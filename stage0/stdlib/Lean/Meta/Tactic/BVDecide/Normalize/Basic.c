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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind(lean_object* v_x_88_){
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
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_88_ = stack[0].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind(v_x_88_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind___boxed(lean_object* v_x_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind(v_x_92_);
lean_dec_ref(v_x_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar(lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_95_ = stack[0].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar(v_x_95_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar___boxed(lean_object* v_x_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar(v_x_99_);
lean_dec_ref(v_x_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___impl(lean_object* v_x_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_tag_nat(v_x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___impl___boxed(lean_object* v_x_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___impl(v_x_104_);
lean_dec_ref(v_x_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object* v_t_106_, lean_object* v_k_107_){
_start:
{
lean_object* v_info_108_; lean_object* v_ctors_109_; lean_object* v___x_110_; 
v_info_108_ = lean_ctor_get(v_t_106_, 0);
lean_inc_ref(v_info_108_);
v_ctors_109_ = lean_ctor_get(v_t_106_, 1);
lean_inc_ref(v_ctors_109_);
lean_dec_ref(v_t_106_);
v___x_110_ = lean_apply_2(v_k_107_, v_info_108_, v_ctors_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object* v_motive_111_, lean_object* v_ctorIdx_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_k_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_113_, v_k_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object* v_motive_117_, lean_object* v_ctorIdx_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_k_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(v_motive_117_, v_ctorIdx_118_, v_t_119_, v_h_120_, v_k_121_);
lean_dec(v_ctorIdx_118_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object* v_t_123_, lean_object* v_simpleEnum_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_123_, v_simpleEnum_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_simpleEnum_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_127_, v_simpleEnum_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object* v_t_131_, lean_object* v_enumWithDefault_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_131_, v_enumWithDefault_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object* v_motive_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_enumWithDefault_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_135_, v_enumWithDefault_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(lean_object* v_x_139_){
_start:
{
lean_object* v_info_140_; 
v_info_140_ = lean_ctor_get(v_x_139_, 0);
lean_inc_ref(v_info_140_);
return v_info_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo___boxed(lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(v_x_141_);
lean_dec_ref(v_x_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___impl(lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_tag_nat(v_x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___impl___boxed(lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___impl(v_x_145_);
lean_dec(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object* v_t_147_, lean_object* v_k_148_){
_start:
{
switch(lean_obj_tag(v_t_147_))
{
case 0:
{
lean_object* v_fvar_149_; lean_object* v___x_150_; 
v_fvar_149_ = lean_ctor_get(v_t_147_, 0);
lean_inc(v_fvar_149_);
lean_dec_ref_known(v_t_147_, 1);
v___x_150_ = lean_apply_1(v_k_148_, v_fvar_149_);
return v___x_150_;
}
case 1:
{
lean_object* v_n_151_; lean_object* v___x_152_; 
v_n_151_ = lean_ctor_get(v_t_147_, 0);
lean_inc(v_n_151_);
lean_dec_ref_known(v_t_147_, 1);
v___x_152_ = lean_apply_1(v_k_148_, v_n_151_);
return v___x_152_;
}
case 2:
{
lean_object* v_e_153_; lean_object* v___x_154_; 
v_e_153_ = lean_ctor_get(v_t_147_, 0);
lean_inc_ref(v_e_153_);
lean_dec_ref_known(v_t_147_, 1);
v___x_154_ = lean_apply_1(v_k_148_, v_e_153_);
return v___x_154_;
}
case 3:
{
lean_object* v_s_155_; lean_object* v___x_156_; 
v_s_155_ = lean_ctor_get(v_t_147_, 0);
lean_inc(v_s_155_);
lean_dec_ref_known(v_t_147_, 1);
v___x_156_ = lean_apply_1(v_k_148_, v_s_155_);
return v___x_156_;
}
default: 
{
lean_dec(v_t_147_);
return v_k_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object* v_motive_157_, lean_object* v_ctorIdx_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_k_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_159_, v_k_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object* v_motive_163_, lean_object* v_ctorIdx_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_k_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(v_motive_163_, v_ctorIdx_164_, v_t_165_, v_h_166_, v_k_167_);
lean_dec(v_ctorIdx_164_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object* v_t_169_, lean_object* v_lctx_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_169_, v_lctx_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_lctx_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_173_, v_lctx_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object* v_t_177_, lean_object* v_enumDomain_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_177_, v_enumDomain_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object* v_motive_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_enumDomain_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_181_, v_enumDomain_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object* v_t_185_, lean_object* v_structureProjection_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_185_, v_structureProjection_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_structureProjection_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_189_, v_structureProjection_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object* v_t_193_, lean_object* v_andFlattened_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_193_, v_andFlattened_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_andFlattened_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_197_, v_andFlattened_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim___redArg(lean_object* v_t_201_, lean_object* v_grind_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_201_, v_grind_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_grind_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_205_, v_grind_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_cegar_elim___redArg(lean_object* v_t_209_, lean_object* v_cegar_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_209_, v_cegar_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_cegar_elim(lean_object* v_motive_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_cegar_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_213_, v_cegar_215_);
return v___x_216_;
}
}
uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object* v_x_221_){
_start:
{
switch(lean_obj_tag(v_x_221_))
{
case 0:
{
lean_object* v_fvar_222_; uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v___x_225_; 
v_fvar_222_ = lean_ctor_get(v_x_221_, 0);
v___x_223_ = 0ULL;
v___x_224_ = l_Lean_instHashableFVarId_hash(v_fvar_222_);
v___x_225_ = lean_uint64_mix_hash(v___x_223_, v___x_224_);
return v___x_225_;
}
case 1:
{
lean_object* v_n_226_; uint64_t v___x_227_; 
v_n_226_ = lean_ctor_get(v_x_221_, 0);
v___x_227_ = 1ULL;
if (lean_obj_tag(v_n_226_) == 0)
{
uint64_t v___x_228_; 
v___x_228_ = 13067028307566252276ULL;
return v___x_228_;
}
else
{
uint64_t v_hash_229_; uint64_t v___x_230_; 
v_hash_229_ = lean_ctor_get_uint64(v_n_226_, sizeof(void*)*2);
v___x_230_ = lean_uint64_mix_hash(v___x_227_, v_hash_229_);
return v___x_230_;
}
}
case 2:
{
lean_object* v_e_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; 
v_e_231_ = lean_ctor_get(v_x_221_, 0);
v___x_232_ = 2ULL;
v___x_233_ = l_Lean_Expr_hash(v_e_231_);
v___x_234_ = lean_uint64_mix_hash(v___x_232_, v___x_233_);
return v___x_234_;
}
case 3:
{
lean_object* v_s_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; 
v_s_235_ = lean_ctor_get(v_x_221_, 0);
v___x_236_ = 3ULL;
v___x_237_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_s_235_);
v___x_238_ = lean_uint64_mix_hash(v___x_236_, v___x_237_);
return v___x_238_;
}
case 4:
{
uint64_t v___x_239_; 
v___x_239_ = 4ULL;
return v___x_239_;
}
default: 
{
uint64_t v___x_240_; 
v___x_240_ = 5ULL;
return v___x_240_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_221_ = stack[0].m_obj;
uint64_t v_res_241_;
v_res_241_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_221_);
stack->m_num = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object* v_x_242_){
_start:
{
uint64_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_242_);
lean_dec(v_x_242_);
v_r_244_ = lean_box_uint64(v_res_243_);
return v_r_244_;
}
}
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
switch(lean_obj_tag(v_x_247_))
{
case 0:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v_fvar_249_; lean_object* v_fvar_250_; uint8_t v___x_251_; 
v_fvar_249_ = lean_ctor_get(v_x_247_, 0);
v_fvar_250_ = lean_ctor_get(v_x_248_, 0);
v___x_251_ = l_Lean_instBEqFVarId_beq(v_fvar_249_, v_fvar_250_);
return v___x_251_;
}
else
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
}
case 1:
{
if (lean_obj_tag(v_x_248_) == 1)
{
lean_object* v_n_253_; lean_object* v_n_254_; uint8_t v___x_255_; 
v_n_253_ = lean_ctor_get(v_x_247_, 0);
v_n_254_ = lean_ctor_get(v_x_248_, 0);
v___x_255_ = lean_name_eq(v_n_253_, v_n_254_);
return v___x_255_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
case 2:
{
if (lean_obj_tag(v_x_248_) == 2)
{
lean_object* v_e_257_; lean_object* v_e_258_; uint8_t v___x_259_; 
v_e_257_ = lean_ctor_get(v_x_247_, 0);
v_e_258_ = lean_ctor_get(v_x_248_, 0);
v___x_259_ = lean_expr_eqv(v_e_257_, v_e_258_);
return v___x_259_;
}
else
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
}
case 3:
{
if (lean_obj_tag(v_x_248_) == 3)
{
lean_object* v_s_261_; lean_object* v_s_262_; 
v_s_261_ = lean_ctor_get(v_x_247_, 0);
v_s_262_ = lean_ctor_get(v_x_248_, 0);
v_x_247_ = v_s_261_;
v_x_248_ = v_s_262_;
goto _start;
}
else
{
uint8_t v___x_264_; 
v___x_264_ = 0;
return v___x_264_;
}
}
case 4:
{
if (lean_obj_tag(v_x_248_) == 4)
{
uint8_t v___x_265_; 
v___x_265_ = 1;
return v___x_265_;
}
else
{
uint8_t v___x_266_; 
v___x_266_ = 0;
return v___x_266_;
}
}
default: 
{
if (lean_obj_tag(v_x_248_) == 5)
{
uint8_t v___x_267_; 
v___x_267_ = 1;
return v___x_267_;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = 0;
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_247_ = stack[0].m_obj;
lean_object* v_x_248_ = stack[1].m_obj;
uint8_t v_res_269_;
v_res_269_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_247_, v_x_248_);
stack->m_num = v_res_269_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_270_, v_x_271_);
lean_dec(v_x_271_);
lean_dec(v_x_270_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object* v_s_276_){
_start:
{
if (lean_obj_tag(v_s_276_) == 3)
{
lean_object* v_s_277_; 
v_s_277_ = lean_ctor_get(v_s_276_, 0);
v_s_276_ = v_s_277_;
goto _start;
}
else
{
lean_inc(v_s_276_);
return v_s_276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object* v_s_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_279_);
lean_dec(v_s_279_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0));
v___x_283_ = l_Lean_stringToMessageData(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4));
v___x_289_ = l_Lean_stringToMessageData(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6));
v___x_292_ = l_Lean_stringToMessageData(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__10));
v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object* v_s_299_){
_start:
{
switch(lean_obj_tag(v_s_299_))
{
case 0:
{
lean_object* v_fvar_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_fvar_300_ = lean_ctor_get(v_s_299_, 0);
lean_inc(v_fvar_300_);
lean_dec_ref_known(v_s_299_, 1);
v___x_301_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1);
v___x_302_ = l_Lean_mkFVar(v_fvar_300_);
v___x_303_ = l_Lean_MessageData_ofExpr(v___x_302_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_301_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
return v___x_304_;
}
case 1:
{
lean_object* v_n_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_n_305_ = lean_ctor_get(v_s_299_, 0);
lean_inc(v_n_305_);
lean_dec_ref_known(v_s_299_, 1);
v___x_306_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3);
v___x_307_ = l_Lean_MessageData_ofName(v_n_305_);
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
return v___x_308_;
}
case 2:
{
lean_object* v_e_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_e_309_ = lean_ctor_get(v_s_299_, 0);
lean_inc_ref(v_e_309_);
lean_dec_ref_known(v_s_299_, 1);
v___x_310_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5);
v___x_311_ = l_Lean_MessageData_ofExpr(v_e_309_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
return v___x_312_;
}
case 3:
{
lean_object* v_s_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_s_313_ = lean_ctor_get(v_s_299_, 0);
lean_inc(v_s_313_);
lean_dec_ref_known(v_s_299_, 1);
v___x_314_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7);
v___x_315_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_313_);
lean_dec(v_s_313_);
v___x_316_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v___x_315_);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_314_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
return v___x_317_;
}
case 4:
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9);
return v___x_318_;
}
default: 
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11);
return v___x_319_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_box(0);
v___x_326_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1));
v___x_327_ = l_Lean_Expr_const___override(v___x_326_, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default));
v___x_329_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2);
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
lean_ctor_set(v___x_331_, 2, v___x_329_);
lean_ctor_set(v___x_331_, 3, v___x_328_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
return v___x_333_;
}
}
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object* v_lhs_334_, lean_object* v_rhs_335_){
_start:
{
lean_object* v_type_336_; lean_object* v_type_337_; uint8_t v___x_338_; 
v_type_336_ = lean_ctor_get(v_lhs_334_, 1);
v_type_337_ = lean_ctor_get(v_rhs_335_, 1);
v___x_338_ = lean_expr_eqv(v_type_336_, v_type_337_);
return v___x_338_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_334_ = stack[0].m_obj;
lean_object* v_rhs_335_ = stack[1].m_obj;
uint8_t v_res_339_;
v_res_339_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_334_, v_rhs_335_);
stack->m_num = v_res_339_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object* v_lhs_340_, lean_object* v_rhs_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_340_, v_rhs_341_);
lean_dec_ref(v_rhs_341_);
lean_dec_ref(v_lhs_340_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object* v_hyp_346_){
_start:
{
lean_object* v_type_347_; uint64_t v___x_348_; 
v_type_347_ = lean_ctor_get(v_hyp_346_, 1);
v___x_348_ = l_Lean_Expr_hash(v_type_347_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_346_ = stack[0].m_obj;
uint64_t v_res_349_;
v_res_349_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_346_);
stack->m_num = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object* v_hyp_350_){
_start:
{
uint64_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_350_);
lean_dec_ref(v_hyp_350_);
v_r_352_ = lean_box_uint64(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object* v_hyp_355_){
_start:
{
lean_object* v_type_356_; lean_object* v___x_357_; 
v_type_356_ = lean_ctor_get(v_hyp_355_, 1);
lean_inc_ref(v_type_356_);
lean_dec_ref(v_hyp_355_);
v___x_357_ = l_Lean_MessageData_ofExpr(v_type_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___impl(lean_object* v_x_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_tag_nat(v_x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___impl___boxed(lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___impl(v_x_362_);
lean_dec(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(lean_object* v_t_364_, lean_object* v_k_365_){
_start:
{
if (lean_obj_tag(v_t_364_) == 0)
{
lean_object* v_restrictedTypes_366_; lean_object* v___x_367_; 
v_restrictedTypes_366_ = lean_ctor_get(v_t_364_, 0);
lean_inc(v_restrictedTypes_366_);
lean_dec_ref_known(v_t_364_, 1);
v___x_367_ = lean_apply_1(v_k_365_, v_restrictedTypes_366_);
return v___x_367_;
}
else
{
return v_k_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(lean_object* v_motive_368_, lean_object* v_ctorIdx_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_k_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_370_, v_k_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___boxed(lean_object* v_motive_374_, lean_object* v_ctorIdx_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_k_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(v_motive_374_, v_ctorIdx_375_, v_t_376_, v_h_377_, v_k_378_);
lean_dec(v_ctorIdx_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim___redArg(lean_object* v_t_380_, lean_object* v_solve_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_380_, v_solve_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim(lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_solve_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_384_, v_solve_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim___redArg(lean_object* v_t_388_, lean_object* v_push_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_388_, v_push_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_push_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_392_, v_push_394_);
return v___x_395_;
}
}
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 1;
return v___x_398_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_396_ = stack[0].m_obj;
uint8_t v_res_399_;
v_res_399_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_x_396_);
stack->m_num = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush___boxed(lean_object* v_x_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_x_400_);
lean_dec(v_x_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(lean_object* v_x_403_){
_start:
{
if (lean_obj_tag(v_x_403_) == 0)
{
lean_object* v_restrictedTypes_404_; 
v_restrictedTypes_404_ = lean_ctor_get(v_x_403_, 0);
lean_inc(v_restrictedTypes_404_);
return v_restrictedTypes_404_;
}
else
{
lean_object* v___x_405_; 
v___x_405_ = lean_box(0);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes___boxed(lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_x_406_);
lean_dec(v_x_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(lean_object* v_mode_408_, lean_object* v_config_409_){
_start:
{
if (lean_obj_tag(v_mode_408_) == 0)
{
return v_config_409_;
}
else
{
lean_object* v_timeout_410_; uint8_t v_trimProofs_411_; uint8_t v_binaryProofs_412_; uint8_t v_acNf_413_; uint8_t v_graphviz_414_; lean_object* v_maxSteps_415_; uint8_t v_shortCircuit_416_; uint8_t v_solverMode_417_; uint8_t v_uf_418_; lean_object* v_cegarRounds_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_timeout_410_ = lean_ctor_get(v_config_409_, 0);
v_trimProofs_411_ = lean_ctor_get_uint8(v_config_409_, sizeof(void*)*3);
v_binaryProofs_412_ = lean_ctor_get_uint8(v_config_409_, sizeof(void*)*3 + 1);
v_acNf_413_ = lean_ctor_get_uint8(v_config_409_, sizeof(void*)*3 + 2);
v_graphviz_414_ = lean_ctor_get_uint8(v_config_409_, sizeof(void*)*3 + 8);
v_maxSteps_415_ = lean_ctor_get(v_config_409_, 1);
v_shortCircuit_416_ = lean_ctor_get_uint8(v_config_409_, sizeof(void*)*3 + 9);
v_solverMode_417_ = lean_ctor_get_uint8(v_config_409_, sizeof(void*)*3 + 10);
v_uf_418_ = lean_ctor_get_uint8(v_config_409_, sizeof(void*)*3 + 11);
v_cegarRounds_419_ = lean_ctor_get(v_config_409_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v_config_409_);
if (v_isSharedCheck_427_ == 0)
{
v___x_421_ = v_config_409_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_cegarRounds_419_);
lean_inc(v_maxSteps_415_);
lean_inc(v_timeout_410_);
lean_dec(v_config_409_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
uint8_t v___x_423_; lean_object* v___x_425_; 
v___x_423_ = 0;
if (v_isShared_422_ == 0)
{
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_timeout_410_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_maxSteps_415_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_cegarRounds_419_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*3, v_trimProofs_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*3 + 1, v_binaryProofs_412_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*3 + 2, v_acNf_413_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*3 + 8, v_graphviz_414_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*3 + 9, v_shortCircuit_416_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*3 + 10, v_solverMode_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*3 + 11, v_uf_418_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*3 + 3, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*3 + 4, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*3 + 5, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*3 + 6, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*3 + 7, v___x_423_);
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig___boxed(lean_object* v_mode_428_, lean_object* v_config_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_428_, v_config_429_);
lean_dec(v_mode_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object* v_mode_431_, lean_object* v_config_432_, lean_object* v_keepCaches_433_){
_start:
{
uint8_t v___y_435_; 
if (lean_obj_tag(v_keepCaches_433_) == 0)
{
uint8_t v_uf_438_; 
v_uf_438_ = lean_ctor_get_uint8(v_config_432_, sizeof(void*)*3 + 11);
if (v_uf_438_ == 0)
{
uint8_t v___x_439_; 
v___x_439_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_431_);
v___y_435_ = v___x_439_;
goto v___jp_434_;
}
else
{
v___y_435_ = v_uf_438_;
goto v___jp_434_;
}
}
else
{
lean_object* v_val_440_; uint8_t v___x_441_; 
v_val_440_ = lean_ctor_get(v_keepCaches_433_, 0);
v___x_441_ = lean_unbox(v_val_440_);
v___y_435_ = v___x_441_;
goto v___jp_434_;
}
v___jp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_431_, v_config_432_);
v___x_437_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v_mode_431_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*2, v___y_435_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new___boxed(lean_object* v_mode_442_, lean_object* v_config_443_, lean_object* v_keepCaches_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_442_, v_config_443_, v_keepCaches_444_);
lean_dec(v_keepCaches_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object* v_ctx_446_){
_start:
{
lean_object* v_config_447_; lean_object* v_restrictedTypes_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_config_447_ = lean_ctor_get(v_ctx_446_, 5);
lean_inc_ref(v_config_447_);
v_restrictedTypes_448_ = lean_ctor_get(v_ctx_446_, 6);
lean_inc(v_restrictedTypes_448_);
lean_dec_ref(v_ctx_446_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_restrictedTypes_448_);
v___x_450_ = lean_box(0);
v___x_451_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_449_, v_config_447_, v___x_450_);
return v___x_451_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl(uint8_t v_x_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_box(v_x_452_);
v___x_454_ = lean_obj_tag_nat(v___x_453_);
lean_dec(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_452_ = stack[0].m_num;
lean_object* v_res_455_;
v_res_455_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl(v_x_452_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl___boxed(lean_object* v_x_456_){
_start:
{
uint8_t v_x_4__boxed_457_; lean_object* v_res_458_; 
v_x_4__boxed_457_ = lean_unbox(v_x_456_);
v_res_458_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl(v_x_4__boxed_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(lean_object* v_k_459_){
_start:
{
lean_inc(v_k_459_);
return v_k_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(v_k_460_);
lean_dec(v_k_460_);
return v_res_461_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(lean_object* v_motive_462_, lean_object* v_ctorIdx_463_, uint8_t v_t_464_, lean_object* v_h_465_, lean_object* v_k_466_){
_start:
{
lean_inc(v_k_466_);
return v_k_466_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_463_ = stack[1].m_obj;
uint8_t v_t_464_ = stack[2].m_num;
lean_object* v_k_466_ = stack[4].m_obj;
lean_object* v_res_467_;
v_res_467_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(lean_box(0), v_ctorIdx_463_, v_t_464_, lean_box(0), v_k_466_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___boxed(lean_object* v_motive_468_, lean_object* v_ctorIdx_469_, lean_object* v_t_470_, lean_object* v_h_471_, lean_object* v_k_472_){
_start:
{
uint8_t v_t_boxed_473_; lean_object* v_res_474_; 
v_t_boxed_473_ = lean_unbox(v_t_470_);
v_res_474_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(v_motive_468_, v_ctorIdx_469_, v_t_boxed_473_, v_h_471_, v_k_472_);
lean_dec(v_k_472_);
lean_dec(v_ctorIdx_469_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_475_){
_start:
{
lean_inc(v_rewrite_475_);
return v_rewrite_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(v_rewrite_476_);
lean_dec(v_rewrite_476_);
return v_res_477_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(lean_object* v_motive_478_, uint8_t v_t_479_, lean_object* v_h_480_, lean_object* v_rewrite_481_){
_start:
{
lean_inc(v_rewrite_481_);
return v_rewrite_481_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_479_ = stack[1].m_num;
lean_object* v_rewrite_481_ = stack[3].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(lean_box(0), v_t_479_, lean_box(0), v_rewrite_481_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___boxed(lean_object* v_motive_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_rewrite_486_){
_start:
{
uint8_t v_t_boxed_487_; lean_object* v_res_488_; 
v_t_boxed_487_ = lean_unbox(v_t_484_);
v_res_488_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(v_motive_483_, v_t_boxed_487_, v_h_485_, v_rewrite_486_);
lean_dec(v_rewrite_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(lean_object* v_ac_489_){
_start:
{
lean_inc(v_ac_489_);
return v_ac_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg___boxed(lean_object* v_ac_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(v_ac_490_);
lean_dec(v_ac_490_);
return v_res_491_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(lean_object* v_motive_492_, uint8_t v_t_493_, lean_object* v_h_494_, lean_object* v_ac_495_){
_start:
{
lean_inc(v_ac_495_);
return v_ac_495_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_493_ = stack[1].m_num;
lean_object* v_ac_495_ = stack[3].m_obj;
lean_object* v_res_496_;
v_res_496_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(lean_box(0), v_t_493_, lean_box(0), v_ac_495_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___boxed(lean_object* v_motive_497_, lean_object* v_t_498_, lean_object* v_h_499_, lean_object* v_ac_500_){
_start:
{
uint8_t v_t_boxed_501_; lean_object* v_res_502_; 
v_t_boxed_501_ = lean_unbox(v_t_498_);
v_res_502_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(v_motive_497_, v_t_boxed_501_, v_h_499_, v_ac_500_);
lean_dec(v_ac_500_);
return v_res_502_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl(uint8_t v_x_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_box(v_x_503_);
v___x_505_ = lean_obj_tag_nat(v___x_504_);
lean_dec(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_503_ = stack[0].m_num;
lean_object* v_res_506_;
v_res_506_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl(v_x_503_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl___boxed(lean_object* v_x_507_){
_start:
{
uint8_t v_x_4__boxed_508_; lean_object* v_res_509_; 
v_x_4__boxed_508_ = lean_unbox(v_x_507_);
v_res_509_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl(v_x_4__boxed_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(lean_object* v_k_510_){
_start:
{
lean_inc(v_k_510_);
return v_k_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(v_k_511_);
lean_dec(v_k_511_);
return v_res_512_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(lean_object* v_motive_513_, lean_object* v_ctorIdx_514_, uint8_t v_t_515_, lean_object* v_h_516_, lean_object* v_k_517_){
_start:
{
lean_inc(v_k_517_);
return v_k_517_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_514_ = stack[1].m_obj;
uint8_t v_t_515_ = stack[2].m_num;
lean_object* v_k_517_ = stack[4].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(lean_box(0), v_ctorIdx_514_, v_t_515_, lean_box(0), v_k_517_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___boxed(lean_object* v_motive_519_, lean_object* v_ctorIdx_520_, lean_object* v_t_521_, lean_object* v_h_522_, lean_object* v_k_523_){
_start:
{
uint8_t v_t_boxed_524_; lean_object* v_res_525_; 
v_t_boxed_524_ = lean_unbox(v_t_521_);
v_res_525_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(v_motive_519_, v_ctorIdx_520_, v_t_boxed_524_, v_h_522_, v_k_523_);
lean_dec(v_k_523_);
lean_dec(v_ctorIdx_520_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_526_){
_start:
{
lean_inc(v_rewrite_526_);
return v_rewrite_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(v_rewrite_527_);
lean_dec(v_rewrite_527_);
return v_res_528_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(lean_object* v_motive_529_, uint8_t v_t_530_, lean_object* v_h_531_, lean_object* v_rewrite_532_){
_start:
{
lean_inc(v_rewrite_532_);
return v_rewrite_532_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_530_ = stack[1].m_num;
lean_object* v_rewrite_532_ = stack[3].m_obj;
lean_object* v_res_533_;
v_res_533_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(lean_box(0), v_t_530_, lean_box(0), v_rewrite_532_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___boxed(lean_object* v_motive_534_, lean_object* v_t_535_, lean_object* v_h_536_, lean_object* v_rewrite_537_){
_start:
{
uint8_t v_t_boxed_538_; lean_object* v_res_539_; 
v_t_boxed_538_ = lean_unbox(v_t_535_);
v_res_539_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(v_motive_534_, v_t_boxed_538_, v_h_536_, v_rewrite_537_);
lean_dec(v_rewrite_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(lean_object* v_reduction_540_){
_start:
{
lean_inc(v_reduction_540_);
return v_reduction_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg___boxed(lean_object* v_reduction_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(v_reduction_541_);
lean_dec(v_reduction_541_);
return v_res_542_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(lean_object* v_motive_543_, uint8_t v_t_544_, lean_object* v_h_545_, lean_object* v_reduction_546_){
_start:
{
lean_inc(v_reduction_546_);
return v_reduction_546_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_544_ = stack[1].m_num;
lean_object* v_reduction_546_ = stack[3].m_obj;
lean_object* v_res_547_;
v_res_547_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(lean_box(0), v_t_544_, lean_box(0), v_reduction_546_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___boxed(lean_object* v_motive_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_reduction_551_){
_start:
{
uint8_t v_t_boxed_552_; lean_object* v_res_553_; 
v_t_boxed_552_ = lean_unbox(v_t_549_);
v_res_553_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(v_motive_548_, v_t_boxed_552_, v_h_550_, v_reduction_551_);
lean_dec(v_reduction_551_);
return v_res_553_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(uint8_t v_x_554_, lean_object* v_x_555_){
_start:
{
if (v_x_554_ == 0)
{
lean_object* v_rewriteSimp_556_; 
v_rewriteSimp_556_ = lean_ctor_get(v_x_555_, 1);
lean_inc_ref(v_rewriteSimp_556_);
return v_rewriteSimp_556_;
}
else
{
lean_object* v_ac_557_; 
v_ac_557_ = lean_ctor_get(v_x_555_, 3);
lean_inc_ref(v_ac_557_);
return v_ac_557_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_554_ = stack[0].m_num;
lean_object* v_x_555_ = stack[1].m_obj;
lean_object* v_res_558_;
v_res_558_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_x_554_, v_x_555_);
stack->m_obj
 = v_res_558_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get___boxed(lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
uint8_t v_x_15__boxed_561_; lean_object* v_res_562_; 
v_x_15__boxed_561_ = lean_unbox(v_x_559_);
v_res_562_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_x_15__boxed_561_, v_x_560_);
lean_dec_ref(v_x_560_);
return v_res_562_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(uint8_t v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
if (v_x_563_ == 0)
{
lean_object* v_reduction_566_; lean_object* v_rewriteDSimp_567_; lean_object* v_ac_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_reduction_566_ = lean_ctor_get(v_x_565_, 0);
v_rewriteDSimp_567_ = lean_ctor_get(v_x_565_, 2);
v_ac_568_ = lean_ctor_get(v_x_565_, 3);
v_isSharedCheck_575_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_x_565_, 1);
lean_dec(v_unused_576_);
v___x_570_ = v_x_565_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_ac_568_);
lean_inc(v_rewriteDSimp_567_);
lean_inc(v_reduction_566_);
lean_dec(v_x_565_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v_x_564_);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_reduction_566_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_x_564_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_rewriteDSimp_567_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v_ac_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_object* v_reduction_577_; lean_object* v_rewriteSimp_578_; lean_object* v_rewriteDSimp_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_reduction_577_ = lean_ctor_get(v_x_565_, 0);
v_rewriteSimp_578_ = lean_ctor_get(v_x_565_, 1);
v_rewriteDSimp_579_ = lean_ctor_get(v_x_565_, 2);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v_x_565_, 3);
lean_dec(v_unused_587_);
v___x_581_ = v_x_565_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_rewriteDSimp_579_);
lean_inc(v_rewriteSimp_578_);
lean_inc(v_reduction_577_);
lean_dec(v_x_565_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 3, v_x_564_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_reduction_577_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_rewriteSimp_578_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_rewriteDSimp_579_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_x_564_);
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
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_563_ = stack[0].m_num;
lean_object* v_x_564_ = stack[1].m_obj;
lean_object* v_x_565_ = stack[2].m_obj;
lean_object* v_res_588_;
v_res_588_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_x_563_, v_x_564_, v_x_565_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set___boxed(lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
uint8_t v_x_28__boxed_592_; lean_object* v_res_593_; 
v_x_28__boxed_592_ = lean_unbox(v_x_589_);
v_res_593_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_x_28__boxed_592_, v_x_590_, v_x_591_);
return v_res_593_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(uint8_t v_x_594_, lean_object* v_x_595_){
_start:
{
if (v_x_594_ == 0)
{
lean_object* v_rewriteDSimp_596_; 
v_rewriteDSimp_596_ = lean_ctor_get(v_x_595_, 2);
lean_inc_ref(v_rewriteDSimp_596_);
return v_rewriteDSimp_596_;
}
else
{
lean_object* v_reduction_597_; 
v_reduction_597_ = lean_ctor_get(v_x_595_, 0);
lean_inc_ref(v_reduction_597_);
return v_reduction_597_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_594_ = stack[0].m_num;
lean_object* v_x_595_ = stack[1].m_obj;
lean_object* v_res_598_;
v_res_598_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_x_594_, v_x_595_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get___boxed(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
uint8_t v_x_15__boxed_601_; lean_object* v_res_602_; 
v_x_15__boxed_601_ = lean_unbox(v_x_599_);
v_res_602_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_x_15__boxed_601_, v_x_600_);
lean_dec_ref(v_x_600_);
return v_res_602_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(uint8_t v_x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
if (v_x_603_ == 0)
{
lean_object* v_reduction_606_; lean_object* v_rewriteSimp_607_; lean_object* v_ac_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_reduction_606_ = lean_ctor_get(v_x_605_, 0);
v_rewriteSimp_607_ = lean_ctor_get(v_x_605_, 1);
v_ac_608_ = lean_ctor_get(v_x_605_, 3);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_x_605_, 2);
lean_dec(v_unused_616_);
v___x_610_ = v_x_605_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_ac_608_);
lean_inc(v_rewriteSimp_607_);
lean_inc(v_reduction_606_);
lean_dec(v_x_605_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 2, v_x_604_);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_reduction_606_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_rewriteSimp_607_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_x_604_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_ac_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
lean_object* v_rewriteSimp_617_; lean_object* v_rewriteDSimp_618_; lean_object* v_ac_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
v_rewriteSimp_617_ = lean_ctor_get(v_x_605_, 1);
v_rewriteDSimp_618_ = lean_ctor_get(v_x_605_, 2);
v_ac_619_ = lean_ctor_get(v_x_605_, 3);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v_x_605_, 0);
lean_dec(v_unused_627_);
v___x_621_ = v_x_605_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_ac_619_);
lean_inc(v_rewriteDSimp_618_);
lean_inc(v_rewriteSimp_617_);
lean_dec(v_x_605_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_x_604_);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_x_604_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_rewriteSimp_617_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_rewriteDSimp_618_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_ac_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_603_ = stack[0].m_num;
lean_object* v_x_604_ = stack[1].m_obj;
lean_object* v_x_605_ = stack[2].m_obj;
lean_object* v_res_628_;
v_res_628_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_x_603_, v_x_604_, v_x_605_);
stack->m_obj
 = v_res_628_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set___boxed(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
uint8_t v_x_28__boxed_632_; lean_object* v_res_633_; 
v_x_28__boxed_632_ = lean_unbox(v_x_629_);
v_res_633_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_x_28__boxed_632_, v_x_630_, v_x_631_);
return v_res_633_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object* v_hyp_639_, lean_object* v_result_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
if (lean_obj_tag(v_result_640_) == 0)
{
lean_object* v___x_647_; 
lean_dec_ref_known(v_result_640_, 0);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v_hyp_639_);
return v___x_647_;
}
else
{
lean_object* v_e_x27_648_; lean_object* v_proof_649_; lean_object* v_name_650_; lean_object* v_type_651_; lean_object* v_value_652_; lean_object* v_source_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_682_; 
v_e_x27_648_ = lean_ctor_get(v_result_640_, 0);
lean_inc_ref(v_e_x27_648_);
v_proof_649_ = lean_ctor_get(v_result_640_, 1);
lean_inc_ref(v_proof_649_);
lean_dec_ref_known(v_result_640_, 2);
v_name_650_ = lean_ctor_get(v_hyp_639_, 0);
v_type_651_ = lean_ctor_get(v_hyp_639_, 1);
v_value_652_ = lean_ctor_get(v_hyp_639_, 2);
v_source_653_ = lean_ctor_get(v_hyp_639_, 3);
v_isSharedCheck_682_ = !lean_is_exclusive(v_hyp_639_);
if (v_isSharedCheck_682_ == 0)
{
v___x_655_ = v_hyp_639_;
v_isShared_656_ = v_isSharedCheck_682_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_source_653_);
lean_inc(v_value_652_);
lean_inc(v_type_651_);
lean_inc(v_name_650_);
lean_dec(v_hyp_639_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_682_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; 
lean_inc_ref(v_type_651_);
v___x_657_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_651_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_673_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_673_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_673_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_673_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_662_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2));
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v_a_658_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_mkConst(v___x_662_, v___x_664_);
lean_inc_ref(v_e_x27_648_);
v___x_666_ = l_Lean_mkApp4(v___x_665_, v_type_651_, v_e_x27_648_, v_proof_649_, v_value_652_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 2, v___x_666_);
lean_ctor_set(v___x_655_, 1, v_e_x27_648_);
v___x_668_ = v___x_655_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_name_650_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_e_x27_648_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_source_653_);
v___x_668_ = v_reuseFailAlloc_672_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_668_);
v___x_670_ = v___x_660_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_del_object(v___x_655_);
lean_dec(v_source_653_);
lean_dec_ref(v_value_652_);
lean_dec_ref(v_type_651_);
lean_dec(v_name_650_);
lean_dec_ref(v_proof_649_);
lean_dec_ref(v_e_x27_648_);
v_a_674_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_657_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_657_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_639_ = stack[0].m_obj;
lean_object* v_result_640_ = stack[1].m_obj;
lean_object* v_a_641_ = stack[2].m_obj;
lean_object* v_a_642_ = stack[3].m_obj;
lean_object* v_a_643_ = stack[4].m_obj;
lean_object* v_a_644_ = stack[5].m_obj;
lean_object* v_a_645_ = stack[6].m_obj;
lean_object* v_res_683_;
v_res_683_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_639_, v_result_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object* v_hyp_684_, lean_object* v_result_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_684_, v_result_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
return v_res_692_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object* v_hyp_693_, lean_object* v_result_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_693_, v_result_694_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
return v___x_702_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_693_ = stack[0].m_obj;
lean_object* v_result_694_ = stack[1].m_obj;
lean_object* v_a_695_ = stack[2].m_obj;
lean_object* v_a_696_ = stack[3].m_obj;
lean_object* v_a_697_ = stack[4].m_obj;
lean_object* v_a_698_ = stack[5].m_obj;
lean_object* v_a_699_ = stack[6].m_obj;
lean_object* v_a_700_ = stack[7].m_obj;
lean_object* v_res_703_;
v_res_703_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_693_, v_result_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
stack->m_obj
 = v_res_703_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object* v_hyp_704_, lean_object* v_result_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_704_, v_result_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_713_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object* v_hyp_714_, lean_object* v_result_715_){
_start:
{
lean_object* v_name_717_; lean_object* v_type_718_; lean_object* v_value_719_; lean_object* v_source_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_729_; 
v_name_717_ = lean_ctor_get(v_hyp_714_, 0);
v_type_718_ = lean_ctor_get(v_hyp_714_, 1);
v_value_719_ = lean_ctor_get(v_hyp_714_, 2);
v_source_720_ = lean_ctor_get(v_hyp_714_, 3);
v_isSharedCheck_729_ = !lean_is_exclusive(v_hyp_714_);
if (v_isSharedCheck_729_ == 0)
{
v___x_722_ = v_hyp_714_;
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_source_720_);
lean_inc(v_value_719_);
lean_inc(v_type_718_);
lean_inc(v_name_717_);
lean_dec(v_hyp_714_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_type_718_, v_result_715_);
lean_dec_ref(v_type_718_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_name_717_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_value_719_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_source_720_);
v___x_726_ = v_reuseFailAlloc_728_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_714_ = stack[0].m_obj;
lean_object* v_result_715_ = stack[1].m_obj;
lean_object* v_res_730_;
v_res_730_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_714_, v_result_715_);
stack->m_obj
 = v_res_730_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object* v_hyp_731_, lean_object* v_result_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_731_, v_result_732_);
lean_dec_ref(v_result_732_);
return v_res_734_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object* v_hyp_735_, lean_object* v_result_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_735_, v_result_736_);
return v___x_744_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_735_ = stack[0].m_obj;
lean_object* v_result_736_ = stack[1].m_obj;
lean_object* v_a_737_ = stack[2].m_obj;
lean_object* v_a_738_ = stack[3].m_obj;
lean_object* v_a_739_ = stack[4].m_obj;
lean_object* v_a_740_ = stack[5].m_obj;
lean_object* v_a_741_ = stack[6].m_obj;
lean_object* v_a_742_ = stack[7].m_obj;
lean_object* v_res_745_;
v_res_745_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_735_, v_result_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
stack->m_obj
 = v_res_745_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object* v_hyp_746_, lean_object* v_result_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_746_, v_result_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec_ref(v_result_747_);
return v_res_755_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_756_){
_start:
{
lean_object* v_config_758_; lean_object* v___x_759_; 
v_config_758_ = lean_ctor_get(v_a_756_, 0);
lean_inc_ref(v_config_758_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v_config_758_);
return v___x_759_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_756_ = stack[0].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_756_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_761_);
lean_dec_ref(v_a_761_);
return v_res_763_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_config_776_; lean_object* v___x_777_; 
v_config_776_ = lean_ctor_get(v_a_764_, 0);
lean_inc_ref(v_config_776_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v_config_776_);
return v___x_777_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_764_ = stack[0].m_obj;
lean_object* v_a_765_ = stack[1].m_obj;
lean_object* v_a_766_ = stack[2].m_obj;
lean_object* v_a_767_ = stack[3].m_obj;
lean_object* v_a_768_ = stack[4].m_obj;
lean_object* v_a_769_ = stack[5].m_obj;
lean_object* v_a_770_ = stack[6].m_obj;
lean_object* v_a_771_ = stack[7].m_obj;
lean_object* v_a_772_ = stack[8].m_obj;
lean_object* v_a_773_ = stack[9].m_obj;
lean_object* v_a_774_ = stack[10].m_obj;
lean_object* v_res_778_;
v_res_778_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
stack->m_obj
 = v_res_778_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_791_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(lean_object* v_a_792_){
_start:
{
lean_object* v_mode_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_mode_794_ = lean_ctor_get(v_a_792_, 1);
v___x_795_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_794_);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_792_ = stack[0].m_obj;
lean_object* v_res_797_;
v_res_797_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(v_a_792_);
stack->m_obj
 = v_res_797_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg___boxed(lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(v_a_798_);
lean_dec_ref(v_a_798_);
return v_res_800_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_mode_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_mode_813_ = lean_ctor_get(v_a_801_, 1);
v___x_814_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_813_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_801_ = stack[0].m_obj;
lean_object* v_a_802_ = stack[1].m_obj;
lean_object* v_a_803_ = stack[2].m_obj;
lean_object* v_a_804_ = stack[3].m_obj;
lean_object* v_a_805_ = stack[4].m_obj;
lean_object* v_a_806_ = stack[5].m_obj;
lean_object* v_a_807_ = stack[6].m_obj;
lean_object* v_a_808_ = stack[7].m_obj;
lean_object* v_a_809_ = stack[8].m_obj;
lean_object* v_a_810_ = stack[9].m_obj;
lean_object* v_a_811_ = stack[10].m_obj;
lean_object* v_res_816_;
v_res_816_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___boxed(lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_829_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(lean_object* v_a_830_){
_start:
{
lean_object* v_mode_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_mode_832_ = lean_ctor_get(v_a_830_, 1);
v___x_833_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_832_);
v___x_834_ = lean_box(v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_830_ = stack[0].m_obj;
lean_object* v_res_836_;
v_res_836_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(v_a_830_);
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg___boxed(lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(v_a_837_);
lean_dec_ref(v_a_837_);
return v_res_839_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_mode_852_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_mode_852_ = lean_ctor_get(v_a_840_, 1);
v___x_853_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_852_);
v___x_854_ = lean_box(v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_840_ = stack[0].m_obj;
lean_object* v_a_841_ = stack[1].m_obj;
lean_object* v_a_842_ = stack[2].m_obj;
lean_object* v_a_843_ = stack[3].m_obj;
lean_object* v_a_844_ = stack[4].m_obj;
lean_object* v_a_845_ = stack[5].m_obj;
lean_object* v_a_846_ = stack[6].m_obj;
lean_object* v_a_847_ = stack[7].m_obj;
lean_object* v_a_848_ = stack[8].m_obj;
lean_object* v_a_849_ = stack[9].m_obj;
lean_object* v_a_850_ = stack[10].m_obj;
lean_object* v_res_856_;
v_res_856_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___boxed(lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
return v_res_869_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; lean_object* v_target_873_; lean_object* v___x_874_; 
v___x_872_ = lean_st_ref_get(v_a_870_);
v_target_873_ = lean_ctor_get(v___x_872_, 2);
lean_inc_ref(v_target_873_);
lean_dec(v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_target_873_);
return v___x_874_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_870_ = stack[0].m_obj;
lean_object* v_res_875_;
v_res_875_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(v_a_870_);
stack->m_obj
 = v_res_875_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg___boxed(lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(v_a_876_);
lean_dec(v_a_876_);
return v_res_878_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_target_892_; lean_object* v___x_893_; 
v___x_891_ = lean_st_ref_get(v_a_880_);
v_target_892_ = lean_ctor_get(v___x_891_, 2);
lean_inc_ref(v_target_892_);
lean_dec(v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v_target_892_);
return v___x_893_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_879_ = stack[0].m_obj;
lean_object* v_a_880_ = stack[1].m_obj;
lean_object* v_a_881_ = stack[2].m_obj;
lean_object* v_a_882_ = stack[3].m_obj;
lean_object* v_a_883_ = stack[4].m_obj;
lean_object* v_a_884_ = stack[5].m_obj;
lean_object* v_a_885_ = stack[6].m_obj;
lean_object* v_a_886_ = stack[7].m_obj;
lean_object* v_a_887_ = stack[8].m_obj;
lean_object* v_a_888_ = stack[9].m_obj;
lean_object* v_a_889_ = stack[10].m_obj;
lean_object* v_res_894_;
v_res_894_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___boxed(lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
return v_res_907_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; lean_object* v_target_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_910_ = lean_st_ref_get(v_a_908_);
v_target_911_ = lean_ctor_get(v___x_910_, 2);
lean_inc_ref(v_target_911_);
lean_dec(v___x_910_);
v___x_912_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_911_);
lean_dec_ref(v_target_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_908_ = stack[0].m_obj;
lean_object* v_res_914_;
v_res_914_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(v_a_908_);
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg___boxed(lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(v_a_915_);
lean_dec(v_a_915_);
return v_res_917_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_target_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_930_ = lean_st_ref_get(v_a_919_);
v_target_931_ = lean_ctor_get(v___x_930_, 2);
lean_inc_ref(v_target_931_);
lean_dec(v___x_930_);
v___x_932_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_931_);
lean_dec_ref(v_target_931_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_918_ = stack[0].m_obj;
lean_object* v_a_919_ = stack[1].m_obj;
lean_object* v_a_920_ = stack[2].m_obj;
lean_object* v_a_921_ = stack[3].m_obj;
lean_object* v_a_922_ = stack[4].m_obj;
lean_object* v_a_923_ = stack[5].m_obj;
lean_object* v_a_924_ = stack[6].m_obj;
lean_object* v_a_925_ = stack[7].m_obj;
lean_object* v_a_926_ = stack[8].m_obj;
lean_object* v_a_927_ = stack[9].m_obj;
lean_object* v_a_928_ = stack[10].m_obj;
lean_object* v_res_934_;
v_res_934_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed(lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_947_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(lean_object* v_target_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; lean_object* v_caches_952_; lean_object* v_typeAnalysis_953_; lean_object* v_hypotheses_954_; uint8_t v_didChange_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_965_; 
v___x_951_ = lean_st_ref_take(v_a_949_);
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
lean_ctor_set(v___x_957_, 2, v_target_948_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_caches_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_typeAnalysis_953_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_target_948_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_hypotheses_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_964_, sizeof(void*)*4, v_didChange_955_);
v___x_961_ = v_reuseFailAlloc_964_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_st_ref_put(v_a_949_, v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_948_ = stack[0].m_obj;
lean_object* v_a_949_ = stack[1].m_obj;
lean_object* v_res_967_;
v_res_967_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(v_target_948_, v_a_949_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg___boxed(lean_object* v_target_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(v_target_968_, v_a_969_);
lean_dec(v_a_969_);
return v_res_971_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(lean_object* v_target_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; lean_object* v_caches_986_; lean_object* v_typeAnalysis_987_; lean_object* v_hypotheses_988_; uint8_t v_didChange_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_999_; 
v___x_985_ = lean_st_ref_take(v_a_974_);
v_caches_986_ = lean_ctor_get(v___x_985_, 0);
v_typeAnalysis_987_ = lean_ctor_get(v___x_985_, 1);
v_hypotheses_988_ = lean_ctor_get(v___x_985_, 3);
v_didChange_989_ = lean_ctor_get_uint8(v___x_985_, sizeof(void*)*4);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_985_, 2);
lean_dec(v_unused_1000_);
v___x_991_ = v___x_985_;
v_isShared_992_ = v_isSharedCheck_999_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_hypotheses_988_);
lean_inc(v_typeAnalysis_987_);
lean_inc(v_caches_986_);
lean_dec(v___x_985_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_999_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_box(0);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 2, v_target_972_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_caches_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_typeAnalysis_987_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_target_972_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_hypotheses_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*4, v_didChange_989_);
v___x_995_ = v_reuseFailAlloc_998_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_st_ref_put(v_a_974_, v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_993_);
return v___x_997_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_972_ = stack[0].m_obj;
lean_object* v_a_973_ = stack[1].m_obj;
lean_object* v_a_974_ = stack[2].m_obj;
lean_object* v_a_975_ = stack[3].m_obj;
lean_object* v_a_976_ = stack[4].m_obj;
lean_object* v_a_977_ = stack[5].m_obj;
lean_object* v_a_978_ = stack[6].m_obj;
lean_object* v_a_979_ = stack[7].m_obj;
lean_object* v_a_980_ = stack[8].m_obj;
lean_object* v_a_981_ = stack[9].m_obj;
lean_object* v_a_982_ = stack[10].m_obj;
lean_object* v_a_983_ = stack[11].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(v_target_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___boxed(lean_object* v_target_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(v_target_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
return v_res_1015_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0(void){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_instMonadControlReaderT___redArg();
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1(void){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_instMonadEIO___redArg();
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2);
v___x_1020_ = l_StateRefT_x27_instMonad___redArg(v___x_1019_);
return v___x_1020_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(lean_object* v_x_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v_target_1038_; 
v___x_1037_ = lean_st_ref_get(v_a_1026_);
v_target_1038_ = lean_ctor_get(v___x_1037_, 2);
lean_inc_ref(v_target_1038_);
lean_dec(v___x_1037_);
if (lean_obj_tag(v_target_1038_) == 1)
{
lean_object* v_goal_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1167_; 
v_goal_1039_ = lean_ctor_get(v_target_1038_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_target_1038_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1041_ = v_target_1038_;
v_isShared_1042_ = v_isSharedCheck_1167_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_goal_1039_);
lean_dec(v_target_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1167_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_toApplicative_1046_; lean_object* v_toFunctor_1047_; lean_object* v_toSeq_1048_; lean_object* v_toSeqLeft_1049_; lean_object* v_toSeqRight_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___f_1064_; lean_object* v___f_1065_; lean_object* v___x_1066_; lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___x_1072_; lean_object* v___f_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___f_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v_toApplicative_1079_; lean_object* v_toFunctor_1080_; lean_object* v_toSeq_1081_; lean_object* v_toSeqLeft_1082_; lean_object* v_toSeqRight_1083_; lean_object* v___f_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_toApplicative_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1165_; 
v___x_1043_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_1044_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_1045_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_1046_ = lean_ctor_get(v___x_1045_, 0);
v_toFunctor_1047_ = lean_ctor_get(v_toApplicative_1046_, 0);
v_toSeq_1048_ = lean_ctor_get(v_toApplicative_1046_, 2);
v_toSeqLeft_1049_ = lean_ctor_get(v_toApplicative_1046_, 3);
v_toSeqRight_1050_ = lean_ctor_get(v_toApplicative_1046_, 4);
v___f_1051_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_1052_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_1047_, 2);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toFunctor_1047_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toFunctor_1047_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___f_1053_);
lean_ctor_set(v___x_1055_, 1, v___f_1054_);
lean_inc(v_toSeqRight_1050_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toSeqRight_1050_);
lean_inc(v_toSeqLeft_1049_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toSeqLeft_1049_);
lean_inc(v_toSeq_1048_);
v___f_1058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1058_, 0, v_toSeq_1048_);
v___x_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1055_);
lean_ctor_set(v___x_1059_, 1, v___f_1051_);
lean_ctor_set(v___x_1059_, 2, v___f_1058_);
lean_ctor_set(v___x_1059_, 3, v___f_1057_);
lean_ctor_set(v___x_1059_, 4, v___f_1056_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___f_1052_);
v___x_1061_ = l_StateRefT_x27_instMonad___redArg(v___x_1060_);
v___x_1062_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1062_, 0, lean_box(0));
lean_closure_set(v___x_1062_, 1, lean_box(0));
lean_closure_set(v___x_1062_, 2, v___x_1061_);
v___x_1063_ = l_instMonadControlTOfPure___redArg(v___x_1062_);
lean_inc_ref(v___x_1063_);
v___f_1064_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1064_, 0, v___x_1044_);
lean_closure_set(v___f_1064_, 1, v___x_1063_);
v___f_1065_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1065_, 0, v___x_1044_);
lean_closure_set(v___f_1065_, 1, v___x_1063_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___f_1064_);
lean_ctor_set(v___x_1066_, 1, v___f_1065_);
lean_inc_ref(v___x_1066_);
v___f_1067_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1067_, 0, v___x_1043_);
lean_closure_set(v___f_1067_, 1, v___x_1066_);
v___f_1068_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1068_, 0, v___x_1043_);
lean_closure_set(v___f_1068_, 1, v___x_1066_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___f_1067_);
lean_ctor_set(v___x_1069_, 1, v___f_1068_);
lean_inc_ref(v___x_1069_);
v___f_1070_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1070_, 0, v___x_1044_);
lean_closure_set(v___f_1070_, 1, v___x_1069_);
v___f_1071_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1071_, 0, v___x_1044_);
lean_closure_set(v___f_1071_, 1, v___x_1069_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___f_1070_);
lean_ctor_set(v___x_1072_, 1, v___f_1071_);
lean_inc_ref(v___x_1072_);
v___f_1073_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1073_, 0, v___x_1043_);
lean_closure_set(v___f_1073_, 1, v___x_1072_);
v___f_1074_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1074_, 0, v___x_1043_);
lean_closure_set(v___f_1074_, 1, v___x_1072_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___f_1073_);
lean_ctor_set(v___x_1075_, 1, v___f_1074_);
lean_inc_ref(v___x_1075_);
v___f_1076_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1076_, 0, v___x_1043_);
lean_closure_set(v___f_1076_, 1, v___x_1075_);
v___f_1077_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1077_, 0, v___x_1043_);
lean_closure_set(v___f_1077_, 1, v___x_1075_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___f_1076_);
lean_ctor_set(v___x_1078_, 1, v___f_1077_);
v_toApplicative_1079_ = lean_ctor_get(v___x_1045_, 0);
v_toFunctor_1080_ = lean_ctor_get(v_toApplicative_1079_, 0);
v_toSeq_1081_ = lean_ctor_get(v_toApplicative_1079_, 2);
v_toSeqLeft_1082_ = lean_ctor_get(v_toApplicative_1079_, 3);
v_toSeqRight_1083_ = lean_ctor_get(v_toApplicative_1079_, 4);
lean_inc_ref_n(v_toFunctor_1080_, 2);
v___f_1084_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1084_, 0, v_toFunctor_1080_);
v___f_1085_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1085_, 0, v_toFunctor_1080_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___f_1084_);
lean_ctor_set(v___x_1086_, 1, v___f_1085_);
lean_inc(v_toSeqRight_1083_);
v___f_1087_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1087_, 0, v_toSeqRight_1083_);
lean_inc(v_toSeqLeft_1082_);
v___f_1088_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1088_, 0, v_toSeqLeft_1082_);
lean_inc(v_toSeq_1081_);
v___f_1089_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1089_, 0, v_toSeq_1081_);
v___x_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1086_);
lean_ctor_set(v___x_1090_, 1, v___f_1051_);
lean_ctor_set(v___x_1090_, 2, v___f_1089_);
lean_ctor_set(v___x_1090_, 3, v___f_1088_);
lean_ctor_set(v___x_1090_, 4, v___f_1087_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___f_1052_);
v___x_1092_ = l_StateRefT_x27_instMonad___redArg(v___x_1091_);
v_toApplicative_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1092_, 1);
lean_dec(v_unused_1166_);
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1165_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_toApplicative_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1165_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_toFunctor_1097_; lean_object* v_toSeq_1098_; lean_object* v_toSeqLeft_1099_; lean_object* v_toSeqRight_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1163_; 
v_toFunctor_1097_ = lean_ctor_get(v_toApplicative_1093_, 0);
v_toSeq_1098_ = lean_ctor_get(v_toApplicative_1093_, 2);
v_toSeqLeft_1099_ = lean_ctor_get(v_toApplicative_1093_, 3);
v_toSeqRight_1100_ = lean_ctor_get(v_toApplicative_1093_, 4);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_toApplicative_1093_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v_toApplicative_1093_, 1);
lean_dec(v_unused_1164_);
v___x_1102_ = v_toApplicative_1093_;
v_isShared_1103_ = v_isSharedCheck_1163_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_toSeqRight_1100_);
lean_inc(v_toSeqLeft_1099_);
lean_inc(v_toSeq_1098_);
lean_inc(v_toFunctor_1097_);
lean_dec(v_toApplicative_1093_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1163_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1113_; 
v___f_1104_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1105_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1097_);
v___f_1106_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1106_, 0, v_toFunctor_1097_);
v___f_1107_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1107_, 0, v_toFunctor_1097_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___f_1106_);
lean_ctor_set(v___x_1108_, 1, v___f_1107_);
v___f_1109_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1109_, 0, v_toSeqRight_1100_);
v___f_1110_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1110_, 0, v_toSeqLeft_1099_);
v___f_1111_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1111_, 0, v_toSeq_1098_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v___f_1109_);
lean_ctor_set(v___x_1102_, 3, v___f_1110_);
lean_ctor_set(v___x_1102_, 2, v___f_1111_);
lean_ctor_set(v___x_1102_, 1, v___f_1104_);
lean_ctor_set(v___x_1102_, 0, v___x_1108_);
v___x_1113_ = v___x_1102_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___f_1104_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v___f_1111_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v___f_1110_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v___f_1109_);
v___x_1113_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v___f_1105_);
lean_ctor_set(v___x_1095_, 0, v___x_1113_);
v___x_1115_ = v___x_1095_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___f_1105_);
v___x_1115_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v_mvarId_1121_; lean_object* v___x_1122_; lean_object* v___x_5100__overap_1123_; lean_object* v___x_1124_; 
v___x_1116_ = l_StateRefT_x27_instMonad___redArg(v___x_1115_);
v___x_1117_ = l_ReaderT_instMonad___redArg(v___x_1116_);
v___x_1118_ = l_StateRefT_x27_instMonad___redArg(v___x_1117_);
v___x_1119_ = l_ReaderT_instMonad___redArg(v___x_1118_);
v___x_1120_ = l_ReaderT_instMonad___redArg(v___x_1119_);
v_mvarId_1121_ = lean_ctor_get(v_goal_1039_, 1);
lean_inc(v_mvarId_1121_);
v___x_1122_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1122_, 0, lean_box(0));
lean_closure_set(v___x_1122_, 1, v_goal_1039_);
lean_closure_set(v___x_1122_, 2, v_x_1025_);
v___x_5100__overap_1123_ = l_Lean_MVarId_withContext___redArg(v___x_1078_, v___x_1120_, v_mvarId_1121_, v___x_1122_);
lean_inc(v_a_1035_);
lean_inc_ref(v_a_1034_);
lean_inc(v_a_1033_);
lean_inc_ref(v_a_1032_);
lean_inc(v_a_1031_);
lean_inc_ref(v_a_1030_);
lean_inc(v_a_1029_);
lean_inc_ref(v_a_1028_);
lean_inc(v_a_1027_);
v___x_1124_ = lean_apply_10(v___x_5100__overap_1123_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, lean_box(0));
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1152_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1152_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1152_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1132_; 
v_fst_1129_ = lean_ctor_get(v_a_1125_, 0);
lean_inc(v_fst_1129_);
v_snd_1130_ = lean_ctor_get(v_a_1125_, 1);
lean_inc(v_snd_1130_);
lean_dec(v_a_1125_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_snd_1130_);
v___x_1132_ = v___x_1041_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_snd_1130_);
v___x_1132_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v_caches_1134_; lean_object* v_typeAnalysis_1135_; lean_object* v_hypotheses_1136_; uint8_t v_didChange_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1149_; 
v___x_1133_ = lean_st_ref_take(v_a_1026_);
v_caches_1134_ = lean_ctor_get(v___x_1133_, 0);
v_typeAnalysis_1135_ = lean_ctor_get(v___x_1133_, 1);
v_hypotheses_1136_ = lean_ctor_get(v___x_1133_, 3);
v_didChange_1137_ = lean_ctor_get_uint8(v___x_1133_, sizeof(void*)*4);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v___x_1133_, 2);
lean_dec(v_unused_1150_);
v___x_1139_ = v___x_1133_;
v_isShared_1140_ = v_isSharedCheck_1149_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_hypotheses_1136_);
lean_inc(v_typeAnalysis_1135_);
lean_inc(v_caches_1134_);
lean_dec(v___x_1133_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1149_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 2, v___x_1132_);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_caches_1134_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_typeAnalysis_1135_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_hypotheses_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1148_, sizeof(void*)*4, v_didChange_1137_);
v___x_1142_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1143_ = lean_st_ref_put(v_a_1026_, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_fst_1129_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1144_);
v___x_1146_ = v___x_1127_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_del_object(v___x_1041_);
v_a_1153_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1124_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1124_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
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
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec_ref(v_target_1038_);
lean_dec_ref(v_x_1025_);
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1025_ = stack[0].m_obj;
lean_object* v_a_1026_ = stack[1].m_obj;
lean_object* v_a_1027_ = stack[2].m_obj;
lean_object* v_a_1028_ = stack[3].m_obj;
lean_object* v_a_1029_ = stack[4].m_obj;
lean_object* v_a_1030_ = stack[5].m_obj;
lean_object* v_a_1031_ = stack[6].m_obj;
lean_object* v_a_1032_ = stack[7].m_obj;
lean_object* v_a_1033_ = stack[8].m_obj;
lean_object* v_a_1034_ = stack[9].m_obj;
lean_object* v_a_1035_ = stack[10].m_obj;
lean_object* v_res_1170_;
v_res_1170_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(v_x_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___boxed(lean_object* v_x_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(v_x_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec(v_a_1172_);
return v_res_1183_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(lean_object* v_00_u03b1_1184_, lean_object* v_x_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v_target_1199_; 
v___x_1198_ = lean_st_ref_get(v_a_1187_);
v_target_1199_ = lean_ctor_get(v___x_1198_, 2);
lean_inc_ref(v_target_1199_);
lean_dec(v___x_1198_);
if (lean_obj_tag(v_target_1199_) == 1)
{
lean_object* v_goal_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1328_; 
v_goal_1200_ = lean_ctor_get(v_target_1199_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_target_1199_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1202_ = v_target_1199_;
v_isShared_1203_ = v_isSharedCheck_1328_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_goal_1200_);
lean_dec(v_target_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1328_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_toApplicative_1207_; lean_object* v_toFunctor_1208_; lean_object* v_toSeq_1209_; lean_object* v_toSeqLeft_1210_; lean_object* v_toSeqRight_1211_; lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v_toApplicative_1240_; lean_object* v_toFunctor_1241_; lean_object* v_toSeq_1242_; lean_object* v_toSeqLeft_1243_; lean_object* v_toSeqRight_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_toApplicative_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1326_; 
v___x_1204_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_1205_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_1206_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_1207_ = lean_ctor_get(v___x_1206_, 0);
v_toFunctor_1208_ = lean_ctor_get(v_toApplicative_1207_, 0);
v_toSeq_1209_ = lean_ctor_get(v_toApplicative_1207_, 2);
v_toSeqLeft_1210_ = lean_ctor_get(v_toApplicative_1207_, 3);
v_toSeqRight_1211_ = lean_ctor_get(v_toApplicative_1207_, 4);
v___f_1212_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_1213_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_1208_, 2);
v___f_1214_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1214_, 0, v_toFunctor_1208_);
v___f_1215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1215_, 0, v_toFunctor_1208_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___f_1214_);
lean_ctor_set(v___x_1216_, 1, v___f_1215_);
lean_inc(v_toSeqRight_1211_);
v___f_1217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1217_, 0, v_toSeqRight_1211_);
lean_inc(v_toSeqLeft_1210_);
v___f_1218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1218_, 0, v_toSeqLeft_1210_);
lean_inc(v_toSeq_1209_);
v___f_1219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1219_, 0, v_toSeq_1209_);
v___x_1220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1216_);
lean_ctor_set(v___x_1220_, 1, v___f_1212_);
lean_ctor_set(v___x_1220_, 2, v___f_1219_);
lean_ctor_set(v___x_1220_, 3, v___f_1218_);
lean_ctor_set(v___x_1220_, 4, v___f_1217_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___f_1213_);
v___x_1222_ = l_StateRefT_x27_instMonad___redArg(v___x_1221_);
v___x_1223_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1223_, 0, lean_box(0));
lean_closure_set(v___x_1223_, 1, lean_box(0));
lean_closure_set(v___x_1223_, 2, v___x_1222_);
v___x_1224_ = l_instMonadControlTOfPure___redArg(v___x_1223_);
lean_inc_ref(v___x_1224_);
v___f_1225_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1225_, 0, v___x_1205_);
lean_closure_set(v___f_1225_, 1, v___x_1224_);
v___f_1226_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1226_, 0, v___x_1205_);
lean_closure_set(v___f_1226_, 1, v___x_1224_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___f_1225_);
lean_ctor_set(v___x_1227_, 1, v___f_1226_);
lean_inc_ref(v___x_1227_);
v___f_1228_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1228_, 0, v___x_1204_);
lean_closure_set(v___f_1228_, 1, v___x_1227_);
v___f_1229_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1229_, 0, v___x_1204_);
lean_closure_set(v___f_1229_, 1, v___x_1227_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___f_1228_);
lean_ctor_set(v___x_1230_, 1, v___f_1229_);
lean_inc_ref(v___x_1230_);
v___f_1231_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1231_, 0, v___x_1205_);
lean_closure_set(v___f_1231_, 1, v___x_1230_);
v___f_1232_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1232_, 0, v___x_1205_);
lean_closure_set(v___f_1232_, 1, v___x_1230_);
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___f_1231_);
lean_ctor_set(v___x_1233_, 1, v___f_1232_);
lean_inc_ref(v___x_1233_);
v___f_1234_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1234_, 0, v___x_1204_);
lean_closure_set(v___f_1234_, 1, v___x_1233_);
v___f_1235_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1235_, 0, v___x_1204_);
lean_closure_set(v___f_1235_, 1, v___x_1233_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___f_1234_);
lean_ctor_set(v___x_1236_, 1, v___f_1235_);
lean_inc_ref(v___x_1236_);
v___f_1237_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1237_, 0, v___x_1204_);
lean_closure_set(v___f_1237_, 1, v___x_1236_);
v___f_1238_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1238_, 0, v___x_1204_);
lean_closure_set(v___f_1238_, 1, v___x_1236_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___f_1237_);
lean_ctor_set(v___x_1239_, 1, v___f_1238_);
v_toApplicative_1240_ = lean_ctor_get(v___x_1206_, 0);
v_toFunctor_1241_ = lean_ctor_get(v_toApplicative_1240_, 0);
v_toSeq_1242_ = lean_ctor_get(v_toApplicative_1240_, 2);
v_toSeqLeft_1243_ = lean_ctor_get(v_toApplicative_1240_, 3);
v_toSeqRight_1244_ = lean_ctor_get(v_toApplicative_1240_, 4);
lean_inc_ref_n(v_toFunctor_1241_, 2);
v___f_1245_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1245_, 0, v_toFunctor_1241_);
v___f_1246_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1246_, 0, v_toFunctor_1241_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___f_1245_);
lean_ctor_set(v___x_1247_, 1, v___f_1246_);
lean_inc(v_toSeqRight_1244_);
v___f_1248_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1248_, 0, v_toSeqRight_1244_);
lean_inc(v_toSeqLeft_1243_);
v___f_1249_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1249_, 0, v_toSeqLeft_1243_);
lean_inc(v_toSeq_1242_);
v___f_1250_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1250_, 0, v_toSeq_1242_);
v___x_1251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1247_);
lean_ctor_set(v___x_1251_, 1, v___f_1212_);
lean_ctor_set(v___x_1251_, 2, v___f_1250_);
lean_ctor_set(v___x_1251_, 3, v___f_1249_);
lean_ctor_set(v___x_1251_, 4, v___f_1248_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___f_1213_);
v___x_1253_ = l_StateRefT_x27_instMonad___redArg(v___x_1252_);
v_toApplicative_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v___x_1253_, 1);
lean_dec(v_unused_1327_);
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1326_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_toApplicative_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1326_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_toFunctor_1258_; lean_object* v_toSeq_1259_; lean_object* v_toSeqLeft_1260_; lean_object* v_toSeqRight_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1324_; 
v_toFunctor_1258_ = lean_ctor_get(v_toApplicative_1254_, 0);
v_toSeq_1259_ = lean_ctor_get(v_toApplicative_1254_, 2);
v_toSeqLeft_1260_ = lean_ctor_get(v_toApplicative_1254_, 3);
v_toSeqRight_1261_ = lean_ctor_get(v_toApplicative_1254_, 4);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_toApplicative_1254_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_toApplicative_1254_, 1);
lean_dec(v_unused_1325_);
v___x_1263_ = v_toApplicative_1254_;
v_isShared_1264_ = v_isSharedCheck_1324_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_toSeqRight_1261_);
lean_inc(v_toSeqLeft_1260_);
lean_inc(v_toSeq_1259_);
lean_inc(v_toFunctor_1258_);
lean_dec(v_toApplicative_1254_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1324_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___x_1274_; 
v___f_1265_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1266_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1258_);
v___f_1267_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1267_, 0, v_toFunctor_1258_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toFunctor_1258_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___f_1267_);
lean_ctor_set(v___x_1269_, 1, v___f_1268_);
v___f_1270_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1270_, 0, v_toSeqRight_1261_);
v___f_1271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1271_, 0, v_toSeqLeft_1260_);
v___f_1272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1272_, 0, v_toSeq_1259_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 4, v___f_1270_);
lean_ctor_set(v___x_1263_, 3, v___f_1271_);
lean_ctor_set(v___x_1263_, 2, v___f_1272_);
lean_ctor_set(v___x_1263_, 1, v___f_1265_);
lean_ctor_set(v___x_1263_, 0, v___x_1269_);
v___x_1274_ = v___x_1263_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___f_1265_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v___f_1272_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v___f_1271_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v___f_1270_);
v___x_1274_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___f_1266_);
lean_ctor_set(v___x_1256_, 0, v___x_1274_);
v___x_1276_ = v___x_1256_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___f_1266_);
v___x_1276_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_mvarId_1282_; lean_object* v___x_1283_; lean_object* v___x_5171__overap_1284_; lean_object* v___x_1285_; 
v___x_1277_ = l_StateRefT_x27_instMonad___redArg(v___x_1276_);
v___x_1278_ = l_ReaderT_instMonad___redArg(v___x_1277_);
v___x_1279_ = l_StateRefT_x27_instMonad___redArg(v___x_1278_);
v___x_1280_ = l_ReaderT_instMonad___redArg(v___x_1279_);
v___x_1281_ = l_ReaderT_instMonad___redArg(v___x_1280_);
v_mvarId_1282_ = lean_ctor_get(v_goal_1200_, 1);
lean_inc(v_mvarId_1282_);
v___x_1283_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1283_, 0, lean_box(0));
lean_closure_set(v___x_1283_, 1, v_goal_1200_);
lean_closure_set(v___x_1283_, 2, v_x_1185_);
v___x_5171__overap_1284_ = l_Lean_MVarId_withContext___redArg(v___x_1239_, v___x_1281_, v_mvarId_1282_, v___x_1283_);
lean_inc(v_a_1196_);
lean_inc_ref(v_a_1195_);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc_ref(v_a_1191_);
lean_inc(v_a_1190_);
lean_inc_ref(v_a_1189_);
lean_inc(v_a_1188_);
v___x_1285_ = lean_apply_10(v___x_5171__overap_1284_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, lean_box(0));
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1313_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1313_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1313_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___x_1293_; 
v_fst_1290_ = lean_ctor_get(v_a_1286_, 0);
lean_inc(v_fst_1290_);
v_snd_1291_ = lean_ctor_get(v_a_1286_, 1);
lean_inc(v_snd_1291_);
lean_dec(v_a_1286_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v_snd_1291_);
v___x_1293_ = v___x_1202_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_snd_1291_);
v___x_1293_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; lean_object* v_caches_1295_; lean_object* v_typeAnalysis_1296_; lean_object* v_hypotheses_1297_; uint8_t v_didChange_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1310_; 
v___x_1294_ = lean_st_ref_take(v_a_1187_);
v_caches_1295_ = lean_ctor_get(v___x_1294_, 0);
v_typeAnalysis_1296_ = lean_ctor_get(v___x_1294_, 1);
v_hypotheses_1297_ = lean_ctor_get(v___x_1294_, 3);
v_didChange_1298_ = lean_ctor_get_uint8(v___x_1294_, sizeof(void*)*4);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v___x_1294_, 2);
lean_dec(v_unused_1311_);
v___x_1300_ = v___x_1294_;
v_isShared_1301_ = v_isSharedCheck_1310_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_hypotheses_1297_);
lean_inc(v_typeAnalysis_1296_);
lean_inc(v_caches_1295_);
lean_dec(v___x_1294_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1310_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 2, v___x_1293_);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_caches_1295_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_typeAnalysis_1296_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_hypotheses_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*4, v_didChange_1298_);
v___x_1303_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1304_ = lean_st_ref_put(v_a_1187_, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_fst_1290_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1305_);
v___x_1307_ = v___x_1288_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1202_);
v_a_1314_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1285_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1285_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
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
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v_target_1199_);
lean_dec_ref(v_x_1185_);
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1185_ = stack[1].m_obj;
lean_object* v_a_1186_ = stack[2].m_obj;
lean_object* v_a_1187_ = stack[3].m_obj;
lean_object* v_a_1188_ = stack[4].m_obj;
lean_object* v_a_1189_ = stack[5].m_obj;
lean_object* v_a_1190_ = stack[6].m_obj;
lean_object* v_a_1191_ = stack[7].m_obj;
lean_object* v_a_1192_ = stack[8].m_obj;
lean_object* v_a_1193_ = stack[9].m_obj;
lean_object* v_a_1194_ = stack[10].m_obj;
lean_object* v_a_1195_ = stack[11].m_obj;
lean_object* v_a_1196_ = stack[12].m_obj;
lean_object* v_res_1331_;
v_res_1331_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(lean_box(0), v_x_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
stack->m_obj
 = v_res_1331_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___boxed(lean_object* v_00_u03b1_1332_, lean_object* v_x_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(v_00_u03b1_1332_, v_x_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
return v_res_1346_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; 
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc(v___y_1348_);
v___x_1358_ = lean_apply_10(v_x_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, lean_box(0));
return v___x_1358_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1347_ = stack[0].m_obj;
lean_object* v___y_1348_ = stack[1].m_obj;
lean_object* v___y_1349_ = stack[2].m_obj;
lean_object* v___y_1350_ = stack[3].m_obj;
lean_object* v___y_1351_ = stack[4].m_obj;
lean_object* v___y_1352_ = stack[5].m_obj;
lean_object* v___y_1353_ = stack[6].m_obj;
lean_object* v___y_1354_ = stack[7].m_obj;
lean_object* v___y_1355_ = stack[8].m_obj;
lean_object* v___y_1356_ = stack[9].m_obj;
lean_object* v_res_1359_;
v_res_1359_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(v_x_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed(lean_object* v_x_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(v_x_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
return v_res_1371_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(lean_object* v_mvarId_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___f_1384_; lean_object* v___x_1385_; 
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1374_);
v___f_1384_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1384_, 0, v_x_1373_);
lean_closure_set(v___f_1384_, 1, v___y_1374_);
lean_closure_set(v___f_1384_, 2, v___y_1375_);
lean_closure_set(v___f_1384_, 3, v___y_1376_);
lean_closure_set(v___f_1384_, 4, v___y_1377_);
lean_closure_set(v___f_1384_, 5, v___y_1378_);
v___x_1385_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1372_, v___f_1384_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
if (lean_obj_tag(v___x_1385_) == 0)
{
return v___x_1385_;
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1372_ = stack[0].m_obj;
lean_object* v_x_1373_ = stack[1].m_obj;
lean_object* v___y_1374_ = stack[2].m_obj;
lean_object* v___y_1375_ = stack[3].m_obj;
lean_object* v___y_1376_ = stack[4].m_obj;
lean_object* v___y_1377_ = stack[5].m_obj;
lean_object* v___y_1378_ = stack[6].m_obj;
lean_object* v___y_1379_ = stack[7].m_obj;
lean_object* v___y_1380_ = stack[8].m_obj;
lean_object* v___y_1381_ = stack[9].m_obj;
lean_object* v___y_1382_ = stack[10].m_obj;
lean_object* v_res_1394_;
v_res_1394_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1372_, v_x_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
stack->m_obj
 = v_res_1394_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___boxed(lean_object* v_mvarId_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1395_, v_x_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
return v_res_1407_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(lean_object* v_00_u03b1_1408_, lean_object* v_mvarId_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1409_, v_x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1409_ = stack[1].m_obj;
lean_object* v_x_1410_ = stack[2].m_obj;
lean_object* v___y_1411_ = stack[3].m_obj;
lean_object* v___y_1412_ = stack[4].m_obj;
lean_object* v___y_1413_ = stack[5].m_obj;
lean_object* v___y_1414_ = stack[6].m_obj;
lean_object* v___y_1415_ = stack[7].m_obj;
lean_object* v___y_1416_ = stack[8].m_obj;
lean_object* v___y_1417_ = stack[9].m_obj;
lean_object* v___y_1418_ = stack[10].m_obj;
lean_object* v___y_1419_ = stack[11].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(lean_box(0), v_mvarId_1409_, v_x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___boxed(lean_object* v_00_u03b1_1423_, lean_object* v_mvarId_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(v_00_u03b1_1423_, v_mvarId_1424_, v_x_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
return v_res_1436_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(lean_object* v_goal_1437_, lean_object* v_falseProof_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_st_mk_ref(v_goal_1437_);
v___x_1450_ = l_Lean_Meta_Grind_closeGoal(v_falseProof_1438_, v___x_1449_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1455_ = lean_st_ref_get(v___x_1449_);
lean_dec(v___x_1449_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_a_1451_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v___x_1449_);
v_a_1461_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1450_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1450_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1437_ = stack[0].m_obj;
lean_object* v_falseProof_1438_ = stack[1].m_obj;
lean_object* v___y_1439_ = stack[2].m_obj;
lean_object* v___y_1440_ = stack[3].m_obj;
lean_object* v___y_1441_ = stack[4].m_obj;
lean_object* v___y_1442_ = stack[5].m_obj;
lean_object* v___y_1443_ = stack[6].m_obj;
lean_object* v___y_1444_ = stack[7].m_obj;
lean_object* v___y_1445_ = stack[8].m_obj;
lean_object* v___y_1446_ = stack[9].m_obj;
lean_object* v___y_1447_ = stack[10].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(v_goal_1437_, v_falseProof_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed(lean_object* v_goal_1470_, lean_object* v_falseProof_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(v_goal_1470_, v_falseProof_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
return v_res_1482_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object* v_falseProof_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v_target_1496_; 
v___x_1495_ = lean_st_ref_get(v_a_1484_);
v_target_1496_ = lean_ctor_get(v___x_1495_, 2);
lean_inc_ref(v_target_1496_);
lean_dec(v___x_1495_);
if (lean_obj_tag(v_target_1496_) == 0)
{
lean_object* v_mvar_1497_; lean_object* v___x_1498_; 
v_mvar_1497_ = lean_ctor_get(v_target_1496_, 0);
lean_inc(v_mvar_1497_);
lean_dec_ref_known(v_target_1496_, 1);
v___x_1498_ = l_Lean_MVarId_assignFalseProof(v_mvar_1497_, v_falseProof_1483_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1498_;
}
else
{
lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1550_; 
v_isSharedCheck_1550_ = !lean_is_exclusive(v_target_1496_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_target_1496_, 0);
lean_dec(v_unused_1551_);
v___x_1500_ = v_target_1496_;
v_isShared_1501_ = v_isSharedCheck_1550_;
goto v_resetjp_1499_;
}
else
{
lean_dec(v_target_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1550_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v_target_1504_; 
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_st_ref_get(v_a_1484_);
v_target_1504_ = lean_ctor_get(v___x_1503_, 2);
lean_inc_ref(v_target_1504_);
lean_dec(v___x_1503_);
if (lean_obj_tag(v_target_1504_) == 1)
{
lean_object* v_goal_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1546_; 
lean_del_object(v___x_1500_);
v_goal_1505_ = lean_ctor_get(v_target_1504_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_target_1504_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1507_ = v_target_1504_;
v_isShared_1508_ = v_isSharedCheck_1546_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_goal_1505_);
lean_dec(v_target_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1546_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_mvarId_1509_; lean_object* v___f_1510_; lean_object* v___x_1511_; 
v_mvarId_1509_ = lean_ctor_get(v_goal_1505_, 1);
lean_inc(v_mvarId_1509_);
v___f_1510_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1510_, 0, v_goal_1505_);
lean_closure_set(v___f_1510_, 1, v_falseProof_1483_);
v___x_1511_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1509_, v___f_1510_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1537_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1537_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1537_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_snd_1516_; lean_object* v___x_1518_; 
v_snd_1516_ = lean_ctor_get(v_a_1512_, 1);
lean_inc(v_snd_1516_);
lean_dec(v_a_1512_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v_snd_1516_);
v___x_1518_ = v___x_1507_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_snd_1516_);
v___x_1518_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v_caches_1520_; lean_object* v_typeAnalysis_1521_; lean_object* v_hypotheses_1522_; uint8_t v_didChange_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1534_; 
v___x_1519_ = lean_st_ref_take(v_a_1484_);
v_caches_1520_ = lean_ctor_get(v___x_1519_, 0);
v_typeAnalysis_1521_ = lean_ctor_get(v___x_1519_, 1);
v_hypotheses_1522_ = lean_ctor_get(v___x_1519_, 3);
v_didChange_1523_ = lean_ctor_get_uint8(v___x_1519_, sizeof(void*)*4);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1519_, 2);
lean_dec(v_unused_1535_);
v___x_1525_ = v___x_1519_;
v_isShared_1526_ = v_isSharedCheck_1534_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_hypotheses_1522_);
lean_inc(v_typeAnalysis_1521_);
lean_inc(v_caches_1520_);
lean_dec(v___x_1519_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1534_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 2, v___x_1518_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_caches_1520_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_typeAnalysis_1521_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_hypotheses_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1533_, sizeof(void*)*4, v_didChange_1523_);
v___x_1528_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1529_ = lean_st_ref_put(v_a_1484_, v___x_1528_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1502_);
v___x_1531_ = v___x_1514_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1502_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_del_object(v___x_1507_);
v_a_1538_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1511_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1511_);
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
}
else
{
lean_object* v___x_1548_; 
lean_dec_ref(v_target_1504_);
lean_dec_ref(v_falseProof_1483_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set_tag(v___x_1500_, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1502_);
v___x_1548_ = v___x_1500_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1502_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_falseProof_1483_ = stack[0].m_obj;
lean_object* v_a_1484_ = stack[1].m_obj;
lean_object* v_a_1485_ = stack[2].m_obj;
lean_object* v_a_1486_ = stack[3].m_obj;
lean_object* v_a_1487_ = stack[4].m_obj;
lean_object* v_a_1488_ = stack[5].m_obj;
lean_object* v_a_1489_ = stack[6].m_obj;
lean_object* v_a_1490_ = stack[7].m_obj;
lean_object* v_a_1491_ = stack[8].m_obj;
lean_object* v_a_1492_ = stack[9].m_obj;
lean_object* v_a_1493_ = stack[10].m_obj;
lean_object* v_res_1552_;
v_res_1552_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
stack->m_obj
 = v_res_1552_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___boxed(lean_object* v_falseProof_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec(v_a_1554_);
return v_res_1565_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(lean_object* v_falseProof_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1566_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_falseProof_1566_ = stack[0].m_obj;
lean_object* v_a_1567_ = stack[1].m_obj;
lean_object* v_a_1568_ = stack[2].m_obj;
lean_object* v_a_1569_ = stack[3].m_obj;
lean_object* v_a_1570_ = stack[4].m_obj;
lean_object* v_a_1571_ = stack[5].m_obj;
lean_object* v_a_1572_ = stack[6].m_obj;
lean_object* v_a_1573_ = stack[7].m_obj;
lean_object* v_a_1574_ = stack[8].m_obj;
lean_object* v_a_1575_ = stack[9].m_obj;
lean_object* v_a_1576_ = stack[10].m_obj;
lean_object* v_a_1577_ = stack[11].m_obj;
lean_object* v_res_1580_;
v_res_1580_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(v_falseProof_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
stack->m_obj
 = v_res_1580_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed(lean_object* v_falseProof_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(v_falseProof_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
return v_res_1594_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1597_; uint8_t v_didChange_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1597_ = lean_st_ref_get(v_a_1595_);
v_didChange_1598_ = lean_ctor_get_uint8(v___x_1597_, sizeof(void*)*4);
lean_dec(v___x_1597_);
v___x_1599_ = lean_box(v_didChange_1598_);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1595_ = stack[0].m_obj;
lean_object* v_res_1601_;
v_res_1601_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_1595_);
stack->m_obj
 = v_res_1601_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_1602_);
lean_dec(v_a_1602_);
return v_res_1604_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1617_; uint8_t v_didChange_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1617_ = lean_st_ref_get(v_a_1606_);
v_didChange_1618_ = lean_ctor_get_uint8(v___x_1617_, sizeof(void*)*4);
lean_dec(v___x_1617_);
v___x_1619_ = lean_box(v_didChange_1618_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1605_ = stack[0].m_obj;
lean_object* v_a_1606_ = stack[1].m_obj;
lean_object* v_a_1607_ = stack[2].m_obj;
lean_object* v_a_1608_ = stack[3].m_obj;
lean_object* v_a_1609_ = stack[4].m_obj;
lean_object* v_a_1610_ = stack[5].m_obj;
lean_object* v_a_1611_ = stack[6].m_obj;
lean_object* v_a_1612_ = stack[7].m_obj;
lean_object* v_a_1613_ = stack[8].m_obj;
lean_object* v_a_1614_ = stack[9].m_obj;
lean_object* v_a_1615_ = stack[10].m_obj;
lean_object* v_res_1621_;
v_res_1621_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
stack->m_obj
 = v_res_1621_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
return v_res_1634_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object* v_a_1635_){
_start:
{
lean_object* v___x_1637_; lean_object* v_caches_1638_; lean_object* v_typeAnalysis_1639_; lean_object* v_target_1640_; lean_object* v_hypotheses_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1652_; 
v___x_1637_ = lean_st_ref_take(v_a_1635_);
v_caches_1638_ = lean_ctor_get(v___x_1637_, 0);
v_typeAnalysis_1639_ = lean_ctor_get(v___x_1637_, 1);
v_target_1640_ = lean_ctor_get(v___x_1637_, 2);
v_hypotheses_1641_ = lean_ctor_get(v___x_1637_, 3);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1643_ = v___x_1637_;
v_isShared_1644_ = v_isSharedCheck_1652_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_hypotheses_1641_);
lean_inc(v_target_1640_);
lean_inc(v_typeAnalysis_1639_);
lean_inc(v_caches_1638_);
lean_dec(v___x_1637_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1652_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; uint8_t v___x_1646_; lean_object* v___x_1648_; 
v___x_1645_ = lean_box(0);
v___x_1646_ = 0;
if (v_isShared_1644_ == 0)
{
v___x_1648_ = v___x_1643_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_caches_1638_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_typeAnalysis_1639_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_target_1640_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_hypotheses_1641_);
v___x_1648_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_ctor_set_uint8(v___x_1648_, sizeof(void*)*4, v___x_1646_);
v___x_1649_ = lean_st_ref_put(v_a_1635_, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1645_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1635_ = stack[0].m_obj;
lean_object* v_res_1653_;
v_res_1653_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_1635_);
stack->m_obj
 = v_res_1653_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_1654_);
lean_dec(v_a_1654_);
return v_res_1656_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v_caches_1670_; lean_object* v_typeAnalysis_1671_; lean_object* v_target_1672_; lean_object* v_hypotheses_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1684_; 
v___x_1669_ = lean_st_ref_take(v_a_1658_);
v_caches_1670_ = lean_ctor_get(v___x_1669_, 0);
v_typeAnalysis_1671_ = lean_ctor_get(v___x_1669_, 1);
v_target_1672_ = lean_ctor_get(v___x_1669_, 2);
v_hypotheses_1673_ = lean_ctor_get(v___x_1669_, 3);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1675_ = v___x_1669_;
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_hypotheses_1673_);
lean_inc(v_target_1672_);
lean_inc(v_typeAnalysis_1671_);
lean_inc(v_caches_1670_);
lean_dec(v___x_1669_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1680_; 
v___x_1677_ = lean_box(0);
v___x_1678_ = 0;
if (v_isShared_1676_ == 0)
{
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_caches_1670_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_typeAnalysis_1671_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_target_1672_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_hypotheses_1673_);
v___x_1680_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*4, v___x_1678_);
v___x_1681_ = lean_st_ref_put(v_a_1658_, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1677_);
return v___x_1682_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1657_ = stack[0].m_obj;
lean_object* v_a_1658_ = stack[1].m_obj;
lean_object* v_a_1659_ = stack[2].m_obj;
lean_object* v_a_1660_ = stack[3].m_obj;
lean_object* v_a_1661_ = stack[4].m_obj;
lean_object* v_a_1662_ = stack[5].m_obj;
lean_object* v_a_1663_ = stack[6].m_obj;
lean_object* v_a_1664_ = stack[7].m_obj;
lean_object* v_a_1665_ = stack[8].m_obj;
lean_object* v_a_1666_ = stack[9].m_obj;
lean_object* v_a_1667_ = stack[10].m_obj;
lean_object* v_res_1685_;
v_res_1685_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
stack->m_obj
 = v_res_1685_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
return v_res_1698_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1701_; lean_object* v_caches_1702_; lean_object* v_typeAnalysis_1703_; lean_object* v_target_1704_; lean_object* v_hypotheses_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1716_; 
v___x_1701_ = lean_st_ref_take(v_a_1699_);
v_caches_1702_ = lean_ctor_get(v___x_1701_, 0);
v_typeAnalysis_1703_ = lean_ctor_get(v___x_1701_, 1);
v_target_1704_ = lean_ctor_get(v___x_1701_, 2);
v_hypotheses_1705_ = lean_ctor_get(v___x_1701_, 3);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1707_ = v___x_1701_;
v_isShared_1708_ = v_isSharedCheck_1716_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_hypotheses_1705_);
lean_inc(v_target_1704_);
lean_inc(v_typeAnalysis_1703_);
lean_inc(v_caches_1702_);
lean_dec(v___x_1701_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1716_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; lean_object* v___x_1712_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = 1;
if (v_isShared_1708_ == 0)
{
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_caches_1702_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_typeAnalysis_1703_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_target_1704_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_hypotheses_1705_);
v___x_1712_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*4, v___x_1710_);
v___x_1713_ = lean_st_ref_put(v_a_1699_, v___x_1712_);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1709_);
return v___x_1714_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1699_ = stack[0].m_obj;
lean_object* v_res_1717_;
v_res_1717_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_1699_);
stack->m_obj
 = v_res_1717_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_1718_);
lean_dec(v_a_1718_);
return v_res_1720_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_caches_1734_; lean_object* v_typeAnalysis_1735_; lean_object* v_target_1736_; lean_object* v_hypotheses_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1748_; 
v___x_1733_ = lean_st_ref_take(v_a_1722_);
v_caches_1734_ = lean_ctor_get(v___x_1733_, 0);
v_typeAnalysis_1735_ = lean_ctor_get(v___x_1733_, 1);
v_target_1736_ = lean_ctor_get(v___x_1733_, 2);
v_hypotheses_1737_ = lean_ctor_get(v___x_1733_, 3);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1739_ = v___x_1733_;
v_isShared_1740_ = v_isSharedCheck_1748_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_hypotheses_1737_);
lean_inc(v_target_1736_);
lean_inc(v_typeAnalysis_1735_);
lean_inc(v_caches_1734_);
lean_dec(v___x_1733_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1748_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1744_; 
v___x_1741_ = lean_box(0);
v___x_1742_ = 1;
if (v_isShared_1740_ == 0)
{
v___x_1744_ = v___x_1739_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_caches_1734_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_typeAnalysis_1735_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_target_1736_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v_hypotheses_1737_);
v___x_1744_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*4, v___x_1742_);
v___x_1745_ = lean_st_ref_put(v_a_1722_, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1741_);
return v___x_1746_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1721_ = stack[0].m_obj;
lean_object* v_a_1722_ = stack[1].m_obj;
lean_object* v_a_1723_ = stack[2].m_obj;
lean_object* v_a_1724_ = stack[3].m_obj;
lean_object* v_a_1725_ = stack[4].m_obj;
lean_object* v_a_1726_ = stack[5].m_obj;
lean_object* v_a_1727_ = stack[6].m_obj;
lean_object* v_a_1728_ = stack[7].m_obj;
lean_object* v_a_1729_ = stack[8].m_obj;
lean_object* v_a_1730_ = stack[9].m_obj;
lean_object* v_a_1731_ = stack[10].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
return v_res_1762_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v_caches_1766_; lean_object* v___x_1767_; 
v___x_1765_ = lean_st_ref_get(v_a_1763_);
v_caches_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc_ref(v_caches_1766_);
lean_dec(v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_caches_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1763_ = stack[0].m_obj;
lean_object* v_res_1768_;
v_res_1768_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(v_a_1763_);
stack->m_obj
 = v_res_1768_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg___boxed(lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(v_a_1769_);
lean_dec(v_a_1769_);
return v_res_1771_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v_caches_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_st_ref_get(v_a_1773_);
v_caches_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc_ref(v_caches_1785_);
lean_dec(v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_caches_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1772_ = stack[0].m_obj;
lean_object* v_a_1773_ = stack[1].m_obj;
lean_object* v_a_1774_ = stack[2].m_obj;
lean_object* v_a_1775_ = stack[3].m_obj;
lean_object* v_a_1776_ = stack[4].m_obj;
lean_object* v_a_1777_ = stack[5].m_obj;
lean_object* v_a_1778_ = stack[6].m_obj;
lean_object* v_a_1779_ = stack[7].m_obj;
lean_object* v_a_1780_ = stack[8].m_obj;
lean_object* v_a_1781_ = stack[9].m_obj;
lean_object* v_a_1782_ = stack[10].m_obj;
lean_object* v_res_1787_;
v_res_1787_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
stack->m_obj
 = v_res_1787_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___boxed(lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1800_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(lean_object* v_caches_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1804_; lean_object* v_typeAnalysis_1805_; lean_object* v_target_1806_; lean_object* v_hypotheses_1807_; uint8_t v_didChange_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1818_; 
v___x_1804_ = lean_st_ref_take(v_a_1802_);
v_typeAnalysis_1805_ = lean_ctor_get(v___x_1804_, 1);
v_target_1806_ = lean_ctor_get(v___x_1804_, 2);
v_hypotheses_1807_ = lean_ctor_get(v___x_1804_, 3);
v_didChange_1808_ = lean_ctor_get_uint8(v___x_1804_, sizeof(void*)*4);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v___x_1804_, 0);
lean_dec(v_unused_1819_);
v___x_1810_ = v___x_1804_;
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_hypotheses_1807_);
lean_inc(v_target_1806_);
lean_inc(v_typeAnalysis_1805_);
lean_dec(v___x_1804_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_box(0);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v_caches_1801_);
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_caches_1801_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_typeAnalysis_1805_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_target_1806_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_hypotheses_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*4, v_didChange_1808_);
v___x_1814_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_st_ref_put(v_a_1802_, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1812_);
return v___x_1816_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_caches_1801_ = stack[0].m_obj;
lean_object* v_a_1802_ = stack[1].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(v_caches_1801_, v_a_1802_);
stack->m_obj
 = v_res_1820_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg___boxed(lean_object* v_caches_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(v_caches_1821_, v_a_1822_);
lean_dec(v_a_1822_);
return v_res_1824_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(lean_object* v_caches_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v_typeAnalysis_1839_; lean_object* v_target_1840_; lean_object* v_hypotheses_1841_; uint8_t v_didChange_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1852_; 
v___x_1838_ = lean_st_ref_take(v_a_1827_);
v_typeAnalysis_1839_ = lean_ctor_get(v___x_1838_, 1);
v_target_1840_ = lean_ctor_get(v___x_1838_, 2);
v_hypotheses_1841_ = lean_ctor_get(v___x_1838_, 3);
v_didChange_1842_ = lean_ctor_get_uint8(v___x_1838_, sizeof(void*)*4);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v___x_1838_, 0);
lean_dec(v_unused_1853_);
v___x_1844_ = v___x_1838_;
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_hypotheses_1841_);
lean_inc(v_target_1840_);
lean_inc(v_typeAnalysis_1839_);
lean_dec(v___x_1838_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_box(0);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v_caches_1825_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_caches_1825_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_typeAnalysis_1839_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_target_1840_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_hypotheses_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1851_, sizeof(void*)*4, v_didChange_1842_);
v___x_1848_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_st_ref_put(v_a_1827_, v___x_1848_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1846_);
return v___x_1850_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches_0interp(lean_interpreter_value* stack)
{
lean_object* v_caches_1825_ = stack[0].m_obj;
lean_object* v_a_1826_ = stack[1].m_obj;
lean_object* v_a_1827_ = stack[2].m_obj;
lean_object* v_a_1828_ = stack[3].m_obj;
lean_object* v_a_1829_ = stack[4].m_obj;
lean_object* v_a_1830_ = stack[5].m_obj;
lean_object* v_a_1831_ = stack[6].m_obj;
lean_object* v_a_1832_ = stack[7].m_obj;
lean_object* v_a_1833_ = stack[8].m_obj;
lean_object* v_a_1834_ = stack[9].m_obj;
lean_object* v_a_1835_ = stack[10].m_obj;
lean_object* v_a_1836_ = stack[11].m_obj;
lean_object* v_res_1854_;
v_res_1854_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(v_caches_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
stack->m_obj
 = v_res_1854_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___boxed(lean_object* v_caches_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(v_caches_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1868_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1869_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_1873_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
lean_ctor_set(v___x_1873_, 2, v___x_1872_);
lean_ctor_set(v___x_1873_, 3, v___x_1872_);
return v___x_1873_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
uint8_t v_keepCaches_1877_; 
v_keepCaches_1877_ = lean_ctor_get_uint8(v_a_1874_, sizeof(void*)*2);
if (v_keepCaches_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v_typeAnalysis_1880_; lean_object* v_target_1881_; lean_object* v_hypotheses_1882_; uint8_t v_didChange_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1893_; 
v___x_1878_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_1879_ = lean_st_ref_take(v_a_1875_);
v_typeAnalysis_1880_ = lean_ctor_get(v___x_1879_, 1);
v_target_1881_ = lean_ctor_get(v___x_1879_, 2);
v_hypotheses_1882_ = lean_ctor_get(v___x_1879_, 3);
v_didChange_1883_ = lean_ctor_get_uint8(v___x_1879_, sizeof(void*)*4);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1879_, 0);
lean_dec(v_unused_1894_);
v___x_1885_ = v___x_1879_;
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_hypotheses_1882_);
lean_inc(v_target_1881_);
lean_inc(v_typeAnalysis_1880_);
lean_dec(v___x_1879_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_box(0);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1878_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_typeAnalysis_1880_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_target_1881_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_hypotheses_1882_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*4, v_didChange_1883_);
v___x_1889_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_st_ref_put(v_a_1875_, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1887_);
return v___x_1891_;
}
}
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1874_ = stack[0].m_obj;
lean_object* v_a_1875_ = stack[1].m_obj;
lean_object* v_res_1897_;
v_res_1897_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1874_, v_a_1875_);
stack->m_obj
 = v_res_1897_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___boxed(lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v_res_1901_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1902_, v_a_1903_);
return v___x_1914_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1902_ = stack[0].m_obj;
lean_object* v_a_1903_ = stack[1].m_obj;
lean_object* v_a_1904_ = stack[2].m_obj;
lean_object* v_a_1905_ = stack[3].m_obj;
lean_object* v_a_1906_ = stack[4].m_obj;
lean_object* v_a_1907_ = stack[5].m_obj;
lean_object* v_a_1908_ = stack[6].m_obj;
lean_object* v_a_1909_ = stack[7].m_obj;
lean_object* v_a_1910_ = stack[8].m_obj;
lean_object* v_a_1911_ = stack[9].m_obj;
lean_object* v_a_1912_ = stack[10].m_obj;
lean_object* v_res_1915_;
v_res_1915_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
stack->m_obj
 = v_res_1915_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___boxed(lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1928_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v_typeAnalysis_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_st_ref_get(v_a_1929_);
v_typeAnalysis_1932_ = lean_ctor_get(v___x_1931_, 1);
lean_inc_ref(v_typeAnalysis_1932_);
lean_dec(v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_typeAnalysis_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1929_ = stack[0].m_obj;
lean_object* v_res_1934_;
v_res_1934_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1929_);
stack->m_obj
 = v_res_1934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1935_);
lean_dec(v_a_1935_);
return v_res_1937_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v_typeAnalysis_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_st_ref_get(v_a_1939_);
v_typeAnalysis_1951_ = lean_ctor_get(v___x_1950_, 1);
lean_inc_ref(v_typeAnalysis_1951_);
lean_dec(v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v_typeAnalysis_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1938_ = stack[0].m_obj;
lean_object* v_a_1939_ = stack[1].m_obj;
lean_object* v_a_1940_ = stack[2].m_obj;
lean_object* v_a_1941_ = stack[3].m_obj;
lean_object* v_a_1942_ = stack[4].m_obj;
lean_object* v_a_1943_ = stack[5].m_obj;
lean_object* v_a_1944_ = stack[6].m_obj;
lean_object* v_a_1945_ = stack[7].m_obj;
lean_object* v_a_1946_ = stack[8].m_obj;
lean_object* v_a_1947_ = stack[9].m_obj;
lean_object* v_a_1948_ = stack[10].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
stack->m_obj
 = v_res_1953_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
return v_res_1966_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v_typeAnalysis_1978_; lean_object* v_interestingStructures_1979_; lean_object* v_uninteresting_1980_; uint8_t v___x_1981_; 
v___x_1975_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1976_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1977_ = lean_st_ref_get(v_a_1973_);
v_typeAnalysis_1978_ = lean_ctor_get(v___x_1977_, 1);
lean_inc_ref(v_typeAnalysis_1978_);
lean_dec(v___x_1977_);
v_interestingStructures_1979_ = lean_ctor_get(v_typeAnalysis_1978_, 0);
lean_inc_ref(v_interestingStructures_1979_);
v_uninteresting_1980_ = lean_ctor_get(v_typeAnalysis_1978_, 3);
lean_inc_ref(v_uninteresting_1980_);
lean_dec_ref(v_typeAnalysis_1978_);
lean_inc(v_n_1972_);
v___x_1981_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1975_, v___x_1976_, v_uninteresting_1980_, v_n_1972_);
lean_dec_ref(v_uninteresting_1980_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1975_, v___x_1976_, v_interestingStructures_1979_, v_n_1972_);
lean_dec_ref(v_interestingStructures_1979_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_box(v___x_1982_);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_dec_ref(v_interestingStructures_1979_);
lean_dec(v_n_1972_);
v___x_1988_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1972_ = stack[0].m_obj;
lean_object* v_a_1973_ = stack[1].m_obj;
lean_object* v_res_1990_;
v_res_1990_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1972_, v_a_1973_);
stack->m_obj
 = v_res_1990_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1991_, v_a_1992_);
lean_dec(v_a_1992_);
return v_res_1994_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v_typeAnalysis_2011_; lean_object* v_interestingStructures_2012_; lean_object* v_uninteresting_2013_; uint8_t v___x_2014_; 
v___x_2008_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2009_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2010_ = lean_st_ref_get(v_a_1997_);
v_typeAnalysis_2011_ = lean_ctor_get(v___x_2010_, 1);
lean_inc_ref(v_typeAnalysis_2011_);
lean_dec(v___x_2010_);
v_interestingStructures_2012_ = lean_ctor_get(v_typeAnalysis_2011_, 0);
lean_inc_ref(v_interestingStructures_2012_);
v_uninteresting_2013_ = lean_ctor_get(v_typeAnalysis_2011_, 3);
lean_inc_ref(v_uninteresting_2013_);
lean_dec_ref(v_typeAnalysis_2011_);
lean_inc(v_n_1995_);
v___x_2014_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_2008_, v___x_2009_, v_uninteresting_2013_, v_n_1995_);
lean_dec_ref(v_uninteresting_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_2008_, v___x_2009_, v_interestingStructures_2012_, v_n_1995_);
lean_dec_ref(v_interestingStructures_2012_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = lean_box(v___x_2015_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v_interestingStructures_2012_);
lean_dec(v_n_1995_);
v___x_2021_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1995_ = stack[0].m_obj;
lean_object* v_a_1996_ = stack[1].m_obj;
lean_object* v_a_1997_ = stack[2].m_obj;
lean_object* v_a_1998_ = stack[3].m_obj;
lean_object* v_a_1999_ = stack[4].m_obj;
lean_object* v_a_2000_ = stack[5].m_obj;
lean_object* v_a_2001_ = stack[6].m_obj;
lean_object* v_a_2002_ = stack[7].m_obj;
lean_object* v_a_2003_ = stack[8].m_obj;
lean_object* v_a_2004_ = stack[9].m_obj;
lean_object* v_a_2005_ = stack[10].m_obj;
lean_object* v_a_2006_ = stack[11].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
stack->m_obj
 = v_res_2023_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
return v_res_2037_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v_caches_2042_; lean_object* v_typeAnalysis_2043_; lean_object* v_target_2044_; lean_object* v_hypotheses_2045_; uint8_t v_didChange_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2057_; 
v___x_2041_ = lean_st_ref_take(v_a_2039_);
v_caches_2042_ = lean_ctor_get(v___x_2041_, 0);
v_typeAnalysis_2043_ = lean_ctor_get(v___x_2041_, 1);
v_target_2044_ = lean_ctor_get(v___x_2041_, 2);
v_hypotheses_2045_ = lean_ctor_get(v___x_2041_, 3);
v_didChange_2046_ = lean_ctor_get_uint8(v___x_2041_, sizeof(void*)*4);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2048_ = v___x_2041_;
v_isShared_2049_ = v_isSharedCheck_2057_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_hypotheses_2045_);
lean_inc(v_target_2044_);
lean_inc(v_typeAnalysis_2043_);
lean_inc(v_caches_2042_);
lean_dec(v___x_2041_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2057_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_apply_1(v_f_2038_, v_typeAnalysis_2043_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 1, v___x_2051_);
v___x_2053_ = v___x_2048_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_caches_2042_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_target_2044_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_hypotheses_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*4, v_didChange_2046_);
v___x_2053_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_st_ref_put(v_a_2039_, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2050_);
return v___x_2055_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2038_ = stack[0].m_obj;
lean_object* v_a_2039_ = stack[1].m_obj;
lean_object* v_res_2058_;
v_res_2058_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_2038_, v_a_2039_);
stack->m_obj
 = v_res_2058_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_2059_, v_a_2060_);
lean_dec(v_a_2060_);
return v_res_2062_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v_caches_2077_; lean_object* v_typeAnalysis_2078_; lean_object* v_target_2079_; lean_object* v_hypotheses_2080_; uint8_t v_didChange_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2092_; 
v___x_2076_ = lean_st_ref_take(v_a_2065_);
v_caches_2077_ = lean_ctor_get(v___x_2076_, 0);
v_typeAnalysis_2078_ = lean_ctor_get(v___x_2076_, 1);
v_target_2079_ = lean_ctor_get(v___x_2076_, 2);
v_hypotheses_2080_ = lean_ctor_get(v___x_2076_, 3);
v_didChange_2081_ = lean_ctor_get_uint8(v___x_2076_, sizeof(void*)*4);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2083_ = v___x_2076_;
v_isShared_2084_ = v_isSharedCheck_2092_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_hypotheses_2080_);
lean_inc(v_target_2079_);
lean_inc(v_typeAnalysis_2078_);
lean_inc(v_caches_2077_);
lean_dec(v___x_2076_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2092_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_apply_1(v_f_2063_, v_typeAnalysis_2078_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2086_);
v___x_2088_ = v___x_2083_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_caches_2077_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_target_2079_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v_hypotheses_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2091_, sizeof(void*)*4, v_didChange_2081_);
v___x_2088_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_st_ref_put(v_a_2065_, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2085_);
return v___x_2090_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2063_ = stack[0].m_obj;
lean_object* v_a_2064_ = stack[1].m_obj;
lean_object* v_a_2065_ = stack[2].m_obj;
lean_object* v_a_2066_ = stack[3].m_obj;
lean_object* v_a_2067_ = stack[4].m_obj;
lean_object* v_a_2068_ = stack[5].m_obj;
lean_object* v_a_2069_ = stack[6].m_obj;
lean_object* v_a_2070_ = stack[7].m_obj;
lean_object* v_a_2071_ = stack[8].m_obj;
lean_object* v_a_2072_ = stack[9].m_obj;
lean_object* v_a_2073_ = stack[10].m_obj;
lean_object* v_a_2074_ = stack[11].m_obj;
lean_object* v_res_2093_;
v_res_2093_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
stack->m_obj
 = v_res_2093_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
return v_res_2107_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_typeAnalysis_2114_; lean_object* v_caches_2115_; lean_object* v_target_2116_; lean_object* v_hypotheses_2117_; uint8_t v_didChange_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2140_; 
v___x_2111_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2112_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2113_ = lean_st_ref_take(v_a_2109_);
v_typeAnalysis_2114_ = lean_ctor_get(v___x_2113_, 1);
v_caches_2115_ = lean_ctor_get(v___x_2113_, 0);
v_target_2116_ = lean_ctor_get(v___x_2113_, 2);
v_hypotheses_2117_ = lean_ctor_get(v___x_2113_, 3);
v_didChange_2118_ = lean_ctor_get_uint8(v___x_2113_, sizeof(void*)*4);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2120_ = v___x_2113_;
v_isShared_2121_ = v_isSharedCheck_2140_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_hypotheses_2117_);
lean_inc(v_target_2116_);
lean_inc(v_typeAnalysis_2114_);
lean_inc(v_caches_2115_);
lean_dec(v___x_2113_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2140_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_interestingStructures_2122_; lean_object* v_interestingEnums_2123_; lean_object* v_interestingMatchers_2124_; lean_object* v_uninteresting_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2139_; 
v_interestingStructures_2122_ = lean_ctor_get(v_typeAnalysis_2114_, 0);
v_interestingEnums_2123_ = lean_ctor_get(v_typeAnalysis_2114_, 1);
v_interestingMatchers_2124_ = lean_ctor_get(v_typeAnalysis_2114_, 2);
v_uninteresting_2125_ = lean_ctor_get(v_typeAnalysis_2114_, 3);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_typeAnalysis_2114_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2127_ = v_typeAnalysis_2114_;
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_uninteresting_2125_);
lean_inc(v_interestingMatchers_2124_);
lean_inc(v_interestingEnums_2123_);
lean_inc(v_interestingStructures_2122_);
lean_dec(v_typeAnalysis_2114_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2111_, v___x_2112_, v_interestingStructures_2122_, v_n_2108_, v___x_2129_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2130_);
v___x_2132_ = v___x_2127_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_interestingEnums_2123_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_interestingMatchers_2124_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_uninteresting_2125_);
v___x_2132_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___x_2132_);
v___x_2134_ = v___x_2120_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_caches_2115_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_target_2116_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v_hypotheses_2117_);
lean_ctor_set_uint8(v_reuseFailAlloc_2137_, sizeof(void*)*4, v_didChange_2118_);
v___x_2134_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_st_ref_put(v_a_2109_, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2129_);
return v___x_2136_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2108_ = stack[0].m_obj;
lean_object* v_a_2109_ = stack[1].m_obj;
lean_object* v_res_2141_;
v_res_2141_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_2108_, v_a_2109_);
stack->m_obj
 = v_res_2141_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_2142_, v_a_2143_);
lean_dec(v_a_2143_);
return v_res_2145_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v_typeAnalysis_2162_; lean_object* v_caches_2163_; lean_object* v_target_2164_; lean_object* v_hypotheses_2165_; uint8_t v_didChange_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2188_; 
v___x_2159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2160_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2161_ = lean_st_ref_take(v_a_2148_);
v_typeAnalysis_2162_ = lean_ctor_get(v___x_2161_, 1);
v_caches_2163_ = lean_ctor_get(v___x_2161_, 0);
v_target_2164_ = lean_ctor_get(v___x_2161_, 2);
v_hypotheses_2165_ = lean_ctor_get(v___x_2161_, 3);
v_didChange_2166_ = lean_ctor_get_uint8(v___x_2161_, sizeof(void*)*4);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2168_ = v___x_2161_;
v_isShared_2169_ = v_isSharedCheck_2188_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_hypotheses_2165_);
lean_inc(v_target_2164_);
lean_inc(v_typeAnalysis_2162_);
lean_inc(v_caches_2163_);
lean_dec(v___x_2161_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2188_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_interestingStructures_2170_; lean_object* v_interestingEnums_2171_; lean_object* v_interestingMatchers_2172_; lean_object* v_uninteresting_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2187_; 
v_interestingStructures_2170_ = lean_ctor_get(v_typeAnalysis_2162_, 0);
v_interestingEnums_2171_ = lean_ctor_get(v_typeAnalysis_2162_, 1);
v_interestingMatchers_2172_ = lean_ctor_get(v_typeAnalysis_2162_, 2);
v_uninteresting_2173_ = lean_ctor_get(v_typeAnalysis_2162_, 3);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_typeAnalysis_2162_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2175_ = v_typeAnalysis_2162_;
v_isShared_2176_ = v_isSharedCheck_2187_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_uninteresting_2173_);
lean_inc(v_interestingMatchers_2172_);
lean_inc(v_interestingEnums_2171_);
lean_inc(v_interestingStructures_2170_);
lean_dec(v_typeAnalysis_2162_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2187_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2177_ = lean_box(0);
v___x_2178_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2159_, v___x_2160_, v_interestingStructures_2170_, v_n_2146_, v___x_2177_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_interestingEnums_2171_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_interestingMatchers_2172_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_uninteresting_2173_);
v___x_2180_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2182_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v___x_2180_);
v___x_2182_ = v___x_2168_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_caches_2163_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_target_2164_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_hypotheses_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2185_, sizeof(void*)*4, v_didChange_2166_);
v___x_2182_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_st_ref_put(v_a_2148_, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2177_);
return v___x_2184_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2146_ = stack[0].m_obj;
lean_object* v_a_2147_ = stack[1].m_obj;
lean_object* v_a_2148_ = stack[2].m_obj;
lean_object* v_a_2149_ = stack[3].m_obj;
lean_object* v_a_2150_ = stack[4].m_obj;
lean_object* v_a_2151_ = stack[5].m_obj;
lean_object* v_a_2152_ = stack[6].m_obj;
lean_object* v_a_2153_ = stack[7].m_obj;
lean_object* v_a_2154_ = stack[8].m_obj;
lean_object* v_a_2155_ = stack[9].m_obj;
lean_object* v_a_2156_ = stack[10].m_obj;
lean_object* v_a_2157_ = stack[11].m_obj;
lean_object* v_res_2189_;
v_res_2189_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
stack->m_obj
 = v_res_2189_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
return v_res_2203_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v_typeAnalysis_2210_; lean_object* v_caches_2211_; lean_object* v_target_2212_; lean_object* v_hypotheses_2213_; uint8_t v_didChange_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2236_; 
v___x_2207_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2208_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2209_ = lean_st_ref_take(v_a_2205_);
v_typeAnalysis_2210_ = lean_ctor_get(v___x_2209_, 1);
v_caches_2211_ = lean_ctor_get(v___x_2209_, 0);
v_target_2212_ = lean_ctor_get(v___x_2209_, 2);
v_hypotheses_2213_ = lean_ctor_get(v___x_2209_, 3);
v_didChange_2214_ = lean_ctor_get_uint8(v___x_2209_, sizeof(void*)*4);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2216_ = v___x_2209_;
v_isShared_2217_ = v_isSharedCheck_2236_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_hypotheses_2213_);
lean_inc(v_target_2212_);
lean_inc(v_typeAnalysis_2210_);
lean_inc(v_caches_2211_);
lean_dec(v___x_2209_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2236_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_interestingStructures_2218_; lean_object* v_interestingEnums_2219_; lean_object* v_interestingMatchers_2220_; lean_object* v_uninteresting_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2235_; 
v_interestingStructures_2218_ = lean_ctor_get(v_typeAnalysis_2210_, 0);
v_interestingEnums_2219_ = lean_ctor_get(v_typeAnalysis_2210_, 1);
v_interestingMatchers_2220_ = lean_ctor_get(v_typeAnalysis_2210_, 2);
v_uninteresting_2221_ = lean_ctor_get(v_typeAnalysis_2210_, 3);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_typeAnalysis_2210_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2223_ = v_typeAnalysis_2210_;
v_isShared_2224_ = v_isSharedCheck_2235_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_uninteresting_2221_);
lean_inc(v_interestingMatchers_2220_);
lean_inc(v_interestingEnums_2219_);
lean_inc(v_interestingStructures_2218_);
lean_dec(v_typeAnalysis_2210_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2235_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2207_, v___x_2208_, v_interestingEnums_2219_, v_n_2204_, v___x_2225_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v___x_2226_);
v___x_2228_ = v___x_2223_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_interestingStructures_2218_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_interestingMatchers_2220_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_uninteresting_2221_);
v___x_2228_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2230_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v___x_2228_);
v___x_2230_ = v___x_2216_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_caches_2211_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_target_2212_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_hypotheses_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*4, v_didChange_2214_);
v___x_2230_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_st_ref_put(v_a_2205_, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2225_);
return v___x_2232_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2204_ = stack[0].m_obj;
lean_object* v_a_2205_ = stack[1].m_obj;
lean_object* v_res_2237_;
v_res_2237_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_2204_, v_a_2205_);
stack->m_obj
 = v_res_2237_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_2238_, v_a_2239_);
lean_dec(v_a_2239_);
return v_res_2241_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_typeAnalysis_2258_; lean_object* v_caches_2259_; lean_object* v_target_2260_; lean_object* v_hypotheses_2261_; uint8_t v_didChange_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2284_; 
v___x_2255_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2256_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2257_ = lean_st_ref_take(v_a_2244_);
v_typeAnalysis_2258_ = lean_ctor_get(v___x_2257_, 1);
v_caches_2259_ = lean_ctor_get(v___x_2257_, 0);
v_target_2260_ = lean_ctor_get(v___x_2257_, 2);
v_hypotheses_2261_ = lean_ctor_get(v___x_2257_, 3);
v_didChange_2262_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*4);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2264_ = v___x_2257_;
v_isShared_2265_ = v_isSharedCheck_2284_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_hypotheses_2261_);
lean_inc(v_target_2260_);
lean_inc(v_typeAnalysis_2258_);
lean_inc(v_caches_2259_);
lean_dec(v___x_2257_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2284_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v_interestingStructures_2266_; lean_object* v_interestingEnums_2267_; lean_object* v_interestingMatchers_2268_; lean_object* v_uninteresting_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2283_; 
v_interestingStructures_2266_ = lean_ctor_get(v_typeAnalysis_2258_, 0);
v_interestingEnums_2267_ = lean_ctor_get(v_typeAnalysis_2258_, 1);
v_interestingMatchers_2268_ = lean_ctor_get(v_typeAnalysis_2258_, 2);
v_uninteresting_2269_ = lean_ctor_get(v_typeAnalysis_2258_, 3);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_typeAnalysis_2258_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2271_ = v_typeAnalysis_2258_;
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_uninteresting_2269_);
lean_inc(v_interestingMatchers_2268_);
lean_inc(v_interestingEnums_2267_);
lean_inc(v_interestingStructures_2266_);
lean_dec(v_typeAnalysis_2258_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2255_, v___x_2256_, v_interestingEnums_2267_, v_n_2242_, v___x_2273_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 1, v___x_2274_);
v___x_2276_ = v___x_2271_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_interestingStructures_2266_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_interestingMatchers_2268_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_uninteresting_2269_);
v___x_2276_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v___x_2276_);
v___x_2278_ = v___x_2264_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_caches_2259_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_target_2260_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_hypotheses_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*4, v_didChange_2262_);
v___x_2278_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_st_ref_put(v_a_2244_, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2273_);
return v___x_2280_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2242_ = stack[0].m_obj;
lean_object* v_a_2243_ = stack[1].m_obj;
lean_object* v_a_2244_ = stack[2].m_obj;
lean_object* v_a_2245_ = stack[3].m_obj;
lean_object* v_a_2246_ = stack[4].m_obj;
lean_object* v_a_2247_ = stack[5].m_obj;
lean_object* v_a_2248_ = stack[6].m_obj;
lean_object* v_a_2249_ = stack[7].m_obj;
lean_object* v_a_2250_ = stack[8].m_obj;
lean_object* v_a_2251_ = stack[9].m_obj;
lean_object* v_a_2252_ = stack[10].m_obj;
lean_object* v_a_2253_ = stack[11].m_obj;
lean_object* v_res_2285_;
v_res_2285_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
stack->m_obj
 = v_res_2285_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
return v_res_2299_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_2300_, lean_object* v_k_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v_typeAnalysis_2307_; lean_object* v_caches_2308_; lean_object* v_target_2309_; lean_object* v_hypotheses_2310_; uint8_t v_didChange_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2333_; 
v___x_2304_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2305_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2306_ = lean_st_ref_take(v_a_2302_);
v_typeAnalysis_2307_ = lean_ctor_get(v___x_2306_, 1);
v_caches_2308_ = lean_ctor_get(v___x_2306_, 0);
v_target_2309_ = lean_ctor_get(v___x_2306_, 2);
v_hypotheses_2310_ = lean_ctor_get(v___x_2306_, 3);
v_didChange_2311_ = lean_ctor_get_uint8(v___x_2306_, sizeof(void*)*4);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2313_ = v___x_2306_;
v_isShared_2314_ = v_isSharedCheck_2333_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_hypotheses_2310_);
lean_inc(v_target_2309_);
lean_inc(v_typeAnalysis_2307_);
lean_inc(v_caches_2308_);
lean_dec(v___x_2306_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2333_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v_interestingStructures_2315_; lean_object* v_interestingEnums_2316_; lean_object* v_interestingMatchers_2317_; lean_object* v_uninteresting_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2332_; 
v_interestingStructures_2315_ = lean_ctor_get(v_typeAnalysis_2307_, 0);
v_interestingEnums_2316_ = lean_ctor_get(v_typeAnalysis_2307_, 1);
v_interestingMatchers_2317_ = lean_ctor_get(v_typeAnalysis_2307_, 2);
v_uninteresting_2318_ = lean_ctor_get(v_typeAnalysis_2307_, 3);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_typeAnalysis_2307_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2320_ = v_typeAnalysis_2307_;
v_isShared_2321_ = v_isSharedCheck_2332_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_uninteresting_2318_);
lean_inc(v_interestingMatchers_2317_);
lean_inc(v_interestingEnums_2316_);
lean_inc(v_interestingStructures_2315_);
lean_dec(v_typeAnalysis_2307_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2332_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2322_ = lean_box(0);
v___x_2323_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2304_, v___x_2305_, v_interestingMatchers_2317_, v_n_2300_, v_k_2301_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 2, v___x_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_interestingStructures_2315_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_interestingEnums_2316_);
lean_ctor_set(v_reuseFailAlloc_2331_, 2, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_uninteresting_2318_);
v___x_2325_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_2325_);
v___x_2327_ = v___x_2313_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_caches_2308_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_target_2309_);
lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_hypotheses_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2330_, sizeof(void*)*4, v_didChange_2311_);
v___x_2327_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_st_ref_put(v_a_2302_, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2322_);
return v___x_2329_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2300_ = stack[0].m_obj;
lean_object* v_k_2301_ = stack[1].m_obj;
lean_object* v_a_2302_ = stack[2].m_obj;
lean_object* v_res_2334_;
v_res_2334_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_2300_, v_k_2301_, v_a_2302_);
stack->m_obj
 = v_res_2334_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_2335_, lean_object* v_k_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_2335_, v_k_2336_, v_a_2337_);
lean_dec(v_a_2337_);
return v_res_2339_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_2340_, lean_object* v_k_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v_typeAnalysis_2357_; lean_object* v_caches_2358_; lean_object* v_target_2359_; lean_object* v_hypotheses_2360_; uint8_t v_didChange_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2383_; 
v___x_2354_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2355_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2356_ = lean_st_ref_take(v_a_2343_);
v_typeAnalysis_2357_ = lean_ctor_get(v___x_2356_, 1);
v_caches_2358_ = lean_ctor_get(v___x_2356_, 0);
v_target_2359_ = lean_ctor_get(v___x_2356_, 2);
v_hypotheses_2360_ = lean_ctor_get(v___x_2356_, 3);
v_didChange_2361_ = lean_ctor_get_uint8(v___x_2356_, sizeof(void*)*4);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2363_ = v___x_2356_;
v_isShared_2364_ = v_isSharedCheck_2383_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_hypotheses_2360_);
lean_inc(v_target_2359_);
lean_inc(v_typeAnalysis_2357_);
lean_inc(v_caches_2358_);
lean_dec(v___x_2356_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2383_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v_interestingStructures_2365_; lean_object* v_interestingEnums_2366_; lean_object* v_interestingMatchers_2367_; lean_object* v_uninteresting_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2382_; 
v_interestingStructures_2365_ = lean_ctor_get(v_typeAnalysis_2357_, 0);
v_interestingEnums_2366_ = lean_ctor_get(v_typeAnalysis_2357_, 1);
v_interestingMatchers_2367_ = lean_ctor_get(v_typeAnalysis_2357_, 2);
v_uninteresting_2368_ = lean_ctor_get(v_typeAnalysis_2357_, 3);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_typeAnalysis_2357_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2370_ = v_typeAnalysis_2357_;
v_isShared_2371_ = v_isSharedCheck_2382_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_uninteresting_2368_);
lean_inc(v_interestingMatchers_2367_);
lean_inc(v_interestingEnums_2366_);
lean_inc(v_interestingStructures_2365_);
lean_dec(v_typeAnalysis_2357_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2382_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2372_ = lean_box(0);
v___x_2373_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2354_, v___x_2355_, v_interestingMatchers_2367_, v_n_2340_, v_k_2341_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 2, v___x_2373_);
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_interestingStructures_2365_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_interestingEnums_2366_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_uninteresting_2368_);
v___x_2375_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2377_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v___x_2375_);
v___x_2377_ = v___x_2363_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_caches_2358_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_target_2359_);
lean_ctor_set(v_reuseFailAlloc_2380_, 3, v_hypotheses_2360_);
lean_ctor_set_uint8(v_reuseFailAlloc_2380_, sizeof(void*)*4, v_didChange_2361_);
v___x_2377_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_st_ref_put(v_a_2343_, v___x_2377_);
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2372_);
return v___x_2379_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2340_ = stack[0].m_obj;
lean_object* v_k_2341_ = stack[1].m_obj;
lean_object* v_a_2342_ = stack[2].m_obj;
lean_object* v_a_2343_ = stack[3].m_obj;
lean_object* v_a_2344_ = stack[4].m_obj;
lean_object* v_a_2345_ = stack[5].m_obj;
lean_object* v_a_2346_ = stack[6].m_obj;
lean_object* v_a_2347_ = stack[7].m_obj;
lean_object* v_a_2348_ = stack[8].m_obj;
lean_object* v_a_2349_ = stack[9].m_obj;
lean_object* v_a_2350_ = stack[10].m_obj;
lean_object* v_a_2351_ = stack[11].m_obj;
lean_object* v_a_2352_ = stack[12].m_obj;
lean_object* v_res_2384_;
v_res_2384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_2340_, v_k_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
stack->m_obj
 = v_res_2384_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_2385_, lean_object* v_k_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_2385_, v_k_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2399_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v_typeAnalysis_2406_; lean_object* v_caches_2407_; lean_object* v_target_2408_; lean_object* v_hypotheses_2409_; uint8_t v_didChange_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2432_; 
v___x_2403_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2404_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2405_ = lean_st_ref_take(v_a_2401_);
v_typeAnalysis_2406_ = lean_ctor_get(v___x_2405_, 1);
v_caches_2407_ = lean_ctor_get(v___x_2405_, 0);
v_target_2408_ = lean_ctor_get(v___x_2405_, 2);
v_hypotheses_2409_ = lean_ctor_get(v___x_2405_, 3);
v_didChange_2410_ = lean_ctor_get_uint8(v___x_2405_, sizeof(void*)*4);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2412_ = v___x_2405_;
v_isShared_2413_ = v_isSharedCheck_2432_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_hypotheses_2409_);
lean_inc(v_target_2408_);
lean_inc(v_typeAnalysis_2406_);
lean_inc(v_caches_2407_);
lean_dec(v___x_2405_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2432_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_interestingStructures_2414_; lean_object* v_interestingEnums_2415_; lean_object* v_interestingMatchers_2416_; lean_object* v_uninteresting_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2431_; 
v_interestingStructures_2414_ = lean_ctor_get(v_typeAnalysis_2406_, 0);
v_interestingEnums_2415_ = lean_ctor_get(v_typeAnalysis_2406_, 1);
v_interestingMatchers_2416_ = lean_ctor_get(v_typeAnalysis_2406_, 2);
v_uninteresting_2417_ = lean_ctor_get(v_typeAnalysis_2406_, 3);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_typeAnalysis_2406_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2419_ = v_typeAnalysis_2406_;
v_isShared_2420_ = v_isSharedCheck_2431_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_uninteresting_2417_);
lean_inc(v_interestingMatchers_2416_);
lean_inc(v_interestingEnums_2415_);
lean_inc(v_interestingStructures_2414_);
lean_dec(v_typeAnalysis_2406_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2431_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2421_ = lean_box(0);
v___x_2422_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2403_, v___x_2404_, v_uninteresting_2417_, v_n_2400_, v___x_2421_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 3, v___x_2422_);
v___x_2424_ = v___x_2419_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_interestingStructures_2414_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_interestingEnums_2415_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_interestingMatchers_2416_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2424_);
v___x_2426_ = v___x_2412_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_caches_2407_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2429_, 2, v_target_2408_);
lean_ctor_set(v_reuseFailAlloc_2429_, 3, v_hypotheses_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, sizeof(void*)*4, v_didChange_2410_);
v___x_2426_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_st_ref_put(v_a_2401_, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2421_);
return v___x_2428_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2400_ = stack[0].m_obj;
lean_object* v_a_2401_ = stack[1].m_obj;
lean_object* v_res_2433_;
v_res_2433_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_2400_, v_a_2401_);
stack->m_obj
 = v_res_2433_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_2434_, v_a_2435_);
lean_dec(v_a_2435_);
return v_res_2437_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v_typeAnalysis_2454_; lean_object* v_caches_2455_; lean_object* v_target_2456_; lean_object* v_hypotheses_2457_; uint8_t v_didChange_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2480_; 
v___x_2451_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2452_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2453_ = lean_st_ref_take(v_a_2440_);
v_typeAnalysis_2454_ = lean_ctor_get(v___x_2453_, 1);
v_caches_2455_ = lean_ctor_get(v___x_2453_, 0);
v_target_2456_ = lean_ctor_get(v___x_2453_, 2);
v_hypotheses_2457_ = lean_ctor_get(v___x_2453_, 3);
v_didChange_2458_ = lean_ctor_get_uint8(v___x_2453_, sizeof(void*)*4);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2460_ = v___x_2453_;
v_isShared_2461_ = v_isSharedCheck_2480_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_hypotheses_2457_);
lean_inc(v_target_2456_);
lean_inc(v_typeAnalysis_2454_);
lean_inc(v_caches_2455_);
lean_dec(v___x_2453_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2480_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_interestingStructures_2462_; lean_object* v_interestingEnums_2463_; lean_object* v_interestingMatchers_2464_; lean_object* v_uninteresting_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2479_; 
v_interestingStructures_2462_ = lean_ctor_get(v_typeAnalysis_2454_, 0);
v_interestingEnums_2463_ = lean_ctor_get(v_typeAnalysis_2454_, 1);
v_interestingMatchers_2464_ = lean_ctor_get(v_typeAnalysis_2454_, 2);
v_uninteresting_2465_ = lean_ctor_get(v_typeAnalysis_2454_, 3);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_typeAnalysis_2454_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2467_ = v_typeAnalysis_2454_;
v_isShared_2468_ = v_isSharedCheck_2479_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_uninteresting_2465_);
lean_inc(v_interestingMatchers_2464_);
lean_inc(v_interestingEnums_2463_);
lean_inc(v_interestingStructures_2462_);
lean_dec(v_typeAnalysis_2454_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2479_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2469_ = lean_box(0);
v___x_2470_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2451_, v___x_2452_, v_uninteresting_2465_, v_n_2438_, v___x_2469_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 3, v___x_2470_);
v___x_2472_ = v___x_2467_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_interestingStructures_2462_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_interestingEnums_2463_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_interestingMatchers_2464_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v___x_2472_);
v___x_2474_ = v___x_2460_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_caches_2455_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_target_2456_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_hypotheses_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*4, v_didChange_2458_);
v___x_2474_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_st_ref_put(v_a_2440_, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2469_);
return v___x_2476_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2438_ = stack[0].m_obj;
lean_object* v_a_2439_ = stack[1].m_obj;
lean_object* v_a_2440_ = stack[2].m_obj;
lean_object* v_a_2441_ = stack[3].m_obj;
lean_object* v_a_2442_ = stack[4].m_obj;
lean_object* v_a_2443_ = stack[5].m_obj;
lean_object* v_a_2444_ = stack[6].m_obj;
lean_object* v_a_2445_ = stack[7].m_obj;
lean_object* v_a_2446_ = stack[8].m_obj;
lean_object* v_a_2447_ = stack[9].m_obj;
lean_object* v_a_2448_ = stack[10].m_obj;
lean_object* v_a_2449_ = stack[11].m_obj;
lean_object* v_res_2481_;
v_res_2481_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
stack->m_obj
 = v_res_2481_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
return v_res_2495_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_unsigned_to_nat(16u);
v___x_2498_ = lean_mk_array(v___x_2497_, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_2500_ = lean_unsigned_to_nat(0u);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2499_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_2503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
lean_ctor_set(v___x_2503_, 2, v___x_2502_);
lean_ctor_set(v___x_2503_, 3, v___x_2502_);
return v___x_2503_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_ctx_2506_, lean_object* v_target_2507_, lean_object* v_x_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2519_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2520_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2522_ = 0;
v___x_2523_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2523_, 0, v___x_2519_);
lean_ctor_set(v___x_2523_, 1, v___x_2520_);
lean_ctor_set(v___x_2523_, 2, v_target_2507_);
lean_ctor_set(v___x_2523_, 3, v___x_2521_);
lean_ctor_set_uint8(v___x_2523_, sizeof(void*)*4, v___x_2522_);
v___x_2524_ = lean_st_mk_ref(v___x_2523_);
lean_inc(v_a_2517_);
lean_inc_ref(v_a_2516_);
lean_inc(v_a_2515_);
lean_inc_ref(v_a_2514_);
lean_inc(v_a_2513_);
lean_inc_ref(v_a_2512_);
lean_inc(v_a_2511_);
lean_inc_ref(v_a_2510_);
lean_inc(v_a_2509_);
lean_inc(v___x_2524_);
v___x_2525_ = lean_apply_12(v_x_2508_, v_ctx_2506_, v___x_2524_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, lean_box(0));
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2535_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2535_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2535_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2530_ = lean_st_ref_get(v___x_2524_);
lean_dec(v___x_2524_);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v_a_2526_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2531_);
v___x_2533_ = v___x_2528_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v___x_2524_);
v_a_2536_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2525_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2525_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2506_ = stack[0].m_obj;
lean_object* v_target_2507_ = stack[1].m_obj;
lean_object* v_x_2508_ = stack[2].m_obj;
lean_object* v_a_2509_ = stack[3].m_obj;
lean_object* v_a_2510_ = stack[4].m_obj;
lean_object* v_a_2511_ = stack[5].m_obj;
lean_object* v_a_2512_ = stack[6].m_obj;
lean_object* v_a_2513_ = stack[7].m_obj;
lean_object* v_a_2514_ = stack[8].m_obj;
lean_object* v_a_2515_ = stack[9].m_obj;
lean_object* v_a_2516_ = stack[10].m_obj;
lean_object* v_a_2517_ = stack[11].m_obj;
lean_object* v_res_2544_;
v_res_2544_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_ctx_2506_, v_target_2507_, v_x_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
stack->m_obj
 = v_res_2544_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_ctx_2545_, lean_object* v_target_2546_, lean_object* v_x_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_ctx_2545_, v_target_2546_, v_x_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
return v_res_2558_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_2559_, lean_object* v_ctx_2560_, lean_object* v_target_2561_, lean_object* v_x_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2573_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2574_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2575_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2576_ = 0;
v___x_2577_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2573_);
lean_ctor_set(v___x_2577_, 1, v___x_2574_);
lean_ctor_set(v___x_2577_, 2, v_target_2561_);
lean_ctor_set(v___x_2577_, 3, v___x_2575_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*4, v___x_2576_);
v___x_2578_ = lean_st_mk_ref(v___x_2577_);
lean_inc(v_a_2571_);
lean_inc_ref(v_a_2570_);
lean_inc(v_a_2569_);
lean_inc_ref(v_a_2568_);
lean_inc(v_a_2567_);
lean_inc_ref(v_a_2566_);
lean_inc(v_a_2565_);
lean_inc_ref(v_a_2564_);
lean_inc(v_a_2563_);
lean_inc(v___x_2578_);
v___x_2579_ = lean_apply_12(v_x_2562_, v_ctx_2560_, v___x_2578_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, lean_box(0));
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2589_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2589_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2589_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2584_ = lean_st_ref_get(v___x_2578_);
lean_dec(v___x_2578_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v_a_2580_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2585_);
v___x_2587_ = v___x_2582_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v___x_2578_);
v_a_2590_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2579_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2579_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2560_ = stack[1].m_obj;
lean_object* v_target_2561_ = stack[2].m_obj;
lean_object* v_x_2562_ = stack[3].m_obj;
lean_object* v_a_2563_ = stack[4].m_obj;
lean_object* v_a_2564_ = stack[5].m_obj;
lean_object* v_a_2565_ = stack[6].m_obj;
lean_object* v_a_2566_ = stack[7].m_obj;
lean_object* v_a_2567_ = stack[8].m_obj;
lean_object* v_a_2568_ = stack[9].m_obj;
lean_object* v_a_2569_ = stack[10].m_obj;
lean_object* v_a_2570_ = stack[11].m_obj;
lean_object* v_a_2571_ = stack[12].m_obj;
lean_object* v_res_2598_;
v_res_2598_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_box(0), v_ctx_2560_, v_target_2561_, v_x_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
stack->m_obj
 = v_res_2598_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_2599_, lean_object* v_ctx_2600_, lean_object* v_target_2601_, lean_object* v_x_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_2599_, v_ctx_2600_, v_target_2601_, v_x_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
return v_res_2613_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_ctx_2614_, lean_object* v_target_2615_, lean_object* v_x_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2627_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2628_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2629_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2630_ = 0;
v___x_2631_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2631_, 0, v___x_2627_);
lean_ctor_set(v___x_2631_, 1, v___x_2628_);
lean_ctor_set(v___x_2631_, 2, v_target_2615_);
lean_ctor_set(v___x_2631_, 3, v___x_2629_);
lean_ctor_set_uint8(v___x_2631_, sizeof(void*)*4, v___x_2630_);
v___x_2632_ = lean_st_mk_ref(v___x_2631_);
lean_inc(v_a_2625_);
lean_inc_ref(v_a_2624_);
lean_inc(v_a_2623_);
lean_inc_ref(v_a_2622_);
lean_inc(v_a_2621_);
lean_inc_ref(v_a_2620_);
lean_inc(v_a_2619_);
lean_inc_ref(v_a_2618_);
lean_inc(v_a_2617_);
lean_inc(v___x_2632_);
v___x_2633_ = lean_apply_12(v_x_2616_, v_ctx_2614_, v___x_2632_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, lean_box(0));
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2642_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_st_ref_get(v___x_2632_);
lean_dec(v___x_2632_);
lean_dec(v___x_2638_);
if (v_isShared_2637_ == 0)
{
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2634_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_dec(v___x_2632_);
return v___x_2633_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2614_ = stack[0].m_obj;
lean_object* v_target_2615_ = stack[1].m_obj;
lean_object* v_x_2616_ = stack[2].m_obj;
lean_object* v_a_2617_ = stack[3].m_obj;
lean_object* v_a_2618_ = stack[4].m_obj;
lean_object* v_a_2619_ = stack[5].m_obj;
lean_object* v_a_2620_ = stack[6].m_obj;
lean_object* v_a_2621_ = stack[7].m_obj;
lean_object* v_a_2622_ = stack[8].m_obj;
lean_object* v_a_2623_ = stack[9].m_obj;
lean_object* v_a_2624_ = stack[10].m_obj;
lean_object* v_a_2625_ = stack[11].m_obj;
lean_object* v_res_2643_;
v_res_2643_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_ctx_2614_, v_target_2615_, v_x_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
stack->m_obj
 = v_res_2643_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_ctx_2644_, lean_object* v_target_2645_, lean_object* v_x_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_ctx_2644_, v_target_2645_, v_x_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
return v_res_2657_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_2658_, lean_object* v_ctx_2659_, lean_object* v_target_2660_, lean_object* v_x_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2672_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2673_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2674_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2675_ = 0;
v___x_2676_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2676_, 0, v___x_2672_);
lean_ctor_set(v___x_2676_, 1, v___x_2673_);
lean_ctor_set(v___x_2676_, 2, v_target_2660_);
lean_ctor_set(v___x_2676_, 3, v___x_2674_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*4, v___x_2675_);
v___x_2677_ = lean_st_mk_ref(v___x_2676_);
lean_inc(v_a_2670_);
lean_inc_ref(v_a_2669_);
lean_inc(v_a_2668_);
lean_inc_ref(v_a_2667_);
lean_inc(v_a_2666_);
lean_inc_ref(v_a_2665_);
lean_inc(v_a_2664_);
lean_inc_ref(v_a_2663_);
lean_inc(v_a_2662_);
lean_inc(v___x_2677_);
v___x_2678_ = lean_apply_12(v_x_2661_, v_ctx_2659_, v___x_2677_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, lean_box(0));
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2687_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2687_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2687_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = lean_st_ref_get(v___x_2677_);
lean_dec(v___x_2677_);
lean_dec(v___x_2683_);
if (v_isShared_2682_ == 0)
{
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2679_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
else
{
lean_dec(v___x_2677_);
return v___x_2678_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2659_ = stack[1].m_obj;
lean_object* v_target_2660_ = stack[2].m_obj;
lean_object* v_x_2661_ = stack[3].m_obj;
lean_object* v_a_2662_ = stack[4].m_obj;
lean_object* v_a_2663_ = stack[5].m_obj;
lean_object* v_a_2664_ = stack[6].m_obj;
lean_object* v_a_2665_ = stack[7].m_obj;
lean_object* v_a_2666_ = stack[8].m_obj;
lean_object* v_a_2667_ = stack[9].m_obj;
lean_object* v_a_2668_ = stack[10].m_obj;
lean_object* v_a_2669_ = stack[11].m_obj;
lean_object* v_a_2670_ = stack[12].m_obj;
lean_object* v_res_2688_;
v_res_2688_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_box(0), v_ctx_2659_, v_target_2660_, v_x_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
stack->m_obj
 = v_res_2688_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_2689_, lean_object* v_ctx_2690_, lean_object* v_target_2691_, lean_object* v_x_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_2689_, v_ctx_2690_, v_target_2691_, v_x_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
return v_res_2703_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2707_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2708_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2707_, v___x_2706_);
return v___x_2708_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___f_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2);
v___f_2710_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2711_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2710_, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3);
v___x_2713_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2714_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2713_, v___x_2712_);
return v___x_2714_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___f_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4);
v___f_2716_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2717_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2716_, v___x_2715_);
return v___x_2717_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5);
v___x_2719_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2720_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2719_, v___x_2718_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___f_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6);
v___f_2722_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2723_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2722_, v___x_2721_);
return v___x_2723_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___f_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7);
v___f_2725_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2726_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2725_, v___x_2724_);
return v___x_2726_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___x_2728_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2729_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2728_, v___x_2727_);
return v___x_2729_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___f_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___f_2731_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2732_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2731_, v___x_2730_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2735_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2736_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2737_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2738_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2737_, v___x_2736_, v___x_2735_);
return v___x_2738_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___f_2740_; lean_object* v___f_2741_; lean_object* v___x_2742_; 
v___x_2739_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___f_2740_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2741_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2742_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2741_, v___f_2740_, v___x_2739_);
return v___x_2742_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2743_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14);
v___x_2744_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2745_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2746_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2745_, v___x_2744_, v___x_2743_);
return v___x_2746_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v___f_2749_; lean_object* v___x_2750_; 
v___x_2747_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15);
v___f_2748_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2749_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2750_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2749_, v___f_2748_, v___x_2747_);
return v___x_2750_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2751_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16);
v___x_2752_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2753_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2754_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2753_, v___x_2752_, v___x_2751_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; 
v___x_2755_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___f_2756_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2757_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2758_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2757_, v___f_2756_, v___x_2755_);
return v___x_2758_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___f_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; 
v___x_2759_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18);
v___f_2760_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2761_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2762_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2761_, v___f_2760_, v___x_2759_);
return v___x_2762_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19);
v___x_2764_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2765_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2766_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2765_, v___x_2764_, v___x_2763_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___x_2770_; 
v___x_2767_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___f_2768_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2769_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2770_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2769_, v___f_2768_, v___x_2767_);
return v___x_2770_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v_cls_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_cls_2781_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2782_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_2783_ = l_Lean_Name_append(v___x_2782_, v_cls_2781_);
return v___x_2783_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___f_2786_; 
v___x_2784_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2785_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2786_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2786_, 0, v___x_2785_);
lean_closure_set(v___f_2786_, 1, v___x_2784_);
return v___f_2786_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___f_2787_; lean_object* v___f_2788_; lean_object* v___f_2789_; 
v___f_2787_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2788_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___f_2789_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2789_, 0, v___f_2788_);
lean_closure_set(v___f_2789_, 1, v___f_2787_);
return v___f_2789_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___f_2791_; lean_object* v___f_2792_; 
v___x_2790_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2791_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2792_, 0, v___f_2791_);
lean_closure_set(v___f_2792_, 1, v___x_2790_);
return v___f_2792_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___f_2793_; lean_object* v___f_2794_; lean_object* v___f_2795_; 
v___f_2793_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2794_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_2795_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2795_, 0, v___f_2794_);
lean_closure_set(v___f_2795_, 1, v___f_2793_);
return v___f_2795_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33(void){
_start:
{
lean_object* v___f_2796_; lean_object* v___f_2797_; lean_object* v___f_2798_; 
v___f_2796_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2797_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___f_2798_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2798_, 0, v___f_2797_);
lean_closure_set(v___f_2798_, 1, v___f_2796_);
return v___f_2798_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___f_2800_; lean_object* v___f_2801_; 
v___x_2799_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2800_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33);
v___f_2801_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2801_, 0, v___f_2800_);
lean_closure_set(v___f_2801_, 1, v___x_2799_);
return v___f_2801_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35(void){
_start:
{
lean_object* v___f_2802_; lean_object* v___f_2803_; lean_object* v___f_2804_; 
v___f_2802_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2803_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2804_, 0, v___f_2803_);
lean_closure_set(v___f_2804_, 1, v___f_2802_);
return v___f_2804_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36));
v___x_2807_ = l_Lean_stringToMessageData(v___x_2806_);
return v___x_2807_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v___y_2822_; lean_object* v___x_2840_; lean_object* v_toApplicative_2841_; lean_object* v_toFunctor_2842_; lean_object* v_toSeq_2843_; lean_object* v_toSeqLeft_2844_; lean_object* v_toSeqRight_2845_; lean_object* v___f_2846_; lean_object* v___f_2847_; lean_object* v___f_2848_; lean_object* v___f_2849_; lean_object* v___x_2850_; lean_object* v___f_2851_; lean_object* v___f_2852_; lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v_toApplicative_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2908_; 
v___x_2840_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2841_ = lean_ctor_get(v___x_2840_, 0);
v_toFunctor_2842_ = lean_ctor_get(v_toApplicative_2841_, 0);
v_toSeq_2843_ = lean_ctor_get(v_toApplicative_2841_, 2);
v_toSeqLeft_2844_ = lean_ctor_get(v_toApplicative_2841_, 3);
v_toSeqRight_2845_ = lean_ctor_get(v_toApplicative_2841_, 4);
v___f_2846_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2847_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2842_, 2);
v___f_2848_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2848_, 0, v_toFunctor_2842_);
v___f_2849_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2849_, 0, v_toFunctor_2842_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___f_2848_);
lean_ctor_set(v___x_2850_, 1, v___f_2849_);
lean_inc(v_toSeqRight_2845_);
v___f_2851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2851_, 0, v_toSeqRight_2845_);
lean_inc(v_toSeqLeft_2844_);
v___f_2852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2852_, 0, v_toSeqLeft_2844_);
lean_inc(v_toSeq_2843_);
v___f_2853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2853_, 0, v_toSeq_2843_);
v___x_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2850_);
lean_ctor_set(v___x_2854_, 1, v___f_2846_);
lean_ctor_set(v___x_2854_, 2, v___f_2853_);
lean_ctor_set(v___x_2854_, 3, v___f_2852_);
lean_ctor_set(v___x_2854_, 4, v___f_2851_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___f_2847_);
v___x_2856_ = l_StateRefT_x27_instMonad___redArg(v___x_2855_);
v_toApplicative_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v___x_2856_, 1);
lean_dec(v_unused_2909_);
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2908_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_toApplicative_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2908_;
goto v_resetjp_2858_;
}
v___jp_2821_:
{
lean_object* v___x_2823_; lean_object* v_caches_2824_; lean_object* v_typeAnalysis_2825_; lean_object* v_target_2826_; lean_object* v_hypotheses_2827_; uint8_t v_didChange_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2839_; 
v___x_2823_ = lean_st_ref_take(v___y_2822_);
v_caches_2824_ = lean_ctor_get(v___x_2823_, 0);
v_typeAnalysis_2825_ = lean_ctor_get(v___x_2823_, 1);
v_target_2826_ = lean_ctor_get(v___x_2823_, 2);
v_hypotheses_2827_ = lean_ctor_get(v___x_2823_, 3);
v_didChange_2828_ = lean_ctor_get_uint8(v___x_2823_, sizeof(void*)*4);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2830_ = v___x_2823_;
v_isShared_2831_ = v_isSharedCheck_2839_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_hypotheses_2827_);
lean_inc(v_target_2826_);
lean_inc(v_typeAnalysis_2825_);
lean_inc(v_caches_2824_);
lean_dec(v___x_2823_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2839_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2832_ = lean_box(0);
v___x_2833_ = lean_array_push(v_hypotheses_2827_, v_hyp_2808_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 3, v___x_2833_);
v___x_2835_ = v___x_2830_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_caches_2824_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_typeAnalysis_2825_);
lean_ctor_set(v_reuseFailAlloc_2838_, 2, v_target_2826_);
lean_ctor_set(v_reuseFailAlloc_2838_, 3, v___x_2833_);
lean_ctor_set_uint8(v_reuseFailAlloc_2838_, sizeof(void*)*4, v_didChange_2828_);
v___x_2835_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_st_ref_put(v___y_2822_, v___x_2835_);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2832_);
return v___x_2837_;
}
}
}
v_resetjp_2858_:
{
lean_object* v_toFunctor_2861_; lean_object* v_toSeq_2862_; lean_object* v_toSeqLeft_2863_; lean_object* v_toSeqRight_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2906_; 
v_toFunctor_2861_ = lean_ctor_get(v_toApplicative_2857_, 0);
v_toSeq_2862_ = lean_ctor_get(v_toApplicative_2857_, 2);
v_toSeqLeft_2863_ = lean_ctor_get(v_toApplicative_2857_, 3);
v_toSeqRight_2864_ = lean_ctor_get(v_toApplicative_2857_, 4);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_toApplicative_2857_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v_toApplicative_2857_, 1);
lean_dec(v_unused_2907_);
v___x_2866_ = v_toApplicative_2857_;
v_isShared_2867_ = v_isSharedCheck_2906_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_toSeqRight_2864_);
lean_inc(v_toSeqLeft_2863_);
lean_inc(v_toSeq_2862_);
lean_inc(v_toFunctor_2861_);
lean_dec(v_toApplicative_2857_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2906_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___f_2868_; lean_object* v___f_2869_; lean_object* v___f_2870_; lean_object* v___f_2871_; lean_object* v___x_2872_; lean_object* v___f_2873_; lean_object* v___f_2874_; lean_object* v___f_2875_; lean_object* v___x_2877_; 
v___f_2868_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2869_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2861_);
v___f_2870_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2870_, 0, v_toFunctor_2861_);
v___f_2871_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2871_, 0, v_toFunctor_2861_);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___f_2870_);
lean_ctor_set(v___x_2872_, 1, v___f_2871_);
v___f_2873_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2873_, 0, v_toSeqRight_2864_);
v___f_2874_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2874_, 0, v_toSeqLeft_2863_);
v___f_2875_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2875_, 0, v_toSeq_2862_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 4, v___f_2873_);
lean_ctor_set(v___x_2866_, 3, v___f_2874_);
lean_ctor_set(v___x_2866_, 2, v___f_2875_);
lean_ctor_set(v___x_2866_, 1, v___f_2868_);
lean_ctor_set(v___x_2866_, 0, v___x_2872_);
v___x_2877_ = v___x_2866_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v___f_2868_);
lean_ctor_set(v_reuseFailAlloc_2905_, 2, v___f_2875_);
lean_ctor_set(v_reuseFailAlloc_2905_, 3, v___f_2874_);
lean_ctor_set(v_reuseFailAlloc_2905_, 4, v___f_2873_);
v___x_2877_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2879_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___f_2869_);
lean_ctor_set(v___x_2859_, 0, v___x_2877_);
v___x_2879_ = v___x_2859_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v___f_2869_);
v___x_2879_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v_toCold_2889_; lean_object* v_options_2890_; uint8_t v_hasTrace_2891_; 
v___x_2880_ = l_StateRefT_x27_instMonad___redArg(v___x_2879_);
v___x_2881_ = l_ReaderT_instMonad___redArg(v___x_2880_);
v___x_2882_ = l_StateRefT_x27_instMonad___redArg(v___x_2881_);
v___x_2883_ = l_ReaderT_instMonad___redArg(v___x_2882_);
v___x_2884_ = l_ReaderT_instMonad___redArg(v___x_2883_);
v___x_2885_ = l_StateRefT_x27_instMonad___redArg(v___x_2884_);
v___x_2886_ = l_ReaderT_instMonad___redArg(v___x_2885_);
v___x_2887_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2888_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toCold_2889_ = lean_ctor_get(v_a_2818_, 0);
v_options_2890_ = lean_ctor_get(v_toCold_2889_, 2);
v_hasTrace_2891_ = lean_ctor_get_uint8(v_options_2890_, sizeof(void*)*1);
if (v_hasTrace_2891_ == 0)
{
lean_dec_ref(v___x_2886_);
v___y_2822_ = v_a_2810_;
goto v___jp_2821_;
}
else
{
lean_object* v_toMonadRef_2892_; lean_object* v_inheritedTraceOptions_2893_; lean_object* v_cls_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v_toMonadRef_2892_ = lean_ctor_get(v___x_2888_, 0);
v_inheritedTraceOptions_2893_ = lean_ctor_get(v_toCold_2889_, 11);
v_cls_2894_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2895_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2896_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2893_, v_options_2890_, v___x_2895_);
if (v___x_2896_ == 0)
{
lean_dec_ref(v___x_2886_);
v___y_2822_ = v_a_2810_;
goto v___jp_2821_;
}
else
{
lean_object* v_type_2897_; lean_object* v___f_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_5398__overap_2902_; lean_object* v___x_2903_; 
v_type_2897_ = lean_ctor_get(v_hyp_2808_, 1);
v___f_2898_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_2899_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_2897_);
v___x_2900_ = l_Lean_MessageData_ofExpr(v_type_2897_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
lean_inc_ref(v_toMonadRef_2892_);
v___x_5398__overap_2902_ = l_Lean_addTrace___redArg(v___x_2886_, v___x_2887_, v_toMonadRef_2892_, v___f_2898_, v_cls_2894_, v___x_2901_);
lean_inc(v_a_2819_);
lean_inc_ref(v_a_2818_);
lean_inc(v_a_2817_);
lean_inc_ref(v_a_2816_);
lean_inc(v_a_2815_);
lean_inc_ref(v_a_2814_);
lean_inc(v_a_2813_);
lean_inc_ref(v_a_2812_);
lean_inc(v_a_2811_);
lean_inc(v_a_2810_);
lean_inc_ref(v_a_2809_);
v___x_2903_ = lean_apply_12(v___x_5398__overap_2902_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, lean_box(0));
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_dec_ref_known(v___x_2903_, 1);
v___y_2822_ = v_a_2810_;
goto v___jp_2821_;
}
else
{
lean_dec_ref(v_hyp_2808_);
return v___x_2903_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_2808_ = stack[0].m_obj;
lean_object* v_a_2809_ = stack[1].m_obj;
lean_object* v_a_2810_ = stack[2].m_obj;
lean_object* v_a_2811_ = stack[3].m_obj;
lean_object* v_a_2812_ = stack[4].m_obj;
lean_object* v_a_2813_ = stack[5].m_obj;
lean_object* v_a_2814_ = stack[6].m_obj;
lean_object* v_a_2815_ = stack[7].m_obj;
lean_object* v_a_2816_ = stack[8].m_obj;
lean_object* v_a_2817_ = stack[9].m_obj;
lean_object* v_a_2818_ = stack[10].m_obj;
lean_object* v_a_2819_ = stack[11].m_obj;
lean_object* v_res_2910_;
v_res_2910_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
stack->m_obj
 = v_res_2910_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
return v_res_2924_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2925_, lean_object* v___x_2926_, lean_object* v_toMonadRef_2927_, lean_object* v___f_2928_, lean_object* v_x_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_toCold_2946_; lean_object* v_options_2947_; uint8_t v_hasTrace_2948_; 
v_toCold_2946_ = lean_ctor_get(v___y_2940_, 0);
v_options_2947_ = lean_ctor_get(v_toCold_2946_, 2);
v_hasTrace_2948_ = lean_ctor_get_uint8(v_options_2947_, sizeof(void*)*1);
if (v_hasTrace_2948_ == 0)
{
lean_dec_ref(v___y_2930_);
lean_dec(v___f_2928_);
lean_dec_ref(v_toMonadRef_2927_);
lean_dec_ref(v___x_2926_);
lean_dec_ref(v___x_2925_);
goto v___jp_2943_;
}
else
{
lean_object* v_inheritedTraceOptions_2949_; lean_object* v_cls_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v_inheritedTraceOptions_2949_ = lean_ctor_get(v_toCold_2946_, 11);
v_cls_2950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2951_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2952_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2949_, v_options_2947_, v___x_2951_);
if (v___x_2952_ == 0)
{
lean_dec_ref(v___y_2930_);
lean_dec(v___f_2928_);
lean_dec_ref(v_toMonadRef_2927_);
lean_dec_ref(v___x_2926_);
lean_dec_ref(v___x_2925_);
goto v___jp_2943_;
}
else
{
lean_object* v_type_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_6389__overap_2957_; lean_object* v___x_2958_; 
v_type_2953_ = lean_ctor_get(v___y_2930_, 1);
lean_inc_ref(v_type_2953_);
lean_dec_ref(v___y_2930_);
v___x_2954_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2955_ = l_Lean_MessageData_ofExpr(v_type_2953_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_6389__overap_2957_ = l_Lean_addTrace___redArg(v___x_2925_, v___x_2926_, v_toMonadRef_2927_, v___f_2928_, v_cls_2950_, v___x_2956_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc(v___y_2937_);
lean_inc_ref(v___y_2936_);
lean_inc(v___y_2935_);
lean_inc_ref(v___y_2934_);
lean_inc(v___y_2933_);
lean_inc(v___y_2932_);
lean_inc_ref(v___y_2931_);
v___x_2958_ = lean_apply_12(v___x_6389__overap_2957_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, lean_box(0));
return v___x_2958_;
}
}
v___jp_2943_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
return v___x_2945_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2925_ = stack[0].m_obj;
lean_object* v___x_2926_ = stack[1].m_obj;
lean_object* v_toMonadRef_2927_ = stack[2].m_obj;
lean_object* v___f_2928_ = stack[3].m_obj;
lean_object* v_x_2929_ = stack[4].m_obj;
lean_object* v___y_2930_ = stack[5].m_obj;
lean_object* v___y_2931_ = stack[6].m_obj;
lean_object* v___y_2932_ = stack[7].m_obj;
lean_object* v___y_2933_ = stack[8].m_obj;
lean_object* v___y_2934_ = stack[9].m_obj;
lean_object* v___y_2935_ = stack[10].m_obj;
lean_object* v___y_2936_ = stack[11].m_obj;
lean_object* v___y_2937_ = stack[12].m_obj;
lean_object* v___y_2938_ = stack[13].m_obj;
lean_object* v___y_2939_ = stack[14].m_obj;
lean_object* v___y_2940_ = stack[15].m_obj;
lean_object* v___y_2941_ = stack[16].m_obj;
lean_object* v_res_2959_;
v_res_2959_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2925_, v___x_2926_, v_toMonadRef_2927_, v___f_2928_, v_x_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
stack->m_obj
 = v_res_2959_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2960_ = _args[0];
lean_object* v___x_2961_ = _args[1];
lean_object* v_toMonadRef_2962_ = _args[2];
lean_object* v___f_2963_ = _args[3];
lean_object* v_x_2964_ = _args[4];
lean_object* v___y_2965_ = _args[5];
lean_object* v___y_2966_ = _args[6];
lean_object* v___y_2967_ = _args[7];
lean_object* v___y_2968_ = _args[8];
lean_object* v___y_2969_ = _args[9];
lean_object* v___y_2970_ = _args[10];
lean_object* v___y_2971_ = _args[11];
lean_object* v___y_2972_ = _args[12];
lean_object* v___y_2973_ = _args[13];
lean_object* v___y_2974_ = _args[14];
lean_object* v___y_2975_ = _args[15];
lean_object* v___y_2976_ = _args[16];
lean_object* v___y_2977_ = _args[17];
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2960_, v___x_2961_, v_toMonadRef_2962_, v___f_2963_, v_x_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
return v_res_2978_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___y_3011_; lean_object* v___x_3012_; lean_object* v_toApplicative_3013_; lean_object* v_toFunctor_3014_; lean_object* v_toSeq_3015_; lean_object* v_toSeqLeft_3016_; lean_object* v_toSeqRight_3017_; lean_object* v___f_3018_; lean_object* v___f_3019_; lean_object* v___f_3020_; lean_object* v___f_3021_; lean_object* v___x_3022_; lean_object* v___f_3023_; lean_object* v___f_3024_; lean_object* v___f_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_toApplicative_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3081_; 
v___x_3012_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_3013_ = lean_ctor_get(v___x_3012_, 0);
v_toFunctor_3014_ = lean_ctor_get(v_toApplicative_3013_, 0);
v_toSeq_3015_ = lean_ctor_get(v_toApplicative_3013_, 2);
v_toSeqLeft_3016_ = lean_ctor_get(v_toApplicative_3013_, 3);
v_toSeqRight_3017_ = lean_ctor_get(v_toApplicative_3013_, 4);
v___f_3018_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_3019_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_3014_, 2);
v___f_3020_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3020_, 0, v_toFunctor_3014_);
v___f_3021_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3021_, 0, v_toFunctor_3014_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___f_3020_);
lean_ctor_set(v___x_3022_, 1, v___f_3021_);
lean_inc(v_toSeqRight_3017_);
v___f_3023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3023_, 0, v_toSeqRight_3017_);
lean_inc(v_toSeqLeft_3016_);
v___f_3024_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3024_, 0, v_toSeqLeft_3016_);
lean_inc(v_toSeq_3015_);
v___f_3025_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3025_, 0, v_toSeq_3015_);
v___x_3026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3022_);
lean_ctor_set(v___x_3026_, 1, v___f_3018_);
lean_ctor_set(v___x_3026_, 2, v___f_3025_);
lean_ctor_set(v___x_3026_, 3, v___f_3024_);
lean_ctor_set(v___x_3026_, 4, v___f_3023_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v___f_3019_);
v___x_3028_ = l_StateRefT_x27_instMonad___redArg(v___x_3027_);
v_toApplicative_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v___x_3028_, 1);
lean_dec(v_unused_3082_);
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3081_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_toApplicative_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3081_;
goto v_resetjp_3030_;
}
v___jp_2992_:
{
lean_object* v___x_2993_; lean_object* v_caches_2994_; lean_object* v_typeAnalysis_2995_; lean_object* v_target_2996_; lean_object* v_hypotheses_2997_; uint8_t v_didChange_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3009_; 
v___x_2993_ = lean_st_ref_take(v_a_2981_);
v_caches_2994_ = lean_ctor_get(v___x_2993_, 0);
v_typeAnalysis_2995_ = lean_ctor_get(v___x_2993_, 1);
v_target_2996_ = lean_ctor_get(v___x_2993_, 2);
v_hypotheses_2997_ = lean_ctor_get(v___x_2993_, 3);
v_didChange_2998_ = lean_ctor_get_uint8(v___x_2993_, sizeof(void*)*4);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3000_ = v___x_2993_;
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_hypotheses_2997_);
lean_inc(v_target_2996_);
lean_inc(v_typeAnalysis_2995_);
lean_inc(v_caches_2994_);
lean_dec(v___x_2993_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3002_ = lean_box(0);
v___x_3003_ = l_Array_append___redArg(v_hypotheses_2997_, v_hyps_2979_);
lean_dec_ref(v_hyps_2979_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 3, v___x_3003_);
v___x_3005_ = v___x_3000_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_caches_2994_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_typeAnalysis_2995_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_target_2996_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v___x_3003_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, sizeof(void*)*4, v_didChange_2998_);
v___x_3005_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_st_ref_put(v_a_2981_, v___x_3005_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3002_);
return v___x_3007_;
}
}
}
v___jp_3010_:
{
if (lean_obj_tag(v___y_3011_) == 0)
{
lean_dec_ref_known(v___y_3011_, 1);
goto v___jp_2992_;
}
else
{
lean_dec_ref(v_hyps_2979_);
return v___y_3011_;
}
}
v_resetjp_3030_:
{
lean_object* v_toFunctor_3033_; lean_object* v_toSeq_3034_; lean_object* v_toSeqLeft_3035_; lean_object* v_toSeqRight_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3079_; 
v_toFunctor_3033_ = lean_ctor_get(v_toApplicative_3029_, 0);
v_toSeq_3034_ = lean_ctor_get(v_toApplicative_3029_, 2);
v_toSeqLeft_3035_ = lean_ctor_get(v_toApplicative_3029_, 3);
v_toSeqRight_3036_ = lean_ctor_get(v_toApplicative_3029_, 4);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_toApplicative_3029_);
if (v_isSharedCheck_3079_ == 0)
{
lean_object* v_unused_3080_; 
v_unused_3080_ = lean_ctor_get(v_toApplicative_3029_, 1);
lean_dec(v_unused_3080_);
v___x_3038_ = v_toApplicative_3029_;
v_isShared_3039_ = v_isSharedCheck_3079_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_toSeqRight_3036_);
lean_inc(v_toSeqLeft_3035_);
lean_inc(v_toSeq_3034_);
lean_inc(v_toFunctor_3033_);
lean_dec(v_toApplicative_3029_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3079_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___f_3040_; lean_object* v___f_3041_; lean_object* v___f_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___f_3047_; lean_object* v___x_3049_; 
v___f_3040_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_3041_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_3033_);
v___f_3042_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3042_, 0, v_toFunctor_3033_);
v___f_3043_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3043_, 0, v_toFunctor_3033_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___f_3042_);
lean_ctor_set(v___x_3044_, 1, v___f_3043_);
v___f_3045_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3045_, 0, v_toSeqRight_3036_);
v___f_3046_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3046_, 0, v_toSeqLeft_3035_);
v___f_3047_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3047_, 0, v_toSeq_3034_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 4, v___f_3045_);
lean_ctor_set(v___x_3038_, 3, v___f_3046_);
lean_ctor_set(v___x_3038_, 2, v___f_3047_);
lean_ctor_set(v___x_3038_, 1, v___f_3040_);
lean_ctor_set(v___x_3038_, 0, v___x_3044_);
v___x_3049_ = v___x_3038_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3044_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___f_3040_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v___f_3047_);
lean_ctor_set(v_reuseFailAlloc_3078_, 3, v___f_3046_);
lean_ctor_set(v_reuseFailAlloc_3078_, 4, v___f_3045_);
v___x_3049_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3051_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 1, v___f_3041_);
lean_ctor_set(v___x_3031_, 0, v___x_3049_);
v___x_3051_ = v___x_3031_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___f_3041_);
v___x_3051_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_toMonadRef_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3052_ = l_StateRefT_x27_instMonad___redArg(v___x_3051_);
v___x_3053_ = l_ReaderT_instMonad___redArg(v___x_3052_);
v___x_3054_ = l_StateRefT_x27_instMonad___redArg(v___x_3053_);
v___x_3055_ = l_ReaderT_instMonad___redArg(v___x_3054_);
v___x_3056_ = l_ReaderT_instMonad___redArg(v___x_3055_);
v___x_3057_ = l_StateRefT_x27_instMonad___redArg(v___x_3056_);
v___x_3058_ = l_ReaderT_instMonad___redArg(v___x_3057_);
v___x_3059_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_3060_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_3061_ = lean_ctor_get(v___x_3060_, 0);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = lean_array_get_size(v_hyps_2979_);
v___x_3064_ = lean_nat_dec_lt(v___x_3062_, v___x_3063_);
if (v___x_3064_ == 0)
{
lean_dec_ref(v___x_3058_);
goto v___jp_2992_;
}
else
{
lean_object* v___f_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___f_3065_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
lean_inc_ref(v_toMonadRef_3061_);
lean_inc_ref(v___x_3058_);
v___f_3066_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 18, 4);
lean_closure_set(v___f_3066_, 0, v___x_3058_);
lean_closure_set(v___f_3066_, 1, v___x_3059_);
lean_closure_set(v___f_3066_, 2, v_toMonadRef_3061_);
lean_closure_set(v___f_3066_, 3, v___f_3065_);
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_nat_dec_le(v___x_3063_, v___x_3063_);
if (v___x_3068_ == 0)
{
if (v___x_3064_ == 0)
{
lean_dec_ref(v___f_3066_);
lean_dec_ref(v___x_3058_);
goto v___jp_2992_;
}
else
{
size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_6041__overap_3071_; lean_object* v___x_3072_; 
v___x_3069_ = ((size_t)0ULL);
v___x_3070_ = lean_usize_of_nat(v___x_3063_);
lean_inc_ref(v_hyps_2979_);
v___x_6041__overap_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3058_, v___f_3066_, v_hyps_2979_, v___x_3069_, v___x_3070_, v___x_3067_);
lean_inc(v_a_2990_);
lean_inc_ref(v_a_2989_);
lean_inc(v_a_2988_);
lean_inc_ref(v_a_2987_);
lean_inc(v_a_2986_);
lean_inc_ref(v_a_2985_);
lean_inc(v_a_2984_);
lean_inc_ref(v_a_2983_);
lean_inc(v_a_2982_);
lean_inc(v_a_2981_);
lean_inc_ref(v_a_2980_);
v___x_3072_ = lean_apply_12(v___x_6041__overap_3071_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, lean_box(0));
v___y_3011_ = v___x_3072_;
goto v___jp_3010_;
}
}
else
{
size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_6044__overap_3075_; lean_object* v___x_3076_; 
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = lean_usize_of_nat(v___x_3063_);
lean_inc_ref(v_hyps_2979_);
v___x_6044__overap_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3058_, v___f_3066_, v_hyps_2979_, v___x_3073_, v___x_3074_, v___x_3067_);
lean_inc(v_a_2990_);
lean_inc_ref(v_a_2989_);
lean_inc(v_a_2988_);
lean_inc_ref(v_a_2987_);
lean_inc(v_a_2986_);
lean_inc_ref(v_a_2985_);
lean_inc(v_a_2984_);
lean_inc_ref(v_a_2983_);
lean_inc(v_a_2982_);
lean_inc(v_a_2981_);
lean_inc_ref(v_a_2980_);
v___x_3076_ = lean_apply_12(v___x_6044__overap_3075_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, lean_box(0));
v___y_3011_ = v___x_3076_;
goto v___jp_3010_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyps_2979_ = stack[0].m_obj;
lean_object* v_a_2980_ = stack[1].m_obj;
lean_object* v_a_2981_ = stack[2].m_obj;
lean_object* v_a_2982_ = stack[3].m_obj;
lean_object* v_a_2983_ = stack[4].m_obj;
lean_object* v_a_2984_ = stack[5].m_obj;
lean_object* v_a_2985_ = stack[6].m_obj;
lean_object* v_a_2986_ = stack[7].m_obj;
lean_object* v_a_2987_ = stack[8].m_obj;
lean_object* v_a_2988_ = stack[9].m_obj;
lean_object* v_a_2989_ = stack[10].m_obj;
lean_object* v_a_2990_ = stack[11].m_obj;
lean_object* v_res_3083_;
v_res_3083_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
stack->m_obj
 = v_res_3083_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
return v_res_3097_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_3098_){
_start:
{
lean_object* v___x_3100_; lean_object* v_hypotheses_3101_; lean_object* v___x_3102_; 
v___x_3100_ = lean_st_ref_get(v_a_3098_);
v_hypotheses_3101_ = lean_ctor_get(v___x_3100_, 3);
lean_inc_ref(v_hypotheses_3101_);
lean_dec(v___x_3100_);
v___x_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_hypotheses_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3098_ = stack[0].m_obj;
lean_object* v_res_3103_;
v_res_3103_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_3098_);
stack->m_obj
 = v_res_3103_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_3104_);
lean_dec(v_a_3104_);
return v_res_3106_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v_hypotheses_3120_; lean_object* v___x_3121_; 
v___x_3119_ = lean_st_ref_get(v_a_3108_);
v_hypotheses_3120_ = lean_ctor_get(v___x_3119_, 3);
lean_inc_ref(v_hypotheses_3120_);
lean_dec(v___x_3119_);
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_hypotheses_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3107_ = stack[0].m_obj;
lean_object* v_a_3108_ = stack[1].m_obj;
lean_object* v_a_3109_ = stack[2].m_obj;
lean_object* v_a_3110_ = stack[3].m_obj;
lean_object* v_a_3111_ = stack[4].m_obj;
lean_object* v_a_3112_ = stack[5].m_obj;
lean_object* v_a_3113_ = stack[6].m_obj;
lean_object* v_a_3114_ = stack[7].m_obj;
lean_object* v_a_3115_ = stack[8].m_obj;
lean_object* v_a_3116_ = stack[9].m_obj;
lean_object* v_a_3117_ = stack[10].m_obj;
lean_object* v_res_3122_;
v_res_3122_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
stack->m_obj
 = v_res_3122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
return v_res_3135_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v_caches_3150_; lean_object* v_typeAnalysis_3151_; lean_object* v_target_3152_; uint8_t v_didChange_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3163_; 
v___x_3149_ = lean_st_ref_take(v___y_3138_);
v_caches_3150_ = lean_ctor_get(v___x_3149_, 0);
v_typeAnalysis_3151_ = lean_ctor_get(v___x_3149_, 1);
v_target_3152_ = lean_ctor_get(v___x_3149_, 2);
v_didChange_3153_ = lean_ctor_get_uint8(v___x_3149_, sizeof(void*)*4);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v___x_3149_, 3);
lean_dec(v_unused_3164_);
v___x_3155_ = v___x_3149_;
v_isShared_3156_ = v_isSharedCheck_3163_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_target_3152_);
lean_inc(v_typeAnalysis_3151_);
lean_inc(v_caches_3150_);
lean_dec(v___x_3149_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3163_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3157_ = lean_box(0);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 3, v_hyps_3136_);
v___x_3159_ = v___x_3155_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_caches_3150_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_typeAnalysis_3151_);
lean_ctor_set(v_reuseFailAlloc_3162_, 2, v_target_3152_);
lean_ctor_set(v_reuseFailAlloc_3162_, 3, v_hyps_3136_);
lean_ctor_set_uint8(v_reuseFailAlloc_3162_, sizeof(void*)*4, v_didChange_3153_);
v___x_3159_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_st_ref_put(v___y_3138_, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3157_);
return v___x_3161_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyps_3136_ = stack[0].m_obj;
lean_object* v___y_3137_ = stack[1].m_obj;
lean_object* v___y_3138_ = stack[2].m_obj;
lean_object* v___y_3139_ = stack[3].m_obj;
lean_object* v___y_3140_ = stack[4].m_obj;
lean_object* v___y_3141_ = stack[5].m_obj;
lean_object* v___y_3142_ = stack[6].m_obj;
lean_object* v___y_3143_ = stack[7].m_obj;
lean_object* v___y_3144_ = stack[8].m_obj;
lean_object* v___y_3145_ = stack[9].m_obj;
lean_object* v___y_3146_ = stack[10].m_obj;
lean_object* v___y_3147_ = stack[11].m_obj;
lean_object* v_res_3165_;
v_res_3165_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
stack->m_obj
 = v_res_3165_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3180_, lean_object* v_hyps_3181_){
_start:
{
lean_object* v___f_3182_; lean_object* v___x_3183_; 
v___f_3182_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3182_, 0, v_hyps_3181_);
v___x_3183_ = lean_apply_2(v_inst_3180_, lean_box(0), v___f_3182_);
return v___x_3183_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; lean_object* v_caches_3197_; lean_object* v_typeAnalysis_3198_; lean_object* v_target_3199_; uint8_t v_didChange_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3211_; 
v___x_3196_ = lean_st_ref_take(v___y_3185_);
v_caches_3197_ = lean_ctor_get(v___x_3196_, 0);
v_typeAnalysis_3198_ = lean_ctor_get(v___x_3196_, 1);
v_target_3199_ = lean_ctor_get(v___x_3196_, 2);
v_didChange_3200_ = lean_ctor_get_uint8(v___x_3196_, sizeof(void*)*4);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v___x_3196_, 3);
lean_dec(v_unused_3212_);
v___x_3202_ = v___x_3196_;
v_isShared_3203_ = v_isSharedCheck_3211_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_target_3199_);
lean_inc(v_typeAnalysis_3198_);
lean_inc(v_caches_3197_);
lean_dec(v___x_3196_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3211_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3204_ = lean_box(0);
v___x_3205_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 3, v___x_3205_);
v___x_3207_ = v___x_3202_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_caches_3197_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_typeAnalysis_3198_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v_target_3199_);
lean_ctor_set(v_reuseFailAlloc_3210_, 3, v___x_3205_);
lean_ctor_set_uint8(v_reuseFailAlloc_3210_, sizeof(void*)*4, v_didChange_3200_);
v___x_3207_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_st_ref_put(v___y_3185_, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3204_);
return v___x_3209_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3184_ = stack[0].m_obj;
lean_object* v___y_3185_ = stack[1].m_obj;
lean_object* v___y_3186_ = stack[2].m_obj;
lean_object* v___y_3187_ = stack[3].m_obj;
lean_object* v___y_3188_ = stack[4].m_obj;
lean_object* v___y_3189_ = stack[5].m_obj;
lean_object* v___y_3190_ = stack[6].m_obj;
lean_object* v___y_3191_ = stack[7].m_obj;
lean_object* v___y_3192_ = stack[8].m_obj;
lean_object* v___y_3193_ = stack[9].m_obj;
lean_object* v___y_3194_ = stack[10].m_obj;
lean_object* v_res_3213_;
v_res_3213_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
stack->m_obj
 = v_res_3213_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3227_, lean_object* v_cls_3228_, lean_object* v_____do__lift_3229_, lean_object* v_____do__lift_3230_){
_start:
{
uint8_t v_hasTrace_3231_; 
v_hasTrace_3231_ = lean_ctor_get_uint8(v_____do__lift_3230_, sizeof(void*)*1);
if (v_hasTrace_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
lean_dec(v_cls_3228_);
v___x_3232_ = lean_box(v_hasTrace_3231_);
v___x_3233_ = lean_apply_2(v_toPure_3227_, lean_box(0), v___x_3232_);
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3234_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3235_ = l_Lean_Name_append(v___x_3234_, v_cls_3228_);
v___x_3236_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3229_, v_____do__lift_3230_, v___x_3235_);
lean_dec(v___x_3235_);
v___x_3237_ = lean_box(v___x_3236_);
v___x_3238_ = lean_apply_2(v_toPure_3227_, lean_box(0), v___x_3237_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3239_, lean_object* v_cls_3240_, lean_object* v_____do__lift_3241_, lean_object* v_____do__lift_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3239_, v_cls_3240_, v_____do__lift_3241_, v_____do__lift_3242_);
lean_dec_ref(v_____do__lift_3242_);
lean_dec_ref(v_____do__lift_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_inst_3244_, lean_object* v_toPure_3245_, lean_object* v_cls_3246_, lean_object* v_toBind_3247_, lean_object* v_____do__lift_3248_){
_start:
{
lean_object* v_getOptionsUnrestricted_3249_; lean_object* v___f_3250_; lean_object* v___x_3251_; 
v_getOptionsUnrestricted_3249_ = lean_ctor_get(v_inst_3244_, 1);
lean_inc(v_getOptionsUnrestricted_3249_);
lean_dec_ref(v_inst_3244_);
v___f_3250_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3250_, 0, v_toPure_3245_);
lean_closure_set(v___f_3250_, 1, v_cls_3246_);
lean_closure_set(v___f_3250_, 2, v_____do__lift_3248_);
v___x_3251_ = lean_apply_4(v_toBind_3247_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3249_, v___f_3250_);
return v___x_3251_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3254_ = l_Lean_stringToMessageData(v___x_3253_);
return v___x_3254_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3255_, lean_object* v_a_3256_, lean_object* v___y_3257_, lean_object* v_inst_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_cls_3262_, uint8_t v_____do__lift_3263_){
_start:
{
if (v_____do__lift_3263_ == 0)
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec(v_cls_3262_);
lean_dec(v_inst_3261_);
lean_dec_ref(v_inst_3260_);
lean_dec_ref(v_inst_3259_);
lean_dec_ref(v_inst_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v_a_3256_);
v___x_3264_ = lean_box(0);
v___x_3265_ = lean_apply_2(v_toPure_3255_, lean_box(0), v___x_3264_);
return v___x_3265_;
}
else
{
lean_object* v_type_3266_; lean_object* v_type_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v_toPure_3255_);
v_type_3266_ = lean_ctor_get(v_a_3256_, 1);
lean_inc_ref(v_type_3266_);
lean_dec_ref(v_a_3256_);
v_type_3267_ = lean_ctor_get(v___y_3257_, 1);
lean_inc_ref(v_type_3267_);
lean_dec_ref(v___y_3257_);
v___x_3268_ = l_Lean_MessageData_ofExpr(v_type_3266_);
v___x_3269_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = l_Lean_MessageData_ofExpr(v_type_3267_);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = l_Lean_addTrace___redArg(v_inst_3258_, v_inst_3259_, v_inst_3260_, v_inst_3261_, v_cls_3262_, v___x_3272_);
return v___x_3273_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3255_ = stack[0].m_obj;
lean_object* v_a_3256_ = stack[1].m_obj;
lean_object* v___y_3257_ = stack[2].m_obj;
lean_object* v_inst_3258_ = stack[3].m_obj;
lean_object* v_inst_3259_ = stack[4].m_obj;
lean_object* v_inst_3260_ = stack[5].m_obj;
lean_object* v_inst_3261_ = stack[6].m_obj;
lean_object* v_cls_3262_ = stack[7].m_obj;
uint8_t v_____do__lift_3263_ = stack[8].m_num;
lean_object* v_res_3274_;
v_res_3274_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3255_, v_a_3256_, v___y_3257_, v_inst_3258_, v_inst_3259_, v_inst_3260_, v_inst_3261_, v_cls_3262_, v_____do__lift_3263_);
stack->m_obj
 = v_res_3274_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3275_, lean_object* v_a_3276_, lean_object* v___y_3277_, lean_object* v_inst_3278_, lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_inst_3281_, lean_object* v_cls_3282_, lean_object* v_____do__lift_3283_){
_start:
{
uint8_t v_____do__lift_3134__boxed_3284_; lean_object* v_res_3285_; 
v_____do__lift_3134__boxed_3284_ = lean_unbox(v_____do__lift_3283_);
v_res_3285_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3275_, v_a_3276_, v___y_3277_, v_inst_3278_, v_inst_3279_, v_inst_3280_, v_inst_3281_, v_cls_3282_, v_____do__lift_3134__boxed_3284_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_toPure_3288_, lean_object* v_toBind_3289_, lean_object* v_a_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_inst_3293_, lean_object* v_x_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_getInheritedTraceOptions_3296_; lean_object* v_cls_3297_; lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_getInheritedTraceOptions_3296_ = lean_ctor_get(v_inst_3286_, 2);
lean_inc(v_getInheritedTraceOptions_3296_);
v_cls_3297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3289_, 2);
lean_inc(v_toPure_3288_);
v___f_3298_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3298_, 0, v_inst_3287_);
lean_closure_set(v___f_3298_, 1, v_toPure_3288_);
lean_closure_set(v___f_3298_, 2, v_cls_3297_);
lean_closure_set(v___f_3298_, 3, v_toBind_3289_);
v___f_3299_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3299_, 0, v_toPure_3288_);
lean_closure_set(v___f_3299_, 1, v_a_3290_);
lean_closure_set(v___f_3299_, 2, v___y_3295_);
lean_closure_set(v___f_3299_, 3, v_inst_3291_);
lean_closure_set(v___f_3299_, 4, v_inst_3286_);
lean_closure_set(v___f_3299_, 5, v_inst_3292_);
lean_closure_set(v___f_3299_, 6, v_inst_3293_);
lean_closure_set(v___f_3299_, 7, v_cls_3297_);
v___x_3300_ = lean_apply_4(v_toBind_3289_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3296_, v___f_3298_);
v___x_3301_ = lean_apply_4(v_toBind_3289_, lean_box(0), lean_box(0), v___x_3300_, v___f_3299_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3302_, lean_object* v_res_3303_, lean_object* v_____r_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_apply_2(v_toPure_3302_, lean_box(0), v_res_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3306_, lean_object* v_toBind_3307_, lean_object* v___f_3308_, lean_object* v_____r_3309_){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3311_ = lean_apply_2(v_inst_3306_, lean_box(0), v___x_3310_);
v___x_3312_ = lean_apply_4(v_toBind_3307_, lean_box(0), lean_box(0), v___x_3311_, v___f_3308_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3313_, lean_object* v_____r_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_apply_1(v___f_3313_, v_____r_3314_);
return v___x_3315_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3316_, lean_object* v_type_3317_, lean_object* v_type_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_cls_3323_, lean_object* v_toBind_3324_, lean_object* v___f_3325_, uint8_t v_____do__lift_3326_){
_start:
{
if (v_____do__lift_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec(v___f_3325_);
lean_dec(v_toBind_3324_);
lean_dec(v_cls_3323_);
lean_dec(v_inst_3322_);
lean_dec_ref(v_inst_3321_);
lean_dec_ref(v_inst_3320_);
lean_dec_ref(v_inst_3319_);
lean_dec_ref(v_type_3318_);
lean_dec_ref(v_type_3317_);
v___x_3327_ = lean_box(0);
v___x_3328_ = lean_apply_1(v___f_3316_, v___x_3327_);
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec(v___f_3316_);
v___x_3329_ = l_Lean_MessageData_ofExpr(v_type_3317_);
v___x_3330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = l_Lean_MessageData_ofExpr(v_type_3318_);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = l_Lean_addTrace___redArg(v_inst_3319_, v_inst_3320_, v_inst_3321_, v_inst_3322_, v_cls_3323_, v___x_3333_);
v___x_3335_ = lean_apply_4(v_toBind_3324_, lean_box(0), lean_box(0), v___x_3334_, v___f_3325_);
return v___x_3335_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3316_ = stack[0].m_obj;
lean_object* v_type_3317_ = stack[1].m_obj;
lean_object* v_type_3318_ = stack[2].m_obj;
lean_object* v_inst_3319_ = stack[3].m_obj;
lean_object* v_inst_3320_ = stack[4].m_obj;
lean_object* v_inst_3321_ = stack[5].m_obj;
lean_object* v_inst_3322_ = stack[6].m_obj;
lean_object* v_cls_3323_ = stack[7].m_obj;
lean_object* v_toBind_3324_ = stack[8].m_obj;
lean_object* v___f_3325_ = stack[9].m_obj;
uint8_t v_____do__lift_3326_ = stack[10].m_num;
lean_object* v_res_3336_;
v_res_3336_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3316_, v_type_3317_, v_type_3318_, v_inst_3319_, v_inst_3320_, v_inst_3321_, v_inst_3322_, v_cls_3323_, v_toBind_3324_, v___f_3325_, v_____do__lift_3326_);
stack->m_obj
 = v_res_3336_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3337_, lean_object* v_type_3338_, lean_object* v_type_3339_, lean_object* v_inst_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_inst_3343_, lean_object* v_cls_3344_, lean_object* v_toBind_3345_, lean_object* v___f_3346_, lean_object* v_____do__lift_3347_){
_start:
{
uint8_t v_____do__lift_3282__boxed_3348_; lean_object* v_res_3349_; 
v_____do__lift_3282__boxed_3348_ = lean_unbox(v_____do__lift_3347_);
v_res_3349_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3337_, v_type_3338_, v_type_3339_, v_inst_3340_, v_inst_3341_, v_inst_3342_, v_inst_3343_, v_cls_3344_, v_toBind_3345_, v___f_3346_, v_____do__lift_3282__boxed_3348_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3350_, lean_object* v_inst_3351_, lean_object* v_toBind_3352_, lean_object* v_inst_3353_, lean_object* v___f_3354_, lean_object* v_a_3355_, lean_object* v_inst_3356_, lean_object* v_inst_3357_, lean_object* v_inst_3358_, lean_object* v_inst_3359_, lean_object* v___f_3360_, lean_object* v_res_3361_){
_start:
{
lean_object* v___x_3362_; lean_object* v_zero_3363_; uint8_t v_isZero_3364_; 
v___x_3362_ = lean_array_get_size(v_res_3361_);
v_zero_3363_ = lean_unsigned_to_nat(0u);
v_isZero_3364_ = lean_nat_dec_eq(v___x_3362_, v_zero_3363_);
if (v_isZero_3364_ == 1)
{
lean_object* v___f_3365_; lean_object* v___f_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
lean_dec(v___f_3360_);
lean_dec(v_inst_3359_);
lean_dec_ref(v_inst_3358_);
lean_dec_ref(v_inst_3357_);
lean_dec_ref(v_inst_3356_);
lean_dec_ref(v_a_3355_);
lean_inc_ref(v_res_3361_);
lean_inc(v_toPure_3350_);
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3365_, 0, v_toPure_3350_);
lean_closure_set(v___f_3365_, 1, v_res_3361_);
lean_inc(v_toBind_3352_);
v___f_3366_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3366_, 0, v_inst_3351_);
lean_closure_set(v___f_3366_, 1, v_toBind_3352_);
lean_closure_set(v___f_3366_, 2, v___f_3365_);
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_nat_dec_lt(v_zero_3363_, v___x_3362_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec_ref(v_res_3361_);
lean_dec(v___f_3354_);
lean_dec_ref(v_inst_3353_);
v___x_3369_ = lean_apply_2(v_toPure_3350_, lean_box(0), v___x_3367_);
v___x_3370_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3369_, v___f_3366_);
return v___x_3370_;
}
else
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_nat_dec_le(v___x_3362_, v___x_3362_);
if (v___x_3371_ == 0)
{
if (v___x_3368_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
lean_dec_ref(v_res_3361_);
lean_dec(v___f_3354_);
lean_dec_ref(v_inst_3353_);
v___x_3372_ = lean_apply_2(v_toPure_3350_, lean_box(0), v___x_3367_);
v___x_3373_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3372_, v___f_3366_);
return v___x_3373_;
}
else
{
size_t v___x_3374_; size_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec(v_toPure_3350_);
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = lean_usize_of_nat(v___x_3362_);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3353_, v___f_3354_, v_res_3361_, v___x_3374_, v___x_3375_, v___x_3367_);
v___x_3377_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3376_, v___f_3366_);
return v___x_3377_;
}
}
else
{
size_t v___x_3378_; size_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec(v_toPure_3350_);
v___x_3378_ = ((size_t)0ULL);
v___x_3379_ = lean_usize_of_nat(v___x_3362_);
v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3353_, v___f_3354_, v_res_3361_, v___x_3378_, v___x_3379_, v___x_3367_);
v___x_3381_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3380_, v___f_3366_);
return v___x_3381_;
}
}
}
else
{
lean_object* v_one_3382_; lean_object* v_n_3383_; uint8_t v_isZero_3384_; 
lean_dec(v___f_3354_);
v_one_3382_ = lean_unsigned_to_nat(1u);
v_n_3383_ = lean_nat_sub(v___x_3362_, v_one_3382_);
v_isZero_3384_ = lean_nat_dec_eq(v_n_3383_, v_zero_3363_);
lean_dec(v_n_3383_);
if (v_isZero_3384_ == 1)
{
lean_object* v_newHyp_3385_; lean_object* v_type_3386_; lean_object* v_type_3387_; uint8_t v___x_3388_; 
lean_dec(v___f_3360_);
v_newHyp_3385_ = lean_array_fget_borrowed(v_res_3361_, v_zero_3363_);
v_type_3386_ = lean_ctor_get(v_newHyp_3385_, 1);
v_type_3387_ = lean_ctor_get(v_a_3355_, 1);
lean_inc_ref(v_type_3387_);
lean_dec_ref(v_a_3355_);
v___x_3388_ = lean_expr_eqv(v_type_3386_, v_type_3387_);
if (v___x_3388_ == 0)
{
lean_object* v_getInheritedTraceOptions_3389_; lean_object* v___f_3390_; lean_object* v___f_3391_; lean_object* v___f_3392_; lean_object* v_cls_3393_; lean_object* v___f_3394_; lean_object* v___f_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_inc_ref(v_type_3386_);
v_getInheritedTraceOptions_3389_ = lean_ctor_get(v_inst_3356_, 2);
lean_inc(v_getInheritedTraceOptions_3389_);
lean_inc(v_toPure_3350_);
v___f_3390_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3390_, 0, v_toPure_3350_);
lean_closure_set(v___f_3390_, 1, v_res_3361_);
lean_inc_n(v_toBind_3352_, 4);
v___f_3391_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3391_, 0, v_inst_3351_);
lean_closure_set(v___f_3391_, 1, v_toBind_3352_);
lean_closure_set(v___f_3391_, 2, v___f_3390_);
lean_inc_ref(v___f_3391_);
v___f_3392_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3392_, 0, v___f_3391_);
v_cls_3393_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3394_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3394_, 0, v_inst_3357_);
lean_closure_set(v___f_3394_, 1, v_toPure_3350_);
lean_closure_set(v___f_3394_, 2, v_cls_3393_);
lean_closure_set(v___f_3394_, 3, v_toBind_3352_);
v___f_3395_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3395_, 0, v___f_3391_);
lean_closure_set(v___f_3395_, 1, v_type_3387_);
lean_closure_set(v___f_3395_, 2, v_type_3386_);
lean_closure_set(v___f_3395_, 3, v_inst_3353_);
lean_closure_set(v___f_3395_, 4, v_inst_3356_);
lean_closure_set(v___f_3395_, 5, v_inst_3358_);
lean_closure_set(v___f_3395_, 6, v_inst_3359_);
lean_closure_set(v___f_3395_, 7, v_cls_3393_);
lean_closure_set(v___f_3395_, 8, v_toBind_3352_);
lean_closure_set(v___f_3395_, 9, v___f_3392_);
v___x_3396_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3389_, v___f_3394_);
v___x_3397_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3396_, v___f_3395_);
return v___x_3397_;
}
else
{
lean_object* v___x_3398_; 
lean_dec_ref(v_type_3387_);
lean_dec(v_inst_3359_);
lean_dec_ref(v_inst_3358_);
lean_dec_ref(v_inst_3357_);
lean_dec_ref(v_inst_3356_);
lean_dec_ref(v_inst_3353_);
lean_dec(v_toBind_3352_);
lean_dec(v_inst_3351_);
v___x_3398_ = lean_apply_2(v_toPure_3350_, lean_box(0), v_res_3361_);
return v___x_3398_;
}
}
else
{
lean_object* v___f_3399_; lean_object* v___f_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
lean_dec(v_inst_3359_);
lean_dec_ref(v_inst_3358_);
lean_dec_ref(v_inst_3357_);
lean_dec_ref(v_inst_3356_);
lean_dec_ref(v_a_3355_);
lean_inc_ref(v_res_3361_);
lean_inc(v_toPure_3350_);
v___f_3399_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3399_, 0, v_toPure_3350_);
lean_closure_set(v___f_3399_, 1, v_res_3361_);
lean_inc(v_toBind_3352_);
v___f_3400_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3400_, 0, v_inst_3351_);
lean_closure_set(v___f_3400_, 1, v_toBind_3352_);
lean_closure_set(v___f_3400_, 2, v___f_3399_);
v___x_3401_ = lean_box(0);
v___x_3402_ = lean_nat_dec_lt(v_zero_3363_, v___x_3362_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec_ref(v_res_3361_);
lean_dec(v___f_3360_);
lean_dec_ref(v_inst_3353_);
v___x_3403_ = lean_apply_2(v_toPure_3350_, lean_box(0), v___x_3401_);
v___x_3404_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3403_, v___f_3400_);
return v___x_3404_;
}
else
{
uint8_t v___x_3405_; 
v___x_3405_ = lean_nat_dec_le(v___x_3362_, v___x_3362_);
if (v___x_3405_ == 0)
{
if (v___x_3402_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
lean_dec_ref(v_res_3361_);
lean_dec(v___f_3360_);
lean_dec_ref(v_inst_3353_);
v___x_3406_ = lean_apply_2(v_toPure_3350_, lean_box(0), v___x_3401_);
v___x_3407_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3406_, v___f_3400_);
return v___x_3407_;
}
else
{
size_t v___x_3408_; size_t v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_dec(v_toPure_3350_);
v___x_3408_ = ((size_t)0ULL);
v___x_3409_ = lean_usize_of_nat(v___x_3362_);
v___x_3410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3353_, v___f_3360_, v_res_3361_, v___x_3408_, v___x_3409_, v___x_3401_);
v___x_3411_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3410_, v___f_3400_);
return v___x_3411_;
}
}
else
{
size_t v___x_3412_; size_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v_toPure_3350_);
v___x_3412_ = ((size_t)0ULL);
v___x_3413_ = lean_usize_of_nat(v___x_3362_);
v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3353_, v___f_3360_, v_res_3361_, v___x_3412_, v___x_3413_, v___x_3401_);
v___x_3415_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3414_, v___f_3400_);
return v___x_3415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3416_, lean_object* v_toPure_3417_, lean_object* v_____do__lift_3418_){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = l_Array_append___redArg(v_bs_3416_, v_____do__lift_3418_);
v___x_3420_ = lean_apply_2(v_toPure_3417_, lean_box(0), v___x_3419_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3421_, lean_object* v_toPure_3422_, lean_object* v_____do__lift_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3421_, v_toPure_3422_, v_____do__lift_3423_);
lean_dec_ref(v_____do__lift_3423_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3425_, lean_object* v_inst_3426_, lean_object* v_toPure_3427_, lean_object* v_toBind_3428_, lean_object* v_inst_3429_, lean_object* v_inst_3430_, lean_object* v_inst_3431_, lean_object* v_inst_3432_, lean_object* v_f_3433_, lean_object* v_bs_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v___f_3436_; lean_object* v___f_3437_; lean_object* v___f_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_inc(v_inst_3431_);
lean_inc_ref(v_inst_3430_);
lean_inc_ref(v_inst_3429_);
lean_inc_ref_n(v_a_3435_, 2);
lean_inc_n(v_toBind_3428_, 3);
lean_inc_n(v_toPure_3427_, 2);
lean_inc_ref(v_inst_3426_);
lean_inc_ref(v_inst_3425_);
v___f_3436_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3436_, 0, v_inst_3425_);
lean_closure_set(v___f_3436_, 1, v_inst_3426_);
lean_closure_set(v___f_3436_, 2, v_toPure_3427_);
lean_closure_set(v___f_3436_, 3, v_toBind_3428_);
lean_closure_set(v___f_3436_, 4, v_a_3435_);
lean_closure_set(v___f_3436_, 5, v_inst_3429_);
lean_closure_set(v___f_3436_, 6, v_inst_3430_);
lean_closure_set(v___f_3436_, 7, v_inst_3431_);
lean_inc_ref(v___f_3436_);
v___f_3437_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3437_, 0, v_toPure_3427_);
lean_closure_set(v___f_3437_, 1, v_inst_3432_);
lean_closure_set(v___f_3437_, 2, v_toBind_3428_);
lean_closure_set(v___f_3437_, 3, v_inst_3429_);
lean_closure_set(v___f_3437_, 4, v___f_3436_);
lean_closure_set(v___f_3437_, 5, v_a_3435_);
lean_closure_set(v___f_3437_, 6, v_inst_3425_);
lean_closure_set(v___f_3437_, 7, v_inst_3426_);
lean_closure_set(v___f_3437_, 8, v_inst_3430_);
lean_closure_set(v___f_3437_, 9, v_inst_3431_);
lean_closure_set(v___f_3437_, 10, v___f_3436_);
v___f_3438_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3438_, 0, v_bs_3434_);
lean_closure_set(v___f_3438_, 1, v_toPure_3427_);
v___x_3439_ = lean_apply_1(v_f_3433_, v_a_3435_);
v___x_3440_ = lean_apply_4(v_toBind_3428_, lean_box(0), lean_box(0), v___x_3439_, v___f_3437_);
v___x_3441_ = lean_apply_4(v_toBind_3428_, lean_box(0), lean_box(0), v___x_3440_, v___f_3438_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3444_, lean_object* v_toPure_3445_, lean_object* v_toBind_3446_, lean_object* v___f_3447_, lean_object* v_inst_3448_, lean_object* v___f_3449_, lean_object* v_____r_3450_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3453_ = lean_array_get_size(v_hyps_3444_);
v___x_3454_ = lean_nat_dec_lt(v___x_3451_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_dec(v___f_3449_);
lean_dec_ref(v_inst_3448_);
lean_dec_ref(v_hyps_3444_);
v___x_3455_ = lean_apply_2(v_toPure_3445_, lean_box(0), v___x_3452_);
v___x_3456_ = lean_apply_4(v_toBind_3446_, lean_box(0), lean_box(0), v___x_3455_, v___f_3447_);
return v___x_3456_;
}
else
{
size_t v___x_3457_; size_t v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_dec(v_toPure_3445_);
v___x_3457_ = ((size_t)0ULL);
v___x_3458_ = lean_usize_of_nat(v___x_3453_);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3448_, v___f_3449_, v_hyps_3444_, v___x_3457_, v___x_3458_, v___x_3452_);
v___x_3460_ = lean_apply_4(v_toBind_3446_, lean_box(0), lean_box(0), v___x_3459_, v___f_3447_);
return v___x_3460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3461_, lean_object* v_toBind_3462_, lean_object* v___f_3463_, lean_object* v_inst_3464_, lean_object* v___f_3465_, lean_object* v_inst_3466_, lean_object* v___f_3467_, lean_object* v_hyps_3468_){
_start:
{
lean_object* v___f_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_inc(v_toBind_3462_);
v___f_3469_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3469_, 0, v_hyps_3468_);
lean_closure_set(v___f_3469_, 1, v_toPure_3461_);
lean_closure_set(v___f_3469_, 2, v_toBind_3462_);
lean_closure_set(v___f_3469_, 3, v___f_3463_);
lean_closure_set(v___f_3469_, 4, v_inst_3464_);
lean_closure_set(v___f_3469_, 5, v___f_3465_);
v___x_3470_ = lean_apply_2(v_inst_3466_, lean_box(0), v___f_3467_);
v___x_3471_ = lean_apply_4(v_toBind_3462_, lean_box(0), lean_box(0), v___x_3470_, v___f_3469_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3473_, lean_object* v_inst_3474_, lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_f_3479_){
_start:
{
lean_object* v_toApplicative_3480_; lean_object* v_toBind_3481_; lean_object* v_toPure_3482_; lean_object* v___f_3483_; lean_object* v___f_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___f_3487_; lean_object* v___f_3488_; lean_object* v___x_3489_; 
v_toApplicative_3480_ = lean_ctor_get(v_inst_3473_, 0);
v_toBind_3481_ = lean_ctor_get(v_inst_3473_, 1);
lean_inc_n(v_toBind_3481_, 3);
v_toPure_3482_ = lean_ctor_get(v_toApplicative_3480_, 1);
lean_inc_n(v_toPure_3482_, 2);
lean_inc_n(v_inst_3478_, 3);
v___f_3483_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3483_, 0, v_inst_3478_);
v___f_3484_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3485_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3486_ = lean_apply_2(v_inst_3478_, lean_box(0), v___x_3485_);
lean_inc_ref(v_inst_3473_);
v___f_3487_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3487_, 0, v_inst_3474_);
lean_closure_set(v___f_3487_, 1, v_inst_3475_);
lean_closure_set(v___f_3487_, 2, v_toPure_3482_);
lean_closure_set(v___f_3487_, 3, v_toBind_3481_);
lean_closure_set(v___f_3487_, 4, v_inst_3473_);
lean_closure_set(v___f_3487_, 5, v_inst_3477_);
lean_closure_set(v___f_3487_, 6, v_inst_3476_);
lean_closure_set(v___f_3487_, 7, v_inst_3478_);
lean_closure_set(v___f_3487_, 8, v_f_3479_);
v___f_3488_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3488_, 0, v_toPure_3482_);
lean_closure_set(v___f_3488_, 1, v_toBind_3481_);
lean_closure_set(v___f_3488_, 2, v___f_3483_);
lean_closure_set(v___f_3488_, 3, v_inst_3473_);
lean_closure_set(v___f_3488_, 4, v___f_3487_);
lean_closure_set(v___f_3488_, 5, v_inst_3478_);
lean_closure_set(v___f_3488_, 6, v___f_3484_);
v___x_3489_ = lean_apply_4(v_toBind_3481_, lean_box(0), lean_box(0), v___x_3486_, v___f_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3490_, lean_object* v_inst_3491_, lean_object* v_inst_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_f_3497_){
_start:
{
lean_object* v_toApplicative_3498_; lean_object* v_toBind_3499_; lean_object* v_toPure_3500_; lean_object* v___f_3501_; lean_object* v___f_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___f_3505_; lean_object* v___f_3506_; lean_object* v___x_3507_; 
v_toApplicative_3498_ = lean_ctor_get(v_inst_3491_, 0);
v_toBind_3499_ = lean_ctor_get(v_inst_3491_, 1);
lean_inc_n(v_toBind_3499_, 3);
v_toPure_3500_ = lean_ctor_get(v_toApplicative_3498_, 1);
lean_inc_n(v_toPure_3500_, 2);
lean_inc_n(v_inst_3496_, 3);
v___f_3501_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3501_, 0, v_inst_3496_);
v___f_3502_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3503_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3504_ = lean_apply_2(v_inst_3496_, lean_box(0), v___x_3503_);
lean_inc_ref(v_inst_3491_);
v___f_3505_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3505_, 0, v_inst_3492_);
lean_closure_set(v___f_3505_, 1, v_inst_3493_);
lean_closure_set(v___f_3505_, 2, v_toPure_3500_);
lean_closure_set(v___f_3505_, 3, v_toBind_3499_);
lean_closure_set(v___f_3505_, 4, v_inst_3491_);
lean_closure_set(v___f_3505_, 5, v_inst_3495_);
lean_closure_set(v___f_3505_, 6, v_inst_3494_);
lean_closure_set(v___f_3505_, 7, v_inst_3496_);
lean_closure_set(v___f_3505_, 8, v_f_3497_);
v___f_3506_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3506_, 0, v_toPure_3500_);
lean_closure_set(v___f_3506_, 1, v_toBind_3499_);
lean_closure_set(v___f_3506_, 2, v___f_3501_);
lean_closure_set(v___f_3506_, 3, v_inst_3491_);
lean_closure_set(v___f_3506_, 4, v___f_3505_);
lean_closure_set(v___f_3506_, 5, v_inst_3496_);
lean_closure_set(v___f_3506_, 6, v___f_3502_);
v___x_3507_ = lean_apply_4(v_toBind_3499_, lean_box(0), lean_box(0), v___x_3504_, v___f_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3508_, lean_object* v_____r_3509_){
_start:
{
uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = 0;
v___x_3511_ = lean_box(v___x_3510_);
v___x_3512_ = lean_apply_2(v_toPure_3508_, lean_box(0), v___x_3511_);
return v___x_3512_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_snd_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; lean_object* v_caches_3527_; lean_object* v_typeAnalysis_3528_; lean_object* v_target_3529_; uint8_t v_didChange_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3540_; 
v___x_3526_ = lean_st_ref_take(v___y_3515_);
v_caches_3527_ = lean_ctor_get(v___x_3526_, 0);
v_typeAnalysis_3528_ = lean_ctor_get(v___x_3526_, 1);
v_target_3529_ = lean_ctor_get(v___x_3526_, 2);
v_didChange_3530_ = lean_ctor_get_uint8(v___x_3526_, sizeof(void*)*4);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3540_ == 0)
{
lean_object* v_unused_3541_; 
v_unused_3541_ = lean_ctor_get(v___x_3526_, 3);
lean_dec(v_unused_3541_);
v___x_3532_ = v___x_3526_;
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_target_3529_);
lean_inc(v_typeAnalysis_3528_);
lean_inc(v_caches_3527_);
lean_dec(v___x_3526_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3534_ = lean_box(0);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 3, v_snd_3513_);
v___x_3536_ = v___x_3532_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_caches_3527_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_typeAnalysis_3528_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_target_3529_);
lean_ctor_set(v_reuseFailAlloc_3539_, 3, v_snd_3513_);
lean_ctor_set_uint8(v_reuseFailAlloc_3539_, sizeof(void*)*4, v_didChange_3530_);
v___x_3536_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = lean_st_ref_put(v___y_3515_, v___x_3536_);
v___x_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3534_);
return v___x_3538_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_3513_ = stack[0].m_obj;
lean_object* v___y_3514_ = stack[1].m_obj;
lean_object* v___y_3515_ = stack[2].m_obj;
lean_object* v___y_3516_ = stack[3].m_obj;
lean_object* v___y_3517_ = stack[4].m_obj;
lean_object* v___y_3518_ = stack[5].m_obj;
lean_object* v___y_3519_ = stack[6].m_obj;
lean_object* v___y_3520_ = stack[7].m_obj;
lean_object* v___y_3521_ = stack[8].m_obj;
lean_object* v___y_3522_ = stack[9].m_obj;
lean_object* v___y_3523_ = stack[10].m_obj;
lean_object* v___y_3524_ = stack[11].m_obj;
lean_object* v_res_3542_;
v_res_3542_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(v_snd_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
stack->m_obj
 = v_res_3542_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed(lean_object* v_snd_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(v_snd_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_inst_3557_, lean_object* v_toBind_3558_, lean_object* v___f_3559_, lean_object* v_toPure_3560_, lean_object* v_____s_3561_){
_start:
{
lean_object* v_fst_3562_; 
v_fst_3562_ = lean_ctor_get(v_____s_3561_, 0);
if (lean_obj_tag(v_fst_3562_) == 0)
{
lean_object* v_snd_3563_; lean_object* v___f_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec(v_toPure_3560_);
v_snd_3563_ = lean_ctor_get(v_____s_3561_, 1);
lean_inc(v_snd_3563_);
lean_dec_ref(v_____s_3561_);
v___f_3564_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_3564_, 0, v_snd_3563_);
v___x_3565_ = lean_apply_2(v_inst_3557_, lean_box(0), v___f_3564_);
v___x_3566_ = lean_apply_4(v_toBind_3558_, lean_box(0), lean_box(0), v___x_3565_, v___f_3559_);
return v___x_3566_;
}
else
{
lean_object* v_val_3567_; lean_object* v___x_3568_; 
lean_inc_ref(v_fst_3562_);
lean_dec_ref(v_____s_3561_);
lean_dec(v___f_3559_);
lean_dec(v_toBind_3558_);
lean_dec(v_inst_3557_);
v_val_3567_ = lean_ctor_get(v_fst_3562_, 0);
lean_inc(v_val_3567_);
lean_dec_ref_known(v_fst_3562_, 1);
v___x_3568_ = lean_apply_2(v_toPure_3560_, lean_box(0), v_val_3567_);
return v___x_3568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_toPure_3569_, lean_object* v_____do__lift_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_apply_2(v_toPure_3569_, lean_box(0), v_____do__lift_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3572_, lean_object* v_next_3573_, lean_object* v_G_3574_, lean_object* v_____do__lift_3575_){
_start:
{
if (lean_obj_tag(v_____do__lift_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3577_; 
lean_dec(v_G_3574_);
v_a_3576_ = lean_ctor_get(v_____do__lift_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v_____do__lift_3575_, 1);
v___x_3577_ = lean_apply_2(v_toPure_3572_, lean_box(0), v_a_3576_);
return v___x_3577_;
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec(v_toPure_3572_);
v_a_3578_ = lean_ctor_get(v_____do__lift_3575_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v_____do__lift_3575_, 1);
v___x_3579_ = lean_unsigned_to_nat(1u);
v___x_3580_ = lean_nat_add(v_next_3573_, v___x_3579_);
v___x_3581_ = lean_apply_4(v_G_3574_, v___x_3580_, v_a_3578_, lean_box(0), lean_box(0));
return v___x_3581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3582_, lean_object* v_next_3583_, lean_object* v_G_3584_, lean_object* v_____do__lift_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3582_, v_next_3583_, v_G_3584_, v_____do__lift_3585_);
lean_dec(v_next_3583_);
return v_res_3586_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(uint8_t v___x_3587_, lean_object* v_snd_3588_, lean_object* v_toPure_3589_, lean_object* v_____r_3590_){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3591_ = lean_box(v___x_3587_);
v___x_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v_snd_3588_);
v___x_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
v___x_3595_ = lean_apply_2(v_toPure_3589_, lean_box(0), v___x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3587_ = stack[0].m_num;
lean_object* v_snd_3588_ = stack[1].m_obj;
lean_object* v_toPure_3589_ = stack[2].m_obj;
lean_object* v_____r_3590_ = stack[3].m_obj;
lean_object* v_res_3596_;
v_res_3596_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_3587_, v_snd_3588_, v_toPure_3589_, v_____r_3590_);
stack->m_obj
 = v_res_3596_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed(lean_object* v___x_3597_, lean_object* v_snd_3598_, lean_object* v_toPure_3599_, lean_object* v_____r_3600_){
_start:
{
uint8_t v___x_1733__boxed_3601_; lean_object* v_res_3602_; 
v___x_1733__boxed_3601_ = lean_unbox(v___x_3597_);
v_res_3602_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_1733__boxed_3601_, v_snd_3598_, v_toPure_3599_, v_____r_3600_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_snd_3603_, lean_object* v_newHyp_3604_, lean_object* v___x_3605_, lean_object* v_toPure_3606_, lean_object* v_____r_3607_){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3608_ = lean_array_push(v_snd_3603_, v_newHyp_3604_);
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3605_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
v___x_3611_ = lean_apply_2(v_toPure_3606_, lean_box(0), v___x_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_toPure_3612_, lean_object* v___x_3613_, lean_object* v_____do__lift_3614_, lean_object* v_____do__lift_3615_){
_start:
{
uint8_t v_hasTrace_3616_; 
v_hasTrace_3616_ = lean_ctor_get_uint8(v_____do__lift_3615_, sizeof(void*)*1);
if (v_hasTrace_3616_ == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_dec(v___x_3613_);
v___x_3617_ = lean_box(v_hasTrace_3616_);
v___x_3618_ = lean_apply_2(v_toPure_3612_, lean_box(0), v___x_3617_);
return v___x_3618_;
}
else
{
lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3619_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3620_ = l_Lean_Name_append(v___x_3619_, v___x_3613_);
v___x_3621_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3614_, v_____do__lift_3615_, v___x_3620_);
lean_dec(v___x_3620_);
v___x_3622_ = lean_box(v___x_3621_);
v___x_3623_ = lean_apply_2(v_toPure_3612_, lean_box(0), v___x_3622_);
return v___x_3623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed(lean_object* v_toPure_3624_, lean_object* v___x_3625_, lean_object* v_____do__lift_3626_, lean_object* v_____do__lift_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(v_toPure_3624_, v___x_3625_, v_____do__lift_3626_, v_____do__lift_3627_);
lean_dec_ref(v_____do__lift_3627_);
lean_dec_ref(v_____do__lift_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v_inst_3629_, lean_object* v_toPure_3630_, lean_object* v___x_3631_, lean_object* v_toBind_3632_, lean_object* v_____do__lift_3633_){
_start:
{
lean_object* v_getOptionsUnrestricted_3634_; lean_object* v___f_3635_; lean_object* v___x_3636_; 
v_getOptionsUnrestricted_3634_ = lean_ctor_get(v_inst_3629_, 1);
lean_inc(v_getOptionsUnrestricted_3634_);
lean_dec_ref(v_inst_3629_);
v___f_3635_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_3635_, 0, v_toPure_3630_);
lean_closure_set(v___f_3635_, 1, v___x_3631_);
lean_closure_set(v___f_3635_, 2, v_____do__lift_3633_);
v___x_3636_ = lean_apply_4(v_toBind_3632_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3634_, v___f_3635_);
return v___x_3636_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object* v___f_3637_, lean_object* v___x_3638_, lean_object* v_type_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_toMonadRef_3642_, lean_object* v_inst_3643_, lean_object* v___x_3644_, lean_object* v_toBind_3645_, lean_object* v___f_3646_, uint8_t v_____do__lift_3647_){
_start:
{
if (v_____do__lift_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_dec(v___f_3646_);
lean_dec(v_toBind_3645_);
lean_dec(v___x_3644_);
lean_dec(v_inst_3643_);
lean_dec_ref(v_toMonadRef_3642_);
lean_dec_ref(v_inst_3641_);
lean_dec_ref(v_inst_3640_);
lean_dec_ref(v_type_3639_);
lean_dec_ref(v___x_3638_);
v___x_3648_ = lean_box(0);
v___x_3649_ = lean_apply_1(v___f_3637_, v___x_3648_);
return v___x_3649_;
}
else
{
lean_object* v_type_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_dec(v___f_3637_);
v_type_3650_ = lean_ctor_get(v___x_3638_, 1);
lean_inc_ref(v_type_3650_);
lean_dec_ref(v___x_3638_);
v___x_3651_ = l_Lean_MessageData_ofExpr(v_type_3650_);
v___x_3652_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = l_Lean_MessageData_ofExpr(v_type_3639_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = l_Lean_addTrace___redArg(v_inst_3640_, v_inst_3641_, v_toMonadRef_3642_, v_inst_3643_, v___x_3644_, v___x_3655_);
v___x_3657_ = lean_apply_4(v_toBind_3645_, lean_box(0), lean_box(0), v___x_3656_, v___f_3646_);
return v___x_3657_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3637_ = stack[0].m_obj;
lean_object* v___x_3638_ = stack[1].m_obj;
lean_object* v_type_3639_ = stack[2].m_obj;
lean_object* v_inst_3640_ = stack[3].m_obj;
lean_object* v_inst_3641_ = stack[4].m_obj;
lean_object* v_toMonadRef_3642_ = stack[5].m_obj;
lean_object* v_inst_3643_ = stack[6].m_obj;
lean_object* v___x_3644_ = stack[7].m_obj;
lean_object* v_toBind_3645_ = stack[8].m_obj;
lean_object* v___f_3646_ = stack[9].m_obj;
uint8_t v_____do__lift_3647_ = stack[10].m_num;
lean_object* v_res_3658_;
v_res_3658_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3637_, v___x_3638_, v_type_3639_, v_inst_3640_, v_inst_3641_, v_toMonadRef_3642_, v_inst_3643_, v___x_3644_, v_toBind_3645_, v___f_3646_, v_____do__lift_3647_);
stack->m_obj
 = v_res_3658_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___f_3659_, lean_object* v___x_3660_, lean_object* v_type_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_toMonadRef_3664_, lean_object* v_inst_3665_, lean_object* v___x_3666_, lean_object* v_toBind_3667_, lean_object* v___f_3668_, lean_object* v_____do__lift_3669_){
_start:
{
uint8_t v_____do__lift_1841__boxed_3670_; lean_object* v_res_3671_; 
v_____do__lift_1841__boxed_3670_ = lean_unbox(v_____do__lift_3669_);
v_res_3671_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3659_, v___x_3660_, v_type_3661_, v_inst_3662_, v_inst_3663_, v_toMonadRef_3664_, v_inst_3665_, v___x_3666_, v_toBind_3667_, v___f_3668_, v_____do__lift_1841__boxed_3670_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v___x_3672_, lean_object* v_snd_3673_, lean_object* v___x_3674_, lean_object* v_toPure_3675_, lean_object* v_inst_3676_, lean_object* v_toBind_3677_, lean_object* v_inst_3678_, lean_object* v_inst_3679_, lean_object* v_inst_3680_, lean_object* v_toMonadRef_3681_, lean_object* v_inst_3682_, lean_object* v___f_3683_, lean_object* v_newHyp_3684_){
_start:
{
lean_object* v_type_3685_; lean_object* v_value_3686_; uint8_t v___x_3687_; 
v_type_3685_ = lean_ctor_get(v_newHyp_3684_, 1);
v_value_3686_ = lean_ctor_get(v_newHyp_3684_, 2);
lean_inc_ref(v_type_3685_);
v___x_3687_ = l_Lean_Expr_isFalse(v_type_3685_);
if (v___x_3687_ == 0)
{
lean_object* v_type_3688_; lean_object* v___f_3689_; lean_object* v___f_3690_; lean_object* v___f_3691_; lean_object* v___f_3692_; uint8_t v___x_3700_; 
lean_dec(v___f_3683_);
v_type_3688_ = lean_ctor_get(v___x_3672_, 1);
lean_inc(v_toPure_3675_);
lean_inc(v___x_3674_);
lean_inc_ref(v_newHyp_3684_);
lean_inc(v_snd_3673_);
v___f_3689_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3689_, 0, v_snd_3673_);
lean_closure_set(v___f_3689_, 1, v_newHyp_3684_);
lean_closure_set(v___f_3689_, 2, v___x_3674_);
lean_closure_set(v___f_3689_, 3, v_toPure_3675_);
v___f_3690_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3690_, 0, v___f_3689_);
lean_inc(v_toBind_3677_);
v___f_3691_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3691_, 0, v_inst_3676_);
lean_closure_set(v___f_3691_, 1, v_toBind_3677_);
lean_closure_set(v___f_3691_, 2, v___f_3690_);
lean_inc_ref(v___f_3691_);
v___f_3692_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3692_, 0, v___f_3691_);
v___x_3700_ = lean_expr_eqv(v_type_3688_, v_type_3685_);
if (v___x_3700_ == 0)
{
lean_inc_ref(v_type_3685_);
lean_dec_ref(v_newHyp_3684_);
lean_dec(v___x_3674_);
lean_dec(v_snd_3673_);
goto v___jp_3693_;
}
else
{
if (v___x_3687_ == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_dec_ref(v___f_3692_);
lean_dec_ref(v___f_3691_);
lean_dec(v_inst_3682_);
lean_dec_ref(v_toMonadRef_3681_);
lean_dec_ref(v_inst_3680_);
lean_dec_ref(v_inst_3679_);
lean_dec_ref(v_inst_3678_);
lean_dec(v_toBind_3677_);
lean_dec_ref(v___x_3672_);
v___x_3701_ = lean_box(0);
v___x_3702_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3673_, v_newHyp_3684_, v___x_3674_, v_toPure_3675_, v___x_3701_);
return v___x_3702_;
}
else
{
lean_inc_ref(v_type_3685_);
lean_dec_ref(v_newHyp_3684_);
lean_dec(v___x_3674_);
lean_dec(v_snd_3673_);
goto v___jp_3693_;
}
}
v___jp_3693_:
{
lean_object* v_getInheritedTraceOptions_3694_; lean_object* v___x_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v_getInheritedTraceOptions_3694_ = lean_ctor_get(v_inst_3678_, 2);
lean_inc(v_getInheritedTraceOptions_3694_);
v___x_3695_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3677_, 3);
v___f_3696_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3696_, 0, v_inst_3679_);
lean_closure_set(v___f_3696_, 1, v_toPure_3675_);
lean_closure_set(v___f_3696_, 2, v___x_3695_);
lean_closure_set(v___f_3696_, 3, v_toBind_3677_);
v___f_3697_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3697_, 0, v___f_3691_);
lean_closure_set(v___f_3697_, 1, v___x_3672_);
lean_closure_set(v___f_3697_, 2, v_type_3685_);
lean_closure_set(v___f_3697_, 3, v_inst_3680_);
lean_closure_set(v___f_3697_, 4, v_inst_3678_);
lean_closure_set(v___f_3697_, 5, v_toMonadRef_3681_);
lean_closure_set(v___f_3697_, 6, v_inst_3682_);
lean_closure_set(v___f_3697_, 7, v___x_3695_);
lean_closure_set(v___f_3697_, 8, v_toBind_3677_);
lean_closure_set(v___f_3697_, 9, v___f_3692_);
v___x_3698_ = lean_apply_4(v_toBind_3677_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3694_, v___f_3696_);
v___x_3699_ = lean_apply_4(v_toBind_3677_, lean_box(0), lean_box(0), v___x_3698_, v___f_3697_);
return v___x_3699_;
}
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
lean_inc_ref(v_value_3686_);
lean_dec_ref(v_newHyp_3684_);
lean_dec(v_inst_3682_);
lean_dec_ref(v_toMonadRef_3681_);
lean_dec_ref(v_inst_3680_);
lean_dec_ref(v_inst_3679_);
lean_dec_ref(v_inst_3678_);
lean_dec(v_toPure_3675_);
lean_dec(v___x_3674_);
lean_dec(v_snd_3673_);
lean_dec_ref(v___x_3672_);
v___x_3703_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3703_, 0, v_value_3686_);
v___x_3704_ = lean_apply_2(v_inst_3676_, lean_box(0), v___x_3703_);
v___x_3705_ = lean_apply_4(v_toBind_3677_, lean_box(0), lean_box(0), v___x_3704_, v___f_3683_);
return v___x_3705_;
}
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3706_, lean_object* v_toPure_3707_, lean_object* v_hyps_3708_, lean_object* v___x_3709_, lean_object* v_inst_3710_, lean_object* v_toBind_3711_, lean_object* v_inst_3712_, lean_object* v_inst_3713_, lean_object* v_inst_3714_, lean_object* v_toMonadRef_3715_, lean_object* v_inst_3716_, lean_object* v_f_3717_, lean_object* v___f_3718_, lean_object* v_next_3719_, lean_object* v_acc_3720_, lean_object* v_h_3721_, lean_object* v_G_3722_){
_start:
{
uint8_t v___x_3723_; 
v___x_3723_ = lean_nat_dec_lt(v_next_3719_, v___x_3706_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; 
lean_dec(v_G_3722_);
lean_dec(v_next_3719_);
lean_dec(v___f_3718_);
lean_dec(v_f_3717_);
lean_dec(v_inst_3716_);
lean_dec_ref(v_toMonadRef_3715_);
lean_dec_ref(v_inst_3714_);
lean_dec_ref(v_inst_3713_);
lean_dec_ref(v_inst_3712_);
lean_dec(v_toBind_3711_);
lean_dec(v_inst_3710_);
lean_dec(v___x_3709_);
v___x_3724_ = lean_apply_2(v_toPure_3707_, lean_box(0), v_acc_3720_);
return v___x_3724_;
}
else
{
lean_object* v_snd_3725_; lean_object* v___f_3726_; lean_object* v___x_3727_; lean_object* v___f_3728_; lean_object* v___x_3729_; lean_object* v___f_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_snd_3725_ = lean_ctor_get(v_acc_3720_, 1);
lean_inc_n(v_snd_3725_, 2);
lean_dec_ref(v_acc_3720_);
lean_inc(v_next_3719_);
lean_inc_n(v_toPure_3707_, 2);
v___f_3726_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3726_, 0, v_toPure_3707_);
lean_closure_set(v___f_3726_, 1, v_next_3719_);
lean_closure_set(v___f_3726_, 2, v_G_3722_);
v___x_3727_ = lean_box(v___x_3723_);
v___f_3728_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3728_, 0, v___x_3727_);
lean_closure_set(v___f_3728_, 1, v_snd_3725_);
lean_closure_set(v___f_3728_, 2, v_toPure_3707_);
v___x_3729_ = lean_array_fget_borrowed(v_hyps_3708_, v_next_3719_);
lean_inc_n(v_toBind_3711_, 3);
lean_inc_n(v___x_3729_, 2);
v___f_3730_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9), 13, 12);
lean_closure_set(v___f_3730_, 0, v___x_3729_);
lean_closure_set(v___f_3730_, 1, v_snd_3725_);
lean_closure_set(v___f_3730_, 2, v___x_3709_);
lean_closure_set(v___f_3730_, 3, v_toPure_3707_);
lean_closure_set(v___f_3730_, 4, v_inst_3710_);
lean_closure_set(v___f_3730_, 5, v_toBind_3711_);
lean_closure_set(v___f_3730_, 6, v_inst_3712_);
lean_closure_set(v___f_3730_, 7, v_inst_3713_);
lean_closure_set(v___f_3730_, 8, v_inst_3714_);
lean_closure_set(v___f_3730_, 9, v_toMonadRef_3715_);
lean_closure_set(v___f_3730_, 10, v_inst_3716_);
lean_closure_set(v___f_3730_, 11, v___f_3728_);
v___x_3731_ = lean_apply_2(v_f_3717_, v_next_3719_, v___x_3729_);
v___x_3732_ = lean_apply_4(v_toBind_3711_, lean_box(0), lean_box(0), v___x_3731_, v___f_3730_);
v___x_3733_ = lean_apply_4(v_toBind_3711_, lean_box(0), lean_box(0), v___x_3732_, v___f_3718_);
v___x_3734_ = lean_apply_4(v_toBind_3711_, lean_box(0), lean_box(0), v___x_3733_, v___f_3726_);
return v___x_3734_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3706_ = stack[0].m_obj;
lean_object* v_toPure_3707_ = stack[1].m_obj;
lean_object* v_hyps_3708_ = stack[2].m_obj;
lean_object* v___x_3709_ = stack[3].m_obj;
lean_object* v_inst_3710_ = stack[4].m_obj;
lean_object* v_toBind_3711_ = stack[5].m_obj;
lean_object* v_inst_3712_ = stack[6].m_obj;
lean_object* v_inst_3713_ = stack[7].m_obj;
lean_object* v_inst_3714_ = stack[8].m_obj;
lean_object* v_toMonadRef_3715_ = stack[9].m_obj;
lean_object* v_inst_3716_ = stack[10].m_obj;
lean_object* v_f_3717_ = stack[11].m_obj;
lean_object* v___f_3718_ = stack[12].m_obj;
lean_object* v_next_3719_ = stack[13].m_obj;
lean_object* v_acc_3720_ = stack[14].m_obj;
lean_object* v_G_3722_ = stack[16].m_obj;
lean_object* v_res_3735_;
v_res_3735_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3706_, v_toPure_3707_, v_hyps_3708_, v___x_3709_, v_inst_3710_, v_toBind_3711_, v_inst_3712_, v_inst_3713_, v_inst_3714_, v_toMonadRef_3715_, v_inst_3716_, v_f_3717_, v___f_3718_, v_next_3719_, v_acc_3720_, lean_box(0), v_G_3722_);
stack->m_obj
 = v_res_3735_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3736_ = _args[0];
lean_object* v_toPure_3737_ = _args[1];
lean_object* v_hyps_3738_ = _args[2];
lean_object* v___x_3739_ = _args[3];
lean_object* v_inst_3740_ = _args[4];
lean_object* v_toBind_3741_ = _args[5];
lean_object* v_inst_3742_ = _args[6];
lean_object* v_inst_3743_ = _args[7];
lean_object* v_inst_3744_ = _args[8];
lean_object* v_toMonadRef_3745_ = _args[9];
lean_object* v_inst_3746_ = _args[10];
lean_object* v_f_3747_ = _args[11];
lean_object* v___f_3748_ = _args[12];
lean_object* v_next_3749_ = _args[13];
lean_object* v_acc_3750_ = _args[14];
lean_object* v_h_3751_ = _args[15];
lean_object* v_G_3752_ = _args[16];
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3736_, v_toPure_3737_, v_hyps_3738_, v___x_3739_, v_inst_3740_, v_toBind_3741_, v_inst_3742_, v_inst_3743_, v_inst_3744_, v_toMonadRef_3745_, v_inst_3746_, v_f_3747_, v___f_3748_, v_next_3749_, v_acc_3750_, v_h_3751_, v_G_3752_);
lean_dec_ref(v_hyps_3738_);
lean_dec(v___x_3736_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3754_, lean_object* v_inst_3755_, lean_object* v_toBind_3756_, lean_object* v_inst_3757_, lean_object* v_inst_3758_, lean_object* v_inst_3759_, lean_object* v_toMonadRef_3760_, lean_object* v_inst_3761_, lean_object* v_f_3762_, lean_object* v___f_3763_, lean_object* v___f_3764_, lean_object* v_hyps_3765_){
_start:
{
lean_object* v___x_3766_; lean_object* v_newHyps_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___f_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3766_ = lean_array_get_size(v_hyps_3765_);
v_newHyps_3767_ = lean_mk_empty_array_with_capacity(v___x_3766_);
v___x_3768_ = lean_unsigned_to_nat(0u);
v___x_3769_ = lean_box(0);
lean_inc(v_toBind_3756_);
v___f_3770_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3770_, 0, v___x_3766_);
lean_closure_set(v___f_3770_, 1, v_toPure_3754_);
lean_closure_set(v___f_3770_, 2, v_hyps_3765_);
lean_closure_set(v___f_3770_, 3, v___x_3769_);
lean_closure_set(v___f_3770_, 4, v_inst_3755_);
lean_closure_set(v___f_3770_, 5, v_toBind_3756_);
lean_closure_set(v___f_3770_, 6, v_inst_3757_);
lean_closure_set(v___f_3770_, 7, v_inst_3758_);
lean_closure_set(v___f_3770_, 8, v_inst_3759_);
lean_closure_set(v___f_3770_, 9, v_toMonadRef_3760_);
lean_closure_set(v___f_3770_, 10, v_inst_3761_);
lean_closure_set(v___f_3770_, 11, v_f_3762_);
lean_closure_set(v___f_3770_, 12, v___f_3763_);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v_newHyps_3767_);
v___x_3772_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3770_, v___x_3768_, v___x_3771_, lean_box(0));
v___x_3773_ = lean_apply_4(v_toBind_3756_, lean_box(0), lean_box(0), v___x_3772_, v___f_3764_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3774_, lean_object* v_inst_3775_, lean_object* v_inst_3776_, lean_object* v_inst_3777_, lean_object* v_inst_3778_, lean_object* v_inst_3779_, lean_object* v_f_3780_){
_start:
{
lean_object* v_toApplicative_3781_; lean_object* v_toBind_3782_; lean_object* v_toPure_3783_; lean_object* v_toMonadRef_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___f_3787_; lean_object* v___f_3788_; lean_object* v___f_3789_; lean_object* v___f_3790_; lean_object* v___x_3791_; 
v_toApplicative_3781_ = lean_ctor_get(v_inst_3774_, 0);
v_toBind_3782_ = lean_ctor_get(v_inst_3774_, 1);
lean_inc_n(v_toBind_3782_, 3);
v_toPure_3783_ = lean_ctor_get(v_toApplicative_3781_, 1);
lean_inc_n(v_toPure_3783_, 4);
v_toMonadRef_3784_ = lean_ctor_get(v_inst_3776_, 1);
lean_inc_ref(v_toMonadRef_3784_);
lean_dec_ref(v_inst_3776_);
v___x_3785_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3775_, 2);
v___x_3786_ = lean_apply_2(v_inst_3775_, lean_box(0), v___x_3785_);
v___f_3787_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3787_, 0, v_toPure_3783_);
v___f_3788_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3788_, 0, v_inst_3775_);
lean_closure_set(v___f_3788_, 1, v_toBind_3782_);
lean_closure_set(v___f_3788_, 2, v___f_3787_);
lean_closure_set(v___f_3788_, 3, v_toPure_3783_);
v___f_3789_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3789_, 0, v_toPure_3783_);
v___f_3790_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3790_, 0, v_toPure_3783_);
lean_closure_set(v___f_3790_, 1, v_inst_3775_);
lean_closure_set(v___f_3790_, 2, v_toBind_3782_);
lean_closure_set(v___f_3790_, 3, v_inst_3777_);
lean_closure_set(v___f_3790_, 4, v_inst_3778_);
lean_closure_set(v___f_3790_, 5, v_inst_3774_);
lean_closure_set(v___f_3790_, 6, v_toMonadRef_3784_);
lean_closure_set(v___f_3790_, 7, v_inst_3779_);
lean_closure_set(v___f_3790_, 8, v_f_3780_);
lean_closure_set(v___f_3790_, 9, v___f_3789_);
lean_closure_set(v___f_3790_, 10, v___f_3788_);
v___x_3791_ = lean_apply_4(v_toBind_3782_, lean_box(0), lean_box(0), v___x_3786_, v___f_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3792_, lean_object* v_inst_3793_, lean_object* v_inst_3794_, lean_object* v_inst_3795_, lean_object* v_inst_3796_, lean_object* v_inst_3797_, lean_object* v_inst_3798_, lean_object* v_inst_3799_, lean_object* v_inst_3800_, lean_object* v_f_3801_){
_start:
{
lean_object* v_toApplicative_3802_; lean_object* v_toBind_3803_; lean_object* v_toPure_3804_; lean_object* v_toMonadRef_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___f_3808_; lean_object* v___f_3809_; lean_object* v___f_3810_; lean_object* v___f_3811_; lean_object* v___x_3812_; 
v_toApplicative_3802_ = lean_ctor_get(v_inst_3793_, 0);
v_toBind_3803_ = lean_ctor_get(v_inst_3793_, 1);
lean_inc_n(v_toBind_3803_, 3);
v_toPure_3804_ = lean_ctor_get(v_toApplicative_3802_, 1);
lean_inc_n(v_toPure_3804_, 4);
v_toMonadRef_3805_ = lean_ctor_get(v_inst_3795_, 1);
lean_inc_ref(v_toMonadRef_3805_);
lean_dec_ref(v_inst_3795_);
v___x_3806_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3794_, 2);
v___x_3807_ = lean_apply_2(v_inst_3794_, lean_box(0), v___x_3806_);
v___f_3808_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3808_, 0, v_toPure_3804_);
v___f_3809_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3809_, 0, v_inst_3794_);
lean_closure_set(v___f_3809_, 1, v_toBind_3803_);
lean_closure_set(v___f_3809_, 2, v___f_3808_);
lean_closure_set(v___f_3809_, 3, v_toPure_3804_);
v___f_3810_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3810_, 0, v_toPure_3804_);
v___f_3811_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3811_, 0, v_toPure_3804_);
lean_closure_set(v___f_3811_, 1, v_inst_3794_);
lean_closure_set(v___f_3811_, 2, v_toBind_3803_);
lean_closure_set(v___f_3811_, 3, v_inst_3797_);
lean_closure_set(v___f_3811_, 4, v_inst_3798_);
lean_closure_set(v___f_3811_, 5, v_inst_3793_);
lean_closure_set(v___f_3811_, 6, v_toMonadRef_3805_);
lean_closure_set(v___f_3811_, 7, v_inst_3799_);
lean_closure_set(v___f_3811_, 8, v_f_3801_);
lean_closure_set(v___f_3811_, 9, v___f_3810_);
lean_closure_set(v___f_3811_, 10, v___f_3809_);
v___x_3812_ = lean_apply_4(v_toBind_3803_, lean_box(0), lean_box(0), v___x_3807_, v___f_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3813_, lean_object* v_inst_3814_, lean_object* v_inst_3815_, lean_object* v_inst_3816_, lean_object* v_inst_3817_, lean_object* v_inst_3818_, lean_object* v_inst_3819_, lean_object* v_inst_3820_, lean_object* v_inst_3821_, lean_object* v_f_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3813_, v_inst_3814_, v_inst_3815_, v_inst_3816_, v_inst_3817_, v_inst_3818_, v_inst_3819_, v_inst_3820_, v_inst_3821_, v_f_3822_);
lean_dec_ref(v_inst_3821_);
lean_dec_ref(v_inst_3817_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3824_, lean_object* v_snd_3825_, lean_object* v___x_3826_, lean_object* v_toPure_3827_, lean_object* v_inst_3828_, lean_object* v_toBind_3829_, lean_object* v_inst_3830_, lean_object* v_inst_3831_, lean_object* v_toMonadRef_3832_, lean_object* v_inst_3833_, lean_object* v_inst_3834_, lean_object* v___f_3835_, lean_object* v_newHyp_3836_){
_start:
{
lean_object* v_type_3837_; lean_object* v_value_3838_; uint8_t v___x_3839_; 
v_type_3837_ = lean_ctor_get(v_newHyp_3836_, 1);
v_value_3838_ = lean_ctor_get(v_newHyp_3836_, 2);
lean_inc_ref(v_type_3837_);
v___x_3839_ = l_Lean_Expr_isFalse(v_type_3837_);
if (v___x_3839_ == 0)
{
lean_object* v_type_3840_; lean_object* v___f_3841_; lean_object* v___f_3842_; lean_object* v___f_3843_; lean_object* v___f_3844_; uint8_t v___x_3852_; 
lean_dec(v___f_3835_);
v_type_3840_ = lean_ctor_get(v___x_3824_, 1);
lean_inc(v_toPure_3827_);
lean_inc(v___x_3826_);
lean_inc_ref(v_newHyp_3836_);
lean_inc(v_snd_3825_);
v___f_3841_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3841_, 0, v_snd_3825_);
lean_closure_set(v___f_3841_, 1, v_newHyp_3836_);
lean_closure_set(v___f_3841_, 2, v___x_3826_);
lean_closure_set(v___f_3841_, 3, v_toPure_3827_);
v___f_3842_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3842_, 0, v___f_3841_);
lean_inc(v_toBind_3829_);
v___f_3843_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3843_, 0, v_inst_3828_);
lean_closure_set(v___f_3843_, 1, v_toBind_3829_);
lean_closure_set(v___f_3843_, 2, v___f_3842_);
lean_inc_ref(v___f_3843_);
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3844_, 0, v___f_3843_);
v___x_3852_ = lean_expr_eqv(v_type_3840_, v_type_3837_);
if (v___x_3852_ == 0)
{
lean_inc_ref(v_type_3837_);
lean_dec_ref(v_newHyp_3836_);
lean_dec(v___x_3826_);
lean_dec(v_snd_3825_);
goto v___jp_3845_;
}
else
{
if (v___x_3839_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_dec_ref(v___f_3844_);
lean_dec_ref(v___f_3843_);
lean_dec_ref(v_inst_3834_);
lean_dec(v_inst_3833_);
lean_dec_ref(v_toMonadRef_3832_);
lean_dec_ref(v_inst_3831_);
lean_dec_ref(v_inst_3830_);
lean_dec(v_toBind_3829_);
lean_dec_ref(v___x_3824_);
v___x_3853_ = lean_box(0);
v___x_3854_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3825_, v_newHyp_3836_, v___x_3826_, v_toPure_3827_, v___x_3853_);
return v___x_3854_;
}
else
{
lean_inc_ref(v_type_3837_);
lean_dec_ref(v_newHyp_3836_);
lean_dec(v___x_3826_);
lean_dec(v_snd_3825_);
goto v___jp_3845_;
}
}
v___jp_3845_:
{
lean_object* v_getInheritedTraceOptions_3846_; lean_object* v___x_3847_; lean_object* v___f_3848_; lean_object* v___f_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v_getInheritedTraceOptions_3846_ = lean_ctor_get(v_inst_3830_, 2);
lean_inc(v_getInheritedTraceOptions_3846_);
v___x_3847_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3829_, 3);
v___f_3848_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3848_, 0, v___f_3843_);
lean_closure_set(v___f_3848_, 1, v___x_3824_);
lean_closure_set(v___f_3848_, 2, v_type_3837_);
lean_closure_set(v___f_3848_, 3, v_inst_3831_);
lean_closure_set(v___f_3848_, 4, v_inst_3830_);
lean_closure_set(v___f_3848_, 5, v_toMonadRef_3832_);
lean_closure_set(v___f_3848_, 6, v_inst_3833_);
lean_closure_set(v___f_3848_, 7, v___x_3847_);
lean_closure_set(v___f_3848_, 8, v_toBind_3829_);
lean_closure_set(v___f_3848_, 9, v___f_3844_);
v___f_3849_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3849_, 0, v_inst_3834_);
lean_closure_set(v___f_3849_, 1, v_toPure_3827_);
lean_closure_set(v___f_3849_, 2, v___x_3847_);
lean_closure_set(v___f_3849_, 3, v_toBind_3829_);
v___x_3850_ = lean_apply_4(v_toBind_3829_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3846_, v___f_3849_);
v___x_3851_ = lean_apply_4(v_toBind_3829_, lean_box(0), lean_box(0), v___x_3850_, v___f_3848_);
return v___x_3851_;
}
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_inc_ref(v_value_3838_);
lean_dec_ref(v_newHyp_3836_);
lean_dec_ref(v_inst_3834_);
lean_dec(v_inst_3833_);
lean_dec_ref(v_toMonadRef_3832_);
lean_dec_ref(v_inst_3831_);
lean_dec_ref(v_inst_3830_);
lean_dec(v_toPure_3827_);
lean_dec(v___x_3826_);
lean_dec(v_snd_3825_);
lean_dec_ref(v___x_3824_);
v___x_3855_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3855_, 0, v_value_3838_);
v___x_3856_ = lean_apply_2(v_inst_3828_, lean_box(0), v___x_3855_);
v___x_3857_ = lean_apply_4(v_toBind_3829_, lean_box(0), lean_box(0), v___x_3856_, v___f_3835_);
return v___x_3857_;
}
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3858_, lean_object* v_toPure_3859_, lean_object* v_hyps_3860_, lean_object* v___x_3861_, lean_object* v_inst_3862_, lean_object* v_toBind_3863_, lean_object* v_inst_3864_, lean_object* v_inst_3865_, lean_object* v_toMonadRef_3866_, lean_object* v_inst_3867_, lean_object* v_inst_3868_, lean_object* v_f_3869_, lean_object* v___f_3870_, lean_object* v_next_3871_, lean_object* v_acc_3872_, lean_object* v_h_3873_, lean_object* v_G_3874_){
_start:
{
uint8_t v___x_3875_; 
v___x_3875_ = lean_nat_dec_lt(v_next_3871_, v___x_3858_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; 
lean_dec(v_G_3874_);
lean_dec(v_next_3871_);
lean_dec(v___f_3870_);
lean_dec(v_f_3869_);
lean_dec_ref(v_inst_3868_);
lean_dec(v_inst_3867_);
lean_dec_ref(v_toMonadRef_3866_);
lean_dec_ref(v_inst_3865_);
lean_dec_ref(v_inst_3864_);
lean_dec(v_toBind_3863_);
lean_dec(v_inst_3862_);
lean_dec(v___x_3861_);
v___x_3876_ = lean_apply_2(v_toPure_3859_, lean_box(0), v_acc_3872_);
return v___x_3876_;
}
else
{
lean_object* v_snd_3877_; lean_object* v___f_3878_; lean_object* v___x_3879_; lean_object* v___f_3880_; lean_object* v___x_3881_; lean_object* v___f_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v_snd_3877_ = lean_ctor_get(v_acc_3872_, 1);
lean_inc_n(v_snd_3877_, 2);
lean_dec_ref(v_acc_3872_);
lean_inc(v_next_3871_);
lean_inc_n(v_toPure_3859_, 2);
v___f_3878_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3878_, 0, v_toPure_3859_);
lean_closure_set(v___f_3878_, 1, v_next_3871_);
lean_closure_set(v___f_3878_, 2, v_G_3874_);
v___x_3879_ = lean_box(v___x_3875_);
v___f_3880_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3880_, 0, v___x_3879_);
lean_closure_set(v___f_3880_, 1, v_snd_3877_);
lean_closure_set(v___f_3880_, 2, v_toPure_3859_);
v___x_3881_ = lean_array_fget_borrowed(v_hyps_3860_, v_next_3871_);
lean_dec(v_next_3871_);
lean_inc_n(v_toBind_3863_, 3);
lean_inc_n(v___x_3881_, 2);
v___f_3882_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3882_, 0, v___x_3881_);
lean_closure_set(v___f_3882_, 1, v_snd_3877_);
lean_closure_set(v___f_3882_, 2, v___x_3861_);
lean_closure_set(v___f_3882_, 3, v_toPure_3859_);
lean_closure_set(v___f_3882_, 4, v_inst_3862_);
lean_closure_set(v___f_3882_, 5, v_toBind_3863_);
lean_closure_set(v___f_3882_, 6, v_inst_3864_);
lean_closure_set(v___f_3882_, 7, v_inst_3865_);
lean_closure_set(v___f_3882_, 8, v_toMonadRef_3866_);
lean_closure_set(v___f_3882_, 9, v_inst_3867_);
lean_closure_set(v___f_3882_, 10, v_inst_3868_);
lean_closure_set(v___f_3882_, 11, v___f_3880_);
v___x_3883_ = lean_apply_1(v_f_3869_, v___x_3881_);
v___x_3884_ = lean_apply_4(v_toBind_3863_, lean_box(0), lean_box(0), v___x_3883_, v___f_3882_);
v___x_3885_ = lean_apply_4(v_toBind_3863_, lean_box(0), lean_box(0), v___x_3884_, v___f_3870_);
v___x_3886_ = lean_apply_4(v_toBind_3863_, lean_box(0), lean_box(0), v___x_3885_, v___f_3878_);
return v___x_3886_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3858_ = stack[0].m_obj;
lean_object* v_toPure_3859_ = stack[1].m_obj;
lean_object* v_hyps_3860_ = stack[2].m_obj;
lean_object* v___x_3861_ = stack[3].m_obj;
lean_object* v_inst_3862_ = stack[4].m_obj;
lean_object* v_toBind_3863_ = stack[5].m_obj;
lean_object* v_inst_3864_ = stack[6].m_obj;
lean_object* v_inst_3865_ = stack[7].m_obj;
lean_object* v_toMonadRef_3866_ = stack[8].m_obj;
lean_object* v_inst_3867_ = stack[9].m_obj;
lean_object* v_inst_3868_ = stack[10].m_obj;
lean_object* v_f_3869_ = stack[11].m_obj;
lean_object* v___f_3870_ = stack[12].m_obj;
lean_object* v_next_3871_ = stack[13].m_obj;
lean_object* v_acc_3872_ = stack[14].m_obj;
lean_object* v_G_3874_ = stack[16].m_obj;
lean_object* v_res_3887_;
v_res_3887_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3858_, v_toPure_3859_, v_hyps_3860_, v___x_3861_, v_inst_3862_, v_toBind_3863_, v_inst_3864_, v_inst_3865_, v_toMonadRef_3866_, v_inst_3867_, v_inst_3868_, v_f_3869_, v___f_3870_, v_next_3871_, v_acc_3872_, lean_box(0), v_G_3874_);
stack->m_obj
 = v_res_3887_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3888_ = _args[0];
lean_object* v_toPure_3889_ = _args[1];
lean_object* v_hyps_3890_ = _args[2];
lean_object* v___x_3891_ = _args[3];
lean_object* v_inst_3892_ = _args[4];
lean_object* v_toBind_3893_ = _args[5];
lean_object* v_inst_3894_ = _args[6];
lean_object* v_inst_3895_ = _args[7];
lean_object* v_toMonadRef_3896_ = _args[8];
lean_object* v_inst_3897_ = _args[9];
lean_object* v_inst_3898_ = _args[10];
lean_object* v_f_3899_ = _args[11];
lean_object* v___f_3900_ = _args[12];
lean_object* v_next_3901_ = _args[13];
lean_object* v_acc_3902_ = _args[14];
lean_object* v_h_3903_ = _args[15];
lean_object* v_G_3904_ = _args[16];
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3888_, v_toPure_3889_, v_hyps_3890_, v___x_3891_, v_inst_3892_, v_toBind_3893_, v_inst_3894_, v_inst_3895_, v_toMonadRef_3896_, v_inst_3897_, v_inst_3898_, v_f_3899_, v___f_3900_, v_next_3901_, v_acc_3902_, v_h_3903_, v_G_3904_);
lean_dec_ref(v_hyps_3890_);
lean_dec(v___x_3888_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3906_, lean_object* v_inst_3907_, lean_object* v_toBind_3908_, lean_object* v_inst_3909_, lean_object* v_inst_3910_, lean_object* v_toMonadRef_3911_, lean_object* v_inst_3912_, lean_object* v_inst_3913_, lean_object* v_f_3914_, lean_object* v___f_3915_, lean_object* v___f_3916_, lean_object* v_hyps_3917_){
_start:
{
lean_object* v___x_3918_; lean_object* v_newHyps_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___f_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3918_ = lean_array_get_size(v_hyps_3917_);
v_newHyps_3919_ = lean_mk_empty_array_with_capacity(v___x_3918_);
v___x_3920_ = lean_unsigned_to_nat(0u);
v___x_3921_ = lean_box(0);
lean_inc(v_toBind_3908_);
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3922_, 0, v___x_3918_);
lean_closure_set(v___f_3922_, 1, v_toPure_3906_);
lean_closure_set(v___f_3922_, 2, v_hyps_3917_);
lean_closure_set(v___f_3922_, 3, v___x_3921_);
lean_closure_set(v___f_3922_, 4, v_inst_3907_);
lean_closure_set(v___f_3922_, 5, v_toBind_3908_);
lean_closure_set(v___f_3922_, 6, v_inst_3909_);
lean_closure_set(v___f_3922_, 7, v_inst_3910_);
lean_closure_set(v___f_3922_, 8, v_toMonadRef_3911_);
lean_closure_set(v___f_3922_, 9, v_inst_3912_);
lean_closure_set(v___f_3922_, 10, v_inst_3913_);
lean_closure_set(v___f_3922_, 11, v_f_3914_);
lean_closure_set(v___f_3922_, 12, v___f_3915_);
v___x_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v_newHyps_3919_);
v___x_3924_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3922_, v___x_3920_, v___x_3923_, lean_box(0));
v___x_3925_ = lean_apply_4(v_toBind_3908_, lean_box(0), lean_box(0), v___x_3924_, v___f_3916_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3926_, lean_object* v_inst_3927_, lean_object* v_inst_3928_, lean_object* v_inst_3929_, lean_object* v_inst_3930_, lean_object* v_inst_3931_, lean_object* v_f_3932_){
_start:
{
lean_object* v_toApplicative_3933_; lean_object* v_toBind_3934_; lean_object* v_toPure_3935_; lean_object* v_toMonadRef_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___f_3939_; lean_object* v___f_3940_; lean_object* v___f_3941_; lean_object* v___f_3942_; lean_object* v___x_3943_; 
v_toApplicative_3933_ = lean_ctor_get(v_inst_3926_, 0);
v_toBind_3934_ = lean_ctor_get(v_inst_3926_, 1);
lean_inc_n(v_toBind_3934_, 3);
v_toPure_3935_ = lean_ctor_get(v_toApplicative_3933_, 1);
lean_inc_n(v_toPure_3935_, 4);
v_toMonadRef_3936_ = lean_ctor_get(v_inst_3928_, 1);
lean_inc_ref(v_toMonadRef_3936_);
lean_dec_ref(v_inst_3928_);
v___x_3937_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3927_, 2);
v___x_3938_ = lean_apply_2(v_inst_3927_, lean_box(0), v___x_3937_);
v___f_3939_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3939_, 0, v_toPure_3935_);
v___f_3940_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3940_, 0, v_inst_3927_);
lean_closure_set(v___f_3940_, 1, v_toBind_3934_);
lean_closure_set(v___f_3940_, 2, v___f_3939_);
lean_closure_set(v___f_3940_, 3, v_toPure_3935_);
v___f_3941_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3941_, 0, v_toPure_3935_);
v___f_3942_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3942_, 0, v_toPure_3935_);
lean_closure_set(v___f_3942_, 1, v_inst_3927_);
lean_closure_set(v___f_3942_, 2, v_toBind_3934_);
lean_closure_set(v___f_3942_, 3, v_inst_3929_);
lean_closure_set(v___f_3942_, 4, v_inst_3926_);
lean_closure_set(v___f_3942_, 5, v_toMonadRef_3936_);
lean_closure_set(v___f_3942_, 6, v_inst_3931_);
lean_closure_set(v___f_3942_, 7, v_inst_3930_);
lean_closure_set(v___f_3942_, 8, v_f_3932_);
lean_closure_set(v___f_3942_, 9, v___f_3941_);
lean_closure_set(v___f_3942_, 10, v___f_3940_);
v___x_3943_ = lean_apply_4(v_toBind_3934_, lean_box(0), lean_box(0), v___x_3938_, v___f_3942_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3944_, lean_object* v_inst_3945_, lean_object* v_inst_3946_, lean_object* v_inst_3947_, lean_object* v_inst_3948_, lean_object* v_inst_3949_, lean_object* v_inst_3950_, lean_object* v_inst_3951_, lean_object* v_inst_3952_, lean_object* v_f_3953_){
_start:
{
lean_object* v_toApplicative_3954_; lean_object* v_toBind_3955_; lean_object* v_toPure_3956_; lean_object* v_toMonadRef_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___f_3960_; lean_object* v___f_3961_; lean_object* v___f_3962_; lean_object* v___f_3963_; lean_object* v___x_3964_; 
v_toApplicative_3954_ = lean_ctor_get(v_inst_3945_, 0);
v_toBind_3955_ = lean_ctor_get(v_inst_3945_, 1);
lean_inc_n(v_toBind_3955_, 3);
v_toPure_3956_ = lean_ctor_get(v_toApplicative_3954_, 1);
lean_inc_n(v_toPure_3956_, 4);
v_toMonadRef_3957_ = lean_ctor_get(v_inst_3947_, 1);
lean_inc_ref(v_toMonadRef_3957_);
lean_dec_ref(v_inst_3947_);
v___x_3958_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3946_, 2);
v___x_3959_ = lean_apply_2(v_inst_3946_, lean_box(0), v___x_3958_);
v___f_3960_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3960_, 0, v_toPure_3956_);
v___f_3961_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3961_, 0, v_inst_3946_);
lean_closure_set(v___f_3961_, 1, v_toBind_3955_);
lean_closure_set(v___f_3961_, 2, v___f_3960_);
lean_closure_set(v___f_3961_, 3, v_toPure_3956_);
v___f_3962_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3962_, 0, v_toPure_3956_);
v___f_3963_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3963_, 0, v_toPure_3956_);
lean_closure_set(v___f_3963_, 1, v_inst_3946_);
lean_closure_set(v___f_3963_, 2, v_toBind_3955_);
lean_closure_set(v___f_3963_, 3, v_inst_3949_);
lean_closure_set(v___f_3963_, 4, v_inst_3945_);
lean_closure_set(v___f_3963_, 5, v_toMonadRef_3957_);
lean_closure_set(v___f_3963_, 6, v_inst_3951_);
lean_closure_set(v___f_3963_, 7, v_inst_3950_);
lean_closure_set(v___f_3963_, 8, v_f_3953_);
lean_closure_set(v___f_3963_, 9, v___f_3962_);
lean_closure_set(v___f_3963_, 10, v___f_3961_);
v___x_3964_ = lean_apply_4(v_toBind_3955_, lean_box(0), lean_box(0), v___x_3959_, v___f_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3965_, lean_object* v_inst_3966_, lean_object* v_inst_3967_, lean_object* v_inst_3968_, lean_object* v_inst_3969_, lean_object* v_inst_3970_, lean_object* v_inst_3971_, lean_object* v_inst_3972_, lean_object* v_inst_3973_, lean_object* v_f_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3965_, v_inst_3966_, v_inst_3967_, v_inst_3968_, v_inst_3969_, v_inst_3970_, v_inst_3971_, v_inst_3972_, v_inst_3973_, v_f_3974_);
lean_dec_ref(v_inst_3973_);
lean_dec_ref(v_inst_3969_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3976_, lean_object* v_x_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_apply_1(v_f_3976_, v___y_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3980_, lean_object* v_inst_3981_, lean_object* v___f_3982_, lean_object* v_hyps_3983_){
_start:
{
lean_object* v_toPure_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v_toPure_3984_ = lean_ctor_get(v_toApplicative_3980_, 1);
lean_inc(v_toPure_3984_);
lean_dec_ref(v_toApplicative_3980_);
v___x_3985_ = lean_unsigned_to_nat(0u);
v___x_3986_ = lean_array_get_size(v_hyps_3983_);
v___x_3987_ = lean_box(0);
v___x_3988_ = lean_nat_dec_lt(v___x_3985_, v___x_3986_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
lean_dec_ref(v_hyps_3983_);
lean_dec(v___f_3982_);
lean_dec_ref(v_inst_3981_);
v___x_3989_ = lean_apply_2(v_toPure_3984_, lean_box(0), v___x_3987_);
return v___x_3989_;
}
else
{
uint8_t v___x_3990_; 
v___x_3990_ = lean_nat_dec_le(v___x_3986_, v___x_3986_);
if (v___x_3990_ == 0)
{
if (v___x_3988_ == 0)
{
lean_object* v___x_3991_; 
lean_dec_ref(v_hyps_3983_);
lean_dec(v___f_3982_);
lean_dec_ref(v_inst_3981_);
v___x_3991_ = lean_apply_2(v_toPure_3984_, lean_box(0), v___x_3987_);
return v___x_3991_;
}
else
{
size_t v___x_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
lean_dec(v_toPure_3984_);
v___x_3992_ = ((size_t)0ULL);
v___x_3993_ = lean_usize_of_nat(v___x_3986_);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3981_, v___f_3982_, v_hyps_3983_, v___x_3992_, v___x_3993_, v___x_3987_);
return v___x_3994_;
}
}
else
{
size_t v___x_3995_; size_t v___x_3996_; lean_object* v___x_3997_; 
lean_dec(v_toPure_3984_);
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = lean_usize_of_nat(v___x_3986_);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3981_, v___f_3982_, v_hyps_3983_, v___x_3995_, v___x_3996_, v___x_3987_);
return v___x_3997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3998_, lean_object* v_inst_3999_, lean_object* v_f_4000_){
_start:
{
lean_object* v_toApplicative_4001_; lean_object* v_toBind_4002_; lean_object* v___f_4003_; lean_object* v___f_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v_toApplicative_4001_ = lean_ctor_get(v_inst_3998_, 0);
lean_inc_ref(v_toApplicative_4001_);
v_toBind_4002_ = lean_ctor_get(v_inst_3998_, 1);
lean_inc(v_toBind_4002_);
v___f_4003_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4003_, 0, v_f_4000_);
v___f_4004_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4004_, 0, v_toApplicative_4001_);
lean_closure_set(v___f_4004_, 1, v_inst_3998_);
lean_closure_set(v___f_4004_, 2, v___f_4003_);
v___x_4005_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_4006_ = lean_apply_2(v_inst_3999_, lean_box(0), v___x_4005_);
v___x_4007_ = lean_apply_4(v_toBind_4002_, lean_box(0), lean_box(0), v___x_4006_, v___f_4004_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_4008_, lean_object* v_inst_4009_, lean_object* v_inst_4010_, lean_object* v_inst_4011_, lean_object* v_f_4012_){
_start:
{
lean_object* v_toApplicative_4013_; lean_object* v_toBind_4014_; lean_object* v___f_4015_; lean_object* v___f_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_toApplicative_4013_ = lean_ctor_get(v_inst_4009_, 0);
lean_inc_ref(v_toApplicative_4013_);
v_toBind_4014_ = lean_ctor_get(v_inst_4009_, 1);
lean_inc(v_toBind_4014_);
v___f_4015_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4015_, 0, v_f_4012_);
v___f_4016_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4016_, 0, v_toApplicative_4013_);
lean_closure_set(v___f_4016_, 1, v_inst_4009_);
lean_closure_set(v___f_4016_, 2, v___f_4015_);
v___x_4017_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_4018_ = lean_apply_2(v_inst_4010_, lean_box(0), v___x_4017_);
v___x_4019_ = lean_apply_4(v_toBind_4014_, lean_box(0), lean_box(0), v___x_4018_, v___f_4016_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_4020_, lean_object* v_inst_4021_, lean_object* v_inst_4022_, lean_object* v_inst_4023_, lean_object* v_f_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_4020_, v_inst_4021_, v_inst_4022_, v_inst_4023_, v_f_4024_);
lean_dec_ref(v_inst_4023_);
return v_res_4025_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
return v___x_4027_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_4028_, lean_object* v_methods_4029_, lean_object* v_config_4030_, lean_object* v_hyp_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v___x_4040_; lean_object* v_caches_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v_typeAnalysis_4048_; lean_object* v_target_4049_; lean_object* v_hypotheses_4050_; uint8_t v_didChange_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4092_; 
v___x_4040_ = lean_st_ref_get(v_a_4032_);
v_caches_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc_ref(v_caches_4041_);
lean_dec(v___x_4040_);
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_4028_, v_caches_4041_);
v___x_4044_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_4045_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4042_);
lean_ctor_set(v___x_4045_, 1, v___x_4043_);
lean_ctor_set(v___x_4045_, 2, v___x_4044_);
lean_ctor_set(v___x_4045_, 3, v___x_4044_);
v___x_4046_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_4028_, v___x_4044_, v_caches_4041_);
v___x_4047_ = lean_st_ref_take(v_a_4032_);
v_typeAnalysis_4048_ = lean_ctor_get(v___x_4047_, 1);
v_target_4049_ = lean_ctor_get(v___x_4047_, 2);
v_hypotheses_4050_ = lean_ctor_get(v___x_4047_, 3);
v_didChange_4051_ = lean_ctor_get_uint8(v___x_4047_, sizeof(void*)*4);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v___x_4047_, 0);
lean_dec(v_unused_4093_);
v___x_4053_ = v___x_4047_;
v_isShared_4054_ = v_isSharedCheck_4092_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_hypotheses_4050_);
lean_inc(v_target_4049_);
lean_inc(v_typeAnalysis_4048_);
lean_dec(v___x_4047_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4092_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4046_);
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_typeAnalysis_4048_);
lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_target_4049_);
lean_ctor_set(v_reuseFailAlloc_4091_, 3, v_hypotheses_4050_);
lean_ctor_set_uint8(v_reuseFailAlloc_4091_, sizeof(void*)*4, v_didChange_4051_);
v___x_4056_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4057_; lean_object* v_type_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4057_ = lean_st_ref_put(v_a_4032_, v___x_4056_);
v_type_4058_ = lean_ctor_get(v_hyp_4031_, 1);
lean_inc_ref(v_type_4058_);
v___x_4059_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_4059_, 0, v_type_4058_);
v___x_4060_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_4059_, v_methods_4029_, v_config_4030_, v___x_4045_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v_fst_4062_; lean_object* v_snd_4063_; lean_object* v___x_4064_; lean_object* v_caches_4065_; lean_object* v_persistentCache_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v_typeAnalysis_4069_; lean_object* v_target_4070_; lean_object* v_hypotheses_4071_; uint8_t v_didChange_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4081_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v_fst_4062_ = lean_ctor_get(v_a_4061_, 0);
lean_inc(v_fst_4062_);
v_snd_4063_ = lean_ctor_get(v_a_4061_, 1);
lean_inc(v_snd_4063_);
lean_dec(v_a_4061_);
v___x_4064_ = lean_st_ref_get(v_a_4032_);
v_caches_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc_ref(v_caches_4065_);
lean_dec(v___x_4064_);
v_persistentCache_4066_ = lean_ctor_get(v_snd_4063_, 1);
lean_inc_ref(v_persistentCache_4066_);
lean_dec(v_snd_4063_);
v___x_4067_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_4028_, v_persistentCache_4066_, v_caches_4065_);
v___x_4068_ = lean_st_ref_take(v_a_4032_);
v_typeAnalysis_4069_ = lean_ctor_get(v___x_4068_, 1);
v_target_4070_ = lean_ctor_get(v___x_4068_, 2);
v_hypotheses_4071_ = lean_ctor_get(v___x_4068_, 3);
v_didChange_4072_ = lean_ctor_get_uint8(v___x_4068_, sizeof(void*)*4);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v___x_4068_, 0);
lean_dec(v_unused_4082_);
v___x_4074_ = v___x_4068_;
v_isShared_4075_ = v_isSharedCheck_4081_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_hypotheses_4071_);
lean_inc(v_target_4070_);
lean_inc(v_typeAnalysis_4069_);
lean_dec(v___x_4068_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4081_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4067_);
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_typeAnalysis_4069_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_target_4070_);
lean_ctor_set(v_reuseFailAlloc_4080_, 3, v_hypotheses_4071_);
lean_ctor_set_uint8(v_reuseFailAlloc_4080_, sizeof(void*)*4, v_didChange_4072_);
v___x_4077_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_st_ref_put(v_a_4032_, v___x_4077_);
v___x_4079_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_4031_, v_fst_4062_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
return v___x_4079_;
}
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec_ref(v_hyp_4031_);
v_a_4083_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4060_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4060_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_cacheId_4028_ = stack[0].m_num;
lean_object* v_methods_4029_ = stack[1].m_obj;
lean_object* v_config_4030_ = stack[2].m_obj;
lean_object* v_hyp_4031_ = stack[3].m_obj;
lean_object* v_a_4032_ = stack[4].m_obj;
lean_object* v_a_4033_ = stack[5].m_obj;
lean_object* v_a_4034_ = stack[6].m_obj;
lean_object* v_a_4035_ = stack[7].m_obj;
lean_object* v_a_4036_ = stack[8].m_obj;
lean_object* v_a_4037_ = stack[9].m_obj;
lean_object* v_a_4038_ = stack[10].m_obj;
lean_object* v_res_4094_;
v_res_4094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4028_, v_methods_4029_, v_config_4030_, v_hyp_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
stack->m_obj
 = v_res_4094_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_4095_, lean_object* v_methods_4096_, lean_object* v_config_4097_, lean_object* v_hyp_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
uint8_t v_cacheId_boxed_4107_; lean_object* v_res_4108_; 
v_cacheId_boxed_4107_ = lean_unbox(v_cacheId_4095_);
v_res_4108_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_4107_, v_methods_4096_, v_config_4097_, v_hyp_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec(v_a_4099_);
return v_res_4108_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_4109_, lean_object* v_methods_4110_, lean_object* v_config_4111_, lean_object* v_hyp_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4109_, v_methods_4110_, v_config_4111_, v_hyp_4112_, v_a_4114_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
return v___x_4125_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp_0interp(lean_interpreter_value* stack)
{
uint8_t v_cacheId_4109_ = stack[0].m_num;
lean_object* v_methods_4110_ = stack[1].m_obj;
lean_object* v_config_4111_ = stack[2].m_obj;
lean_object* v_hyp_4112_ = stack[3].m_obj;
lean_object* v_a_4113_ = stack[4].m_obj;
lean_object* v_a_4114_ = stack[5].m_obj;
lean_object* v_a_4115_ = stack[6].m_obj;
lean_object* v_a_4116_ = stack[7].m_obj;
lean_object* v_a_4117_ = stack[8].m_obj;
lean_object* v_a_4118_ = stack[9].m_obj;
lean_object* v_a_4119_ = stack[10].m_obj;
lean_object* v_a_4120_ = stack[11].m_obj;
lean_object* v_a_4121_ = stack[12].m_obj;
lean_object* v_a_4122_ = stack[13].m_obj;
lean_object* v_a_4123_ = stack[14].m_obj;
lean_object* v_res_4126_;
v_res_4126_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_4109_, v_methods_4110_, v_config_4111_, v_hyp_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
stack->m_obj
 = v_res_4126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4127_, lean_object* v_methods_4128_, lean_object* v_config_4129_, lean_object* v_hyp_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
uint8_t v_cacheId_boxed_4143_; lean_object* v_res_4144_; 
v_cacheId_boxed_4143_ = lean_unbox(v_cacheId_4127_);
v_res_4144_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4143_, v_methods_4128_, v_config_4129_, v_hyp_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
return v_res_4144_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4145_, lean_object* v_methods_4146_, lean_object* v_config_4147_, lean_object* v_hyp_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_){
_start:
{
lean_object* v___x_4157_; lean_object* v_caches_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v_typeAnalysis_4165_; lean_object* v_target_4166_; lean_object* v_hypotheses_4167_; uint8_t v_didChange_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4209_; 
v___x_4157_ = lean_st_ref_get(v_a_4149_);
v_caches_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc_ref(v_caches_4158_);
lean_dec(v___x_4157_);
v___x_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4145_, v_caches_4158_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4163_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4145_, v___x_4162_, v_caches_4158_);
v___x_4164_ = lean_st_ref_take(v_a_4149_);
v_typeAnalysis_4165_ = lean_ctor_get(v___x_4164_, 1);
v_target_4166_ = lean_ctor_get(v___x_4164_, 2);
v_hypotheses_4167_ = lean_ctor_get(v___x_4164_, 3);
v_didChange_4168_ = lean_ctor_get_uint8(v___x_4164_, sizeof(void*)*4);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4209_ == 0)
{
lean_object* v_unused_4210_; 
v_unused_4210_ = lean_ctor_get(v___x_4164_, 0);
lean_dec(v_unused_4210_);
v___x_4170_ = v___x_4164_;
v_isShared_4171_ = v_isSharedCheck_4209_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_hypotheses_4167_);
lean_inc(v_target_4166_);
lean_inc(v_typeAnalysis_4165_);
lean_dec(v___x_4164_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4209_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 0, v___x_4163_);
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4163_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_typeAnalysis_4165_);
lean_ctor_set(v_reuseFailAlloc_4208_, 2, v_target_4166_);
lean_ctor_set(v_reuseFailAlloc_4208_, 3, v_hypotheses_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4208_, sizeof(void*)*4, v_didChange_4168_);
v___x_4173_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; lean_object* v_type_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4174_ = lean_st_ref_put(v_a_4149_, v___x_4173_);
v_type_4175_ = lean_ctor_get(v_hyp_4148_, 1);
lean_inc_ref(v_type_4175_);
v___x_4176_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4176_, 0, v_type_4175_);
v___x_4177_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4176_, v_methods_4146_, v_config_4147_, v___x_4161_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v_fst_4179_; lean_object* v_snd_4180_; lean_object* v___x_4181_; lean_object* v_caches_4182_; lean_object* v_cache_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v_typeAnalysis_4186_; lean_object* v_target_4187_; lean_object* v_hypotheses_4188_; uint8_t v_didChange_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4198_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4177_, 1);
v_fst_4179_ = lean_ctor_get(v_a_4178_, 0);
lean_inc(v_fst_4179_);
v_snd_4180_ = lean_ctor_get(v_a_4178_, 1);
lean_inc(v_snd_4180_);
lean_dec(v_a_4178_);
v___x_4181_ = lean_st_ref_get(v_a_4149_);
v_caches_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc_ref(v_caches_4182_);
lean_dec(v___x_4181_);
v_cache_4183_ = lean_ctor_get(v_snd_4180_, 1);
lean_inc_ref(v_cache_4183_);
lean_dec(v_snd_4180_);
v___x_4184_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4145_, v_cache_4183_, v_caches_4182_);
v___x_4185_ = lean_st_ref_take(v_a_4149_);
v_typeAnalysis_4186_ = lean_ctor_get(v___x_4185_, 1);
v_target_4187_ = lean_ctor_get(v___x_4185_, 2);
v_hypotheses_4188_ = lean_ctor_get(v___x_4185_, 3);
v_didChange_4189_ = lean_ctor_get_uint8(v___x_4185_, sizeof(void*)*4);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4198_ == 0)
{
lean_object* v_unused_4199_; 
v_unused_4199_ = lean_ctor_get(v___x_4185_, 0);
lean_dec(v_unused_4199_);
v___x_4191_ = v___x_4185_;
v_isShared_4192_ = v_isSharedCheck_4198_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_hypotheses_4188_);
lean_inc(v_target_4187_);
lean_inc(v_typeAnalysis_4186_);
lean_dec(v___x_4185_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4198_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 0, v___x_4184_);
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4184_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v_typeAnalysis_4186_);
lean_ctor_set(v_reuseFailAlloc_4197_, 2, v_target_4187_);
lean_ctor_set(v_reuseFailAlloc_4197_, 3, v_hypotheses_4188_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, sizeof(void*)*4, v_didChange_4189_);
v___x_4194_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_st_ref_put(v_a_4149_, v___x_4194_);
v___x_4196_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4148_, v_fst_4179_);
lean_dec(v_fst_4179_);
return v___x_4196_;
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec_ref(v_hyp_4148_);
v_a_4200_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4177_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4177_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_cacheId_4145_ = stack[0].m_num;
lean_object* v_methods_4146_ = stack[1].m_obj;
lean_object* v_config_4147_ = stack[2].m_obj;
lean_object* v_hyp_4148_ = stack[3].m_obj;
lean_object* v_a_4149_ = stack[4].m_obj;
lean_object* v_a_4150_ = stack[5].m_obj;
lean_object* v_a_4151_ = stack[6].m_obj;
lean_object* v_a_4152_ = stack[7].m_obj;
lean_object* v_a_4153_ = stack[8].m_obj;
lean_object* v_a_4154_ = stack[9].m_obj;
lean_object* v_a_4155_ = stack[10].m_obj;
lean_object* v_res_4211_;
v_res_4211_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4145_, v_methods_4146_, v_config_4147_, v_hyp_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_);
stack->m_obj
 = v_res_4211_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4212_, lean_object* v_methods_4213_, lean_object* v_config_4214_, lean_object* v_hyp_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
uint8_t v_cacheId_boxed_4224_; lean_object* v_res_4225_; 
v_cacheId_boxed_4224_ = lean_unbox(v_cacheId_4212_);
v_res_4225_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4224_, v_methods_4213_, v_config_4214_, v_hyp_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
return v_res_4225_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4226_, lean_object* v_methods_4227_, lean_object* v_config_4228_, lean_object* v_hyp_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4226_, v_methods_4227_, v_config_4228_, v_hyp_4229_, v_a_4231_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
return v___x_4242_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp_0interp(lean_interpreter_value* stack)
{
uint8_t v_cacheId_4226_ = stack[0].m_num;
lean_object* v_methods_4227_ = stack[1].m_obj;
lean_object* v_config_4228_ = stack[2].m_obj;
lean_object* v_hyp_4229_ = stack[3].m_obj;
lean_object* v_a_4230_ = stack[4].m_obj;
lean_object* v_a_4231_ = stack[5].m_obj;
lean_object* v_a_4232_ = stack[6].m_obj;
lean_object* v_a_4233_ = stack[7].m_obj;
lean_object* v_a_4234_ = stack[8].m_obj;
lean_object* v_a_4235_ = stack[9].m_obj;
lean_object* v_a_4236_ = stack[10].m_obj;
lean_object* v_a_4237_ = stack[11].m_obj;
lean_object* v_a_4238_ = stack[12].m_obj;
lean_object* v_a_4239_ = stack[13].m_obj;
lean_object* v_a_4240_ = stack[14].m_obj;
lean_object* v_res_4243_;
v_res_4243_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_4226_, v_methods_4227_, v_config_4228_, v_hyp_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
stack->m_obj
 = v_res_4243_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4244_, lean_object* v_methods_4245_, lean_object* v_config_4246_, lean_object* v_hyp_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
uint8_t v_cacheId_boxed_4260_; lean_object* v_res_4261_; 
v_cacheId_boxed_4260_ = lean_unbox(v_cacheId_4244_);
v_res_4261_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4260_, v_methods_4245_, v_config_4246_, v_hyp_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
lean_dec(v_a_4258_);
lean_dec_ref(v_a_4257_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
return v_res_4261_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4262_, lean_object* v_a_4263_, lean_object* v___x_4264_, lean_object* v_____r_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4278_ = lean_array_push(v_snd_4262_, v_a_4263_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4264_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
v___x_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_4262_ = stack[0].m_obj;
lean_object* v_a_4263_ = stack[1].m_obj;
lean_object* v___x_4264_ = stack[2].m_obj;
lean_object* v_____r_4265_ = stack[3].m_obj;
lean_object* v___y_4266_ = stack[4].m_obj;
lean_object* v___y_4267_ = stack[5].m_obj;
lean_object* v___y_4268_ = stack[6].m_obj;
lean_object* v___y_4269_ = stack[7].m_obj;
lean_object* v___y_4270_ = stack[8].m_obj;
lean_object* v___y_4271_ = stack[9].m_obj;
lean_object* v___y_4272_ = stack[10].m_obj;
lean_object* v___y_4273_ = stack[11].m_obj;
lean_object* v___y_4274_ = stack[12].m_obj;
lean_object* v___y_4275_ = stack[13].m_obj;
lean_object* v___y_4276_ = stack[14].m_obj;
lean_object* v_res_4282_;
v_res_4282_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4262_, v_a_4263_, v___x_4264_, v_____r_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
stack->m_obj
 = v_res_4282_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4283_, lean_object* v_a_4284_, lean_object* v___x_4285_, lean_object* v_____r_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4283_, v_a_4284_, v___x_4285_, v_____r_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
return v_res_4299_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4300_, lean_object* v___f_4301_, lean_object* v_____r_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v_caches_4316_; lean_object* v_typeAnalysis_4317_; lean_object* v_target_4318_; lean_object* v_hypotheses_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4329_; 
v___x_4315_ = lean_st_ref_take(v___y_4304_);
v_caches_4316_ = lean_ctor_get(v___x_4315_, 0);
v_typeAnalysis_4317_ = lean_ctor_get(v___x_4315_, 1);
v_target_4318_ = lean_ctor_get(v___x_4315_, 2);
v_hypotheses_4319_ = lean_ctor_get(v___x_4315_, 3);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4321_ = v___x_4315_;
v_isShared_4322_ = v_isSharedCheck_4329_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_hypotheses_4319_);
lean_inc(v_target_4318_);
lean_inc(v_typeAnalysis_4317_);
lean_inc(v_caches_4316_);
lean_dec(v___x_4315_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4329_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4323_; lean_object* v___x_4325_; 
v___x_4323_ = lean_box(0);
if (v_isShared_4322_ == 0)
{
v___x_4325_ = v___x_4321_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_caches_4316_);
lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_typeAnalysis_4317_);
lean_ctor_set(v_reuseFailAlloc_4328_, 2, v_target_4318_);
lean_ctor_set(v_reuseFailAlloc_4328_, 3, v_hypotheses_4319_);
v___x_4325_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
lean_ctor_set_uint8(v___x_4325_, sizeof(void*)*4, v___x_4300_);
v___x_4326_ = lean_st_ref_put(v___y_4304_, v___x_4325_);
lean_inc(v___y_4313_);
lean_inc_ref(v___y_4312_);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
lean_inc(v___y_4309_);
lean_inc_ref(v___y_4308_);
lean_inc(v___y_4307_);
lean_inc_ref(v___y_4306_);
lean_inc(v___y_4305_);
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
v___x_4327_ = lean_apply_13(v___f_4301_, v___x_4323_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, lean_box(0));
return v___x_4327_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4300_ = stack[0].m_num;
lean_object* v___f_4301_ = stack[1].m_obj;
lean_object* v_____r_4302_ = stack[2].m_obj;
lean_object* v___y_4303_ = stack[3].m_obj;
lean_object* v___y_4304_ = stack[4].m_obj;
lean_object* v___y_4305_ = stack[5].m_obj;
lean_object* v___y_4306_ = stack[6].m_obj;
lean_object* v___y_4307_ = stack[7].m_obj;
lean_object* v___y_4308_ = stack[8].m_obj;
lean_object* v___y_4309_ = stack[9].m_obj;
lean_object* v___y_4310_ = stack[10].m_obj;
lean_object* v___y_4311_ = stack[11].m_obj;
lean_object* v___y_4312_ = stack[12].m_obj;
lean_object* v___y_4313_ = stack[13].m_obj;
lean_object* v_res_4330_;
v_res_4330_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4300_, v___f_4301_, v_____r_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
stack->m_obj
 = v_res_4330_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4331_, lean_object* v___f_4332_, lean_object* v_____r_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
uint8_t v___x_22319__boxed_4346_; lean_object* v_res_4347_; 
v___x_22319__boxed_4346_ = lean_unbox(v___x_4331_);
v_res_4347_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22319__boxed_4346_, v___f_4332_, v_____r_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
return v_res_4347_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4348_, lean_object* v_hypotheses_4349_, uint8_t v_cacheId_4350_, lean_object* v_methods_4351_, lean_object* v_config_4352_, lean_object* v___x_4353_, lean_object* v___x_4354_, lean_object* v___x_4355_, lean_object* v_toMonadRef_4356_, lean_object* v___f_4357_, lean_object* v_next_4358_, lean_object* v_acc_4359_, lean_object* v_h_4360_, lean_object* v_G_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___y_4375_; uint8_t v___x_4397_; 
v___x_4397_ = lean_nat_dec_lt(v_next_4358_, v___x_4348_);
if (v___x_4397_ == 0)
{
lean_object* v___x_4398_; 
lean_dec_ref(v_G_4361_);
lean_dec(v___f_4357_);
lean_dec_ref(v_toMonadRef_4356_);
lean_dec_ref(v___x_4355_);
lean_dec_ref(v___x_4354_);
lean_dec(v___x_4353_);
lean_dec_ref(v_config_4352_);
lean_dec_ref(v_methods_4351_);
v___x_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4398_, 0, v_acc_4359_);
return v___x_4398_;
}
else
{
lean_object* v_snd_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4473_; 
v_snd_4399_ = lean_ctor_get(v_acc_4359_, 1);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_acc_4359_);
if (v_isSharedCheck_4473_ == 0)
{
lean_object* v_unused_4474_; 
v_unused_4474_ = lean_ctor_get(v_acc_4359_, 0);
lean_dec(v_unused_4474_);
v___x_4401_ = v_acc_4359_;
v_isShared_4402_ = v_isSharedCheck_4473_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_snd_4399_);
lean_dec(v_acc_4359_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4473_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_array_fget_borrowed(v_hypotheses_4349_, v_next_4358_);
lean_inc(v___x_4403_);
v___x_4404_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4350_, v_methods_4351_, v_config_4352_, v___x_4403_, v___y_4363_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v_type_4406_; lean_object* v_value_4407_; uint8_t v___x_4408_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v_type_4406_ = lean_ctor_get(v_a_4405_, 1);
v_value_4407_ = lean_ctor_get(v_a_4405_, 2);
lean_inc_ref(v_type_4406_);
v___x_4408_ = l_Lean_Expr_isFalse(v_type_4406_);
if (v___x_4408_ == 0)
{
lean_object* v_type_4409_; lean_object* v___f_4410_; uint8_t v___x_4440_; 
lean_del_object(v___x_4401_);
v_type_4409_ = lean_ctor_get(v___x_4403_, 1);
lean_inc(v___x_4353_);
lean_inc(v_a_4405_);
lean_inc(v_snd_4399_);
v___f_4410_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4410_, 0, v_snd_4399_);
lean_closure_set(v___f_4410_, 1, v_a_4405_);
lean_closure_set(v___f_4410_, 2, v___x_4353_);
v___x_4440_ = lean_expr_eqv(v_type_4409_, v_type_4406_);
if (v___x_4440_ == 0)
{
lean_inc_ref(v_type_4406_);
lean_dec(v_a_4405_);
lean_dec(v_snd_4399_);
lean_dec(v___x_4353_);
goto v___jp_4414_;
}
else
{
if (v___x_4408_ == 0)
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
lean_dec_ref(v___f_4410_);
lean_dec(v___f_4357_);
lean_dec_ref(v_toMonadRef_4356_);
lean_dec_ref(v___x_4355_);
lean_dec_ref(v___x_4354_);
v___x_4441_ = lean_box(0);
v___x_4442_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4399_, v_a_4405_, v___x_4353_, v___x_4441_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
v___y_4375_ = v___x_4442_;
goto v___jp_4374_;
}
else
{
lean_inc_ref(v_type_4406_);
lean_dec(v_a_4405_);
lean_dec(v_snd_4399_);
lean_dec(v___x_4353_);
goto v___jp_4414_;
}
}
v___jp_4411_:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4412_ = lean_box(0);
v___x_4413_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4397_, v___f_4410_, v___x_4412_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
v___y_4375_ = v___x_4413_;
goto v___jp_4374_;
}
v___jp_4414_:
{
lean_object* v_toCold_4415_; lean_object* v_options_4416_; uint8_t v_hasTrace_4417_; 
v_toCold_4415_ = lean_ctor_get(v___y_4371_, 0);
v_options_4416_ = lean_ctor_get(v_toCold_4415_, 2);
v_hasTrace_4417_ = lean_ctor_get_uint8(v_options_4416_, sizeof(void*)*1);
if (v_hasTrace_4417_ == 0)
{
lean_dec_ref(v_type_4406_);
lean_dec(v___f_4357_);
lean_dec_ref(v_toMonadRef_4356_);
lean_dec_ref(v___x_4355_);
lean_dec_ref(v___x_4354_);
goto v___jp_4411_;
}
else
{
lean_object* v_inheritedTraceOptions_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v_inheritedTraceOptions_4418_ = lean_ctor_get(v_toCold_4415_, 11);
v___x_4419_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4420_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4421_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4418_, v_options_4416_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_dec_ref(v_type_4406_);
lean_dec(v___f_4357_);
lean_dec_ref(v_toMonadRef_4356_);
lean_dec_ref(v___x_4355_);
lean_dec_ref(v___x_4354_);
goto v___jp_4411_;
}
else
{
lean_object* v_type_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_22210__overap_4428_; lean_object* v___x_4429_; 
v_type_4422_ = lean_ctor_get(v___x_4403_, 1);
lean_inc_ref(v_type_4422_);
v___x_4423_ = l_Lean_MessageData_ofExpr(v_type_4422_);
v___x_4424_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
v___x_4426_ = l_Lean_MessageData_ofExpr(v_type_4406_);
v___x_4427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4425_);
lean_ctor_set(v___x_4427_, 1, v___x_4426_);
v___x_22210__overap_4428_ = l_Lean_addTrace___redArg(v___x_4354_, v___x_4355_, v_toMonadRef_4356_, v___f_4357_, v___x_4419_, v___x_4427_);
lean_inc(v___y_4372_);
lean_inc_ref(v___y_4371_);
lean_inc(v___y_4370_);
lean_inc_ref(v___y_4369_);
lean_inc(v___y_4368_);
lean_inc_ref(v___y_4367_);
lean_inc(v___y_4366_);
lean_inc_ref(v___y_4365_);
lean_inc(v___y_4364_);
lean_inc(v___y_4363_);
lean_inc_ref(v___y_4362_);
v___x_4429_ = lean_apply_12(v___x_22210__overap_4428_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, lean_box(0));
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4431_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref_known(v___x_4429_, 1);
v___x_4431_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4397_, v___f_4410_, v_a_4430_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
v___y_4375_ = v___x_4431_;
goto v___jp_4374_;
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec_ref(v___f_4410_);
lean_dec_ref(v_G_4361_);
v_a_4432_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4429_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4429_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4443_; 
lean_inc_ref(v_value_4407_);
lean_dec(v_a_4405_);
lean_dec_ref(v_G_4361_);
lean_dec(v___f_4357_);
lean_dec_ref(v_toMonadRef_4356_);
lean_dec_ref(v___x_4355_);
lean_dec_ref(v___x_4354_);
lean_dec(v___x_4353_);
v___x_4443_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4407_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4455_; 
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4455_ == 0)
{
lean_object* v_unused_4456_; 
v_unused_4456_ = lean_ctor_get(v___x_4443_, 0);
lean_dec(v_unused_4456_);
v___x_4445_ = v___x_4443_;
v_isShared_4446_ = v_isSharedCheck_4455_;
goto v_resetjp_4444_;
}
else
{
lean_dec(v___x_4443_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4455_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4450_; 
v___x_4447_ = lean_box(v___x_4397_);
v___x_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 0, v___x_4448_);
v___x_4450_ = v___x_4401_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4454_, 1, v_snd_4399_);
v___x_4450_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
lean_object* v___x_4452_; 
if (v_isShared_4446_ == 0)
{
lean_ctor_set(v___x_4445_, 0, v___x_4450_);
v___x_4452_ = v___x_4445_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_del_object(v___x_4401_);
lean_dec(v_snd_4399_);
v_a_4457_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4443_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4443_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_del_object(v___x_4401_);
lean_dec(v_snd_4399_);
lean_dec_ref(v_G_4361_);
lean_dec(v___f_4357_);
lean_dec_ref(v_toMonadRef_4356_);
lean_dec_ref(v___x_4355_);
lean_dec_ref(v___x_4354_);
lean_dec(v___x_4353_);
v_a_4465_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4404_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4404_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
v___jp_4374_:
{
if (lean_obj_tag(v___y_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4388_; 
v_a_4376_ = lean_ctor_get(v___y_4375_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___y_4375_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4378_ = v___y_4375_;
v_isShared_4379_ = v_isSharedCheck_4388_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___y_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4388_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
if (lean_obj_tag(v_a_4376_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4382_; 
lean_dec_ref(v_G_4361_);
v_a_4380_ = lean_ctor_get(v_a_4376_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v_a_4376_, 1);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v_a_4380_);
v___x_4382_ = v___x_4378_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4380_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
lean_del_object(v___x_4378_);
v_a_4384_ = lean_ctor_get(v_a_4376_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v_a_4376_, 1);
v___x_4385_ = lean_unsigned_to_nat(1u);
v___x_4386_ = lean_nat_add(v_next_4358_, v___x_4385_);
lean_inc(v___y_4372_);
lean_inc_ref(v___y_4371_);
lean_inc(v___y_4370_);
lean_inc_ref(v___y_4369_);
lean_inc(v___y_4368_);
lean_inc_ref(v___y_4367_);
lean_inc(v___y_4366_);
lean_inc_ref(v___y_4365_);
lean_inc(v___y_4364_);
lean_inc(v___y_4363_);
lean_inc_ref(v___y_4362_);
v___x_4387_ = lean_apply_16(v_G_4361_, v___x_4386_, v_a_4384_, lean_box(0), lean_box(0), v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, lean_box(0));
return v___x_4387_;
}
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec_ref(v_G_4361_);
v_a_4389_ = lean_ctor_get(v___y_4375_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___y_4375_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___y_4375_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___y_4375_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4348_ = stack[0].m_obj;
lean_object* v_hypotheses_4349_ = stack[1].m_obj;
uint8_t v_cacheId_4350_ = stack[2].m_num;
lean_object* v_methods_4351_ = stack[3].m_obj;
lean_object* v_config_4352_ = stack[4].m_obj;
lean_object* v___x_4353_ = stack[5].m_obj;
lean_object* v___x_4354_ = stack[6].m_obj;
lean_object* v___x_4355_ = stack[7].m_obj;
lean_object* v_toMonadRef_4356_ = stack[8].m_obj;
lean_object* v___f_4357_ = stack[9].m_obj;
lean_object* v_next_4358_ = stack[10].m_obj;
lean_object* v_acc_4359_ = stack[11].m_obj;
lean_object* v_G_4361_ = stack[13].m_obj;
lean_object* v___y_4362_ = stack[14].m_obj;
lean_object* v___y_4363_ = stack[15].m_obj;
lean_object* v___y_4364_ = stack[16].m_obj;
lean_object* v___y_4365_ = stack[17].m_obj;
lean_object* v___y_4366_ = stack[18].m_obj;
lean_object* v___y_4367_ = stack[19].m_obj;
lean_object* v___y_4368_ = stack[20].m_obj;
lean_object* v___y_4369_ = stack[21].m_obj;
lean_object* v___y_4370_ = stack[22].m_obj;
lean_object* v___y_4371_ = stack[23].m_obj;
lean_object* v___y_4372_ = stack[24].m_obj;
lean_object* v_res_4475_;
v_res_4475_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4348_, v_hypotheses_4349_, v_cacheId_4350_, v_methods_4351_, v_config_4352_, v___x_4353_, v___x_4354_, v___x_4355_, v_toMonadRef_4356_, v___f_4357_, v_next_4358_, v_acc_4359_, lean_box(0), v_G_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
stack->m_obj
 = v_res_4475_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4476_ = _args[0];
lean_object* v_hypotheses_4477_ = _args[1];
lean_object* v_cacheId_4478_ = _args[2];
lean_object* v_methods_4479_ = _args[3];
lean_object* v_config_4480_ = _args[4];
lean_object* v___x_4481_ = _args[5];
lean_object* v___x_4482_ = _args[6];
lean_object* v___x_4483_ = _args[7];
lean_object* v_toMonadRef_4484_ = _args[8];
lean_object* v___f_4485_ = _args[9];
lean_object* v_next_4486_ = _args[10];
lean_object* v_acc_4487_ = _args[11];
lean_object* v_h_4488_ = _args[12];
lean_object* v_G_4489_ = _args[13];
lean_object* v___y_4490_ = _args[14];
lean_object* v___y_4491_ = _args[15];
lean_object* v___y_4492_ = _args[16];
lean_object* v___y_4493_ = _args[17];
lean_object* v___y_4494_ = _args[18];
lean_object* v___y_4495_ = _args[19];
lean_object* v___y_4496_ = _args[20];
lean_object* v___y_4497_ = _args[21];
lean_object* v___y_4498_ = _args[22];
lean_object* v___y_4499_ = _args[23];
lean_object* v___y_4500_ = _args[24];
lean_object* v___y_4501_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4502_; lean_object* v_res_4503_; 
v_cacheId_boxed_4502_ = lean_unbox(v_cacheId_4478_);
v_res_4503_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4476_, v_hypotheses_4477_, v_cacheId_boxed_4502_, v_methods_4479_, v_config_4480_, v___x_4481_, v___x_4482_, v___x_4483_, v_toMonadRef_4484_, v___f_4485_, v_next_4486_, v_acc_4487_, v_h_4488_, v_G_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v_next_4486_);
lean_dec_ref(v_hypotheses_4477_);
lean_dec(v___x_4476_);
return v_res_4503_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4504_, lean_object* v_methods_4505_, lean_object* v_config_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v___x_4519_; lean_object* v_toApplicative_4520_; lean_object* v_toFunctor_4521_; lean_object* v_toSeq_4522_; lean_object* v_toSeqLeft_4523_; lean_object* v_toSeqRight_4524_; lean_object* v___f_4525_; lean_object* v___f_4526_; lean_object* v___f_4527_; lean_object* v___f_4528_; lean_object* v___x_4529_; lean_object* v___f_4530_; lean_object* v___f_4531_; lean_object* v___f_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v_toApplicative_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4623_; 
v___x_4519_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4520_ = lean_ctor_get(v___x_4519_, 0);
v_toFunctor_4521_ = lean_ctor_get(v_toApplicative_4520_, 0);
v_toSeq_4522_ = lean_ctor_get(v_toApplicative_4520_, 2);
v_toSeqLeft_4523_ = lean_ctor_get(v_toApplicative_4520_, 3);
v_toSeqRight_4524_ = lean_ctor_get(v_toApplicative_4520_, 4);
v___f_4525_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4526_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4521_, 2);
v___f_4527_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4527_, 0, v_toFunctor_4521_);
v___f_4528_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4528_, 0, v_toFunctor_4521_);
v___x_4529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4529_, 0, v___f_4527_);
lean_ctor_set(v___x_4529_, 1, v___f_4528_);
lean_inc(v_toSeqRight_4524_);
v___f_4530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4530_, 0, v_toSeqRight_4524_);
lean_inc(v_toSeqLeft_4523_);
v___f_4531_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4531_, 0, v_toSeqLeft_4523_);
lean_inc(v_toSeq_4522_);
v___f_4532_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4532_, 0, v_toSeq_4522_);
v___x_4533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4529_);
lean_ctor_set(v___x_4533_, 1, v___f_4525_);
lean_ctor_set(v___x_4533_, 2, v___f_4532_);
lean_ctor_set(v___x_4533_, 3, v___f_4531_);
lean_ctor_set(v___x_4533_, 4, v___f_4530_);
v___x_4534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
lean_ctor_set(v___x_4534_, 1, v___f_4526_);
v___x_4535_ = l_StateRefT_x27_instMonad___redArg(v___x_4534_);
v_toApplicative_4536_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4623_ == 0)
{
lean_object* v_unused_4624_; 
v_unused_4624_ = lean_ctor_get(v___x_4535_, 1);
lean_dec(v_unused_4624_);
v___x_4538_ = v___x_4535_;
v_isShared_4539_ = v_isSharedCheck_4623_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_toApplicative_4536_);
lean_dec(v___x_4535_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4623_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v_toFunctor_4540_; lean_object* v_toSeq_4541_; lean_object* v_toSeqLeft_4542_; lean_object* v_toSeqRight_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4621_; 
v_toFunctor_4540_ = lean_ctor_get(v_toApplicative_4536_, 0);
v_toSeq_4541_ = lean_ctor_get(v_toApplicative_4536_, 2);
v_toSeqLeft_4542_ = lean_ctor_get(v_toApplicative_4536_, 3);
v_toSeqRight_4543_ = lean_ctor_get(v_toApplicative_4536_, 4);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_toApplicative_4536_);
if (v_isSharedCheck_4621_ == 0)
{
lean_object* v_unused_4622_; 
v_unused_4622_ = lean_ctor_get(v_toApplicative_4536_, 1);
lean_dec(v_unused_4622_);
v___x_4545_ = v_toApplicative_4536_;
v_isShared_4546_ = v_isSharedCheck_4621_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_toSeqRight_4543_);
lean_inc(v_toSeqLeft_4542_);
lean_inc(v_toSeq_4541_);
lean_inc(v_toFunctor_4540_);
lean_dec(v_toApplicative_4536_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4621_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___f_4547_; lean_object* v___f_4548_; lean_object* v___f_4549_; lean_object* v___f_4550_; lean_object* v___x_4551_; lean_object* v___f_4552_; lean_object* v___f_4553_; lean_object* v___f_4554_; lean_object* v___x_4556_; 
v___f_4547_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4548_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4540_);
v___f_4549_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4549_, 0, v_toFunctor_4540_);
v___f_4550_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4550_, 0, v_toFunctor_4540_);
v___x_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___f_4549_);
lean_ctor_set(v___x_4551_, 1, v___f_4550_);
v___f_4552_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4552_, 0, v_toSeqRight_4543_);
v___f_4553_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4553_, 0, v_toSeqLeft_4542_);
v___f_4554_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4554_, 0, v_toSeq_4541_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 4, v___f_4552_);
lean_ctor_set(v___x_4545_, 3, v___f_4553_);
lean_ctor_set(v___x_4545_, 2, v___f_4554_);
lean_ctor_set(v___x_4545_, 1, v___f_4547_);
lean_ctor_set(v___x_4545_, 0, v___x_4551_);
v___x_4556_ = v___x_4545_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4620_, 1, v___f_4547_);
lean_ctor_set(v_reuseFailAlloc_4620_, 2, v___f_4554_);
lean_ctor_set(v_reuseFailAlloc_4620_, 3, v___f_4553_);
lean_ctor_set(v_reuseFailAlloc_4620_, 4, v___f_4552_);
v___x_4556_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
lean_object* v___x_4558_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 1, v___f_4548_);
lean_ctor_set(v___x_4538_, 0, v___x_4556_);
v___x_4558_ = v___x_4538_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4556_);
lean_ctor_set(v_reuseFailAlloc_4619_, 1, v___f_4548_);
v___x_4558_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v_toMonadRef_4567_; lean_object* v___f_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v_hypotheses_4571_; lean_object* v___x_4572_; lean_object* v_newHyps_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___f_4577_; lean_object* v___x_4578_; lean_object* v___x_22108__overap_4579_; lean_object* v___x_4580_; 
v___x_4559_ = l_StateRefT_x27_instMonad___redArg(v___x_4558_);
v___x_4560_ = l_ReaderT_instMonad___redArg(v___x_4559_);
v___x_4561_ = l_StateRefT_x27_instMonad___redArg(v___x_4560_);
v___x_4562_ = l_ReaderT_instMonad___redArg(v___x_4561_);
v___x_4563_ = l_ReaderT_instMonad___redArg(v___x_4562_);
v___x_4564_ = l_StateRefT_x27_instMonad___redArg(v___x_4563_);
v___x_4565_ = l_ReaderT_instMonad___redArg(v___x_4564_);
v___x_4566_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4567_ = lean_ctor_get(v___x_4566_, 0);
v___f_4568_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4569_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4570_ = lean_st_ref_get(v_a_4508_);
v_hypotheses_4571_ = lean_ctor_get(v___x_4570_, 3);
lean_inc_ref(v_hypotheses_4571_);
lean_dec(v___x_4570_);
v___x_4572_ = lean_array_get_size(v_hypotheses_4571_);
v_newHyps_4573_ = lean_mk_empty_array_with_capacity(v___x_4572_);
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = lean_box(0);
v___x_4576_ = lean_box(v_cacheId_4504_);
lean_inc_ref(v_toMonadRef_4567_);
v___f_4577_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4577_, 0, v___x_4572_);
lean_closure_set(v___f_4577_, 1, v_hypotheses_4571_);
lean_closure_set(v___f_4577_, 2, v___x_4576_);
lean_closure_set(v___f_4577_, 3, v_methods_4505_);
lean_closure_set(v___f_4577_, 4, v_config_4506_);
lean_closure_set(v___f_4577_, 5, v___x_4575_);
lean_closure_set(v___f_4577_, 6, v___x_4565_);
lean_closure_set(v___f_4577_, 7, v___x_4569_);
lean_closure_set(v___f_4577_, 8, v_toMonadRef_4567_);
lean_closure_set(v___f_4577_, 9, v___f_4568_);
v___x_4578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4575_);
lean_ctor_set(v___x_4578_, 1, v_newHyps_4573_);
v___x_22108__overap_4579_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4577_, v___x_4574_, v___x_4578_, lean_box(0));
lean_inc(v_a_4517_);
lean_inc_ref(v_a_4516_);
lean_inc(v_a_4515_);
lean_inc_ref(v_a_4514_);
lean_inc(v_a_4513_);
lean_inc_ref(v_a_4512_);
lean_inc(v_a_4511_);
lean_inc_ref(v_a_4510_);
lean_inc(v_a_4509_);
lean_inc(v_a_4508_);
lean_inc_ref(v_a_4507_);
v___x_4580_ = lean_apply_12(v___x_22108__overap_4579_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, lean_box(0));
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4610_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4610_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4610_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v_fst_4585_; 
v_fst_4585_ = lean_ctor_get(v_a_4581_, 0);
if (lean_obj_tag(v_fst_4585_) == 0)
{
lean_object* v_snd_4586_; lean_object* v___x_4587_; lean_object* v_caches_4588_; lean_object* v_typeAnalysis_4589_; lean_object* v_target_4590_; uint8_t v_didChange_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4604_; 
v_snd_4586_ = lean_ctor_get(v_a_4581_, 1);
lean_inc(v_snd_4586_);
lean_dec(v_a_4581_);
v___x_4587_ = lean_st_ref_take(v_a_4508_);
v_caches_4588_ = lean_ctor_get(v___x_4587_, 0);
v_typeAnalysis_4589_ = lean_ctor_get(v___x_4587_, 1);
v_target_4590_ = lean_ctor_get(v___x_4587_, 2);
v_didChange_4591_ = lean_ctor_get_uint8(v___x_4587_, sizeof(void*)*4);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4604_ == 0)
{
lean_object* v_unused_4605_; 
v_unused_4605_ = lean_ctor_get(v___x_4587_, 3);
lean_dec(v_unused_4605_);
v___x_4593_ = v___x_4587_;
v_isShared_4594_ = v_isSharedCheck_4604_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_target_4590_);
lean_inc(v_typeAnalysis_4589_);
lean_inc(v_caches_4588_);
lean_dec(v___x_4587_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4604_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 3, v_snd_4586_);
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_caches_4588_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v_typeAnalysis_4589_);
lean_ctor_set(v_reuseFailAlloc_4603_, 2, v_target_4590_);
lean_ctor_set(v_reuseFailAlloc_4603_, 3, v_snd_4586_);
lean_ctor_set_uint8(v_reuseFailAlloc_4603_, sizeof(void*)*4, v_didChange_4591_);
v___x_4596_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4597_; uint8_t v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4601_; 
v___x_4597_ = lean_st_ref_put(v_a_4508_, v___x_4596_);
v___x_4598_ = 0;
v___x_4599_ = lean_box(v___x_4598_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4599_);
v___x_4601_ = v___x_4583_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
else
{
lean_object* v_val_4606_; lean_object* v___x_4608_; 
lean_inc_ref(v_fst_4585_);
lean_dec(v_a_4581_);
v_val_4606_ = lean_ctor_get(v_fst_4585_, 0);
lean_inc(v_val_4606_);
lean_dec_ref_known(v_fst_4585_, 1);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v_val_4606_);
v___x_4608_ = v___x_4583_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_val_4606_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
v_a_4611_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4580_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4580_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps_0interp(lean_interpreter_value* stack)
{
uint8_t v_cacheId_4504_ = stack[0].m_num;
lean_object* v_methods_4505_ = stack[1].m_obj;
lean_object* v_config_4506_ = stack[2].m_obj;
lean_object* v_a_4507_ = stack[3].m_obj;
lean_object* v_a_4508_ = stack[4].m_obj;
lean_object* v_a_4509_ = stack[5].m_obj;
lean_object* v_a_4510_ = stack[6].m_obj;
lean_object* v_a_4511_ = stack[7].m_obj;
lean_object* v_a_4512_ = stack[8].m_obj;
lean_object* v_a_4513_ = stack[9].m_obj;
lean_object* v_a_4514_ = stack[10].m_obj;
lean_object* v_a_4515_ = stack[11].m_obj;
lean_object* v_a_4516_ = stack[12].m_obj;
lean_object* v_a_4517_ = stack[13].m_obj;
lean_object* v_res_4625_;
v_res_4625_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_4504_, v_methods_4505_, v_config_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
stack->m_obj
 = v_res_4625_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_4626_, lean_object* v_methods_4627_, lean_object* v_config_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
uint8_t v_cacheId_boxed_4641_; lean_object* v_res_4642_; 
v_cacheId_boxed_4641_ = lean_unbox(v_cacheId_4626_);
v_res_4642_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_4641_, v_methods_4627_, v_config_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_);
lean_dec(v_a_4639_);
lean_dec_ref(v_a_4638_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
lean_dec(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
return v_res_4642_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_4643_, lean_object* v_hypotheses_4644_, uint8_t v_cacheId_4645_, lean_object* v_methods_4646_, lean_object* v_config_4647_, lean_object* v___x_4648_, lean_object* v___x_4649_, lean_object* v___x_4650_, lean_object* v_toMonadRef_4651_, lean_object* v___f_4652_, lean_object* v_next_4653_, lean_object* v_acc_4654_, lean_object* v_h_4655_, lean_object* v_G_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v___y_4670_; uint8_t v___x_4692_; 
v___x_4692_ = lean_nat_dec_lt(v_next_4653_, v___x_4643_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; 
lean_dec_ref(v_G_4656_);
lean_dec(v___f_4652_);
lean_dec_ref(v_toMonadRef_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4649_);
lean_dec(v___x_4648_);
lean_dec_ref(v_config_4647_);
lean_dec_ref(v_methods_4646_);
v___x_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4693_, 0, v_acc_4654_);
return v___x_4693_;
}
else
{
lean_object* v_snd_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4768_; 
v_snd_4694_ = lean_ctor_get(v_acc_4654_, 1);
v_isSharedCheck_4768_ = !lean_is_exclusive(v_acc_4654_);
if (v_isSharedCheck_4768_ == 0)
{
lean_object* v_unused_4769_; 
v_unused_4769_ = lean_ctor_get(v_acc_4654_, 0);
lean_dec(v_unused_4769_);
v___x_4696_ = v_acc_4654_;
v_isShared_4697_ = v_isSharedCheck_4768_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_snd_4694_);
lean_dec(v_acc_4654_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4768_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4698_ = lean_array_fget_borrowed(v_hypotheses_4644_, v_next_4653_);
lean_inc(v___x_4698_);
v___x_4699_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4645_, v_methods_4646_, v_config_4647_, v___x_4698_, v___y_4658_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v_type_4701_; lean_object* v_value_4702_; uint8_t v___x_4703_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
lean_inc(v_a_4700_);
lean_dec_ref_known(v___x_4699_, 1);
v_type_4701_ = lean_ctor_get(v_a_4700_, 1);
v_value_4702_ = lean_ctor_get(v_a_4700_, 2);
lean_inc_ref(v_type_4701_);
v___x_4703_ = l_Lean_Expr_isFalse(v_type_4701_);
if (v___x_4703_ == 0)
{
lean_object* v_type_4704_; lean_object* v___f_4705_; uint8_t v___x_4735_; 
lean_del_object(v___x_4696_);
v_type_4704_ = lean_ctor_get(v___x_4698_, 1);
lean_inc(v___x_4648_);
lean_inc(v_a_4700_);
lean_inc(v_snd_4694_);
v___f_4705_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4705_, 0, v_snd_4694_);
lean_closure_set(v___f_4705_, 1, v_a_4700_);
lean_closure_set(v___f_4705_, 2, v___x_4648_);
v___x_4735_ = lean_expr_eqv(v_type_4704_, v_type_4701_);
if (v___x_4735_ == 0)
{
lean_inc_ref(v_type_4701_);
lean_dec(v_a_4700_);
lean_dec(v_snd_4694_);
lean_dec(v___x_4648_);
goto v___jp_4709_;
}
else
{
if (v___x_4703_ == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
lean_dec_ref(v___f_4705_);
lean_dec(v___f_4652_);
lean_dec_ref(v_toMonadRef_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4649_);
v___x_4736_ = lean_box(0);
v___x_4737_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4694_, v_a_4700_, v___x_4648_, v___x_4736_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
v___y_4670_ = v___x_4737_;
goto v___jp_4669_;
}
else
{
lean_inc_ref(v_type_4701_);
lean_dec(v_a_4700_);
lean_dec(v_snd_4694_);
lean_dec(v___x_4648_);
goto v___jp_4709_;
}
}
v___jp_4706_:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = lean_box(0);
v___x_4708_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4692_, v___f_4705_, v___x_4707_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
v___y_4670_ = v___x_4708_;
goto v___jp_4669_;
}
v___jp_4709_:
{
lean_object* v_toCold_4710_; lean_object* v_options_4711_; uint8_t v_hasTrace_4712_; 
v_toCold_4710_ = lean_ctor_get(v___y_4666_, 0);
v_options_4711_ = lean_ctor_get(v_toCold_4710_, 2);
v_hasTrace_4712_ = lean_ctor_get_uint8(v_options_4711_, sizeof(void*)*1);
if (v_hasTrace_4712_ == 0)
{
lean_dec_ref(v_type_4701_);
lean_dec(v___f_4652_);
lean_dec_ref(v_toMonadRef_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4649_);
goto v___jp_4706_;
}
else
{
lean_object* v_inheritedTraceOptions_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; uint8_t v___x_4716_; 
v_inheritedTraceOptions_4713_ = lean_ctor_get(v_toCold_4710_, 11);
v___x_4714_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4715_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4713_, v_options_4711_, v___x_4715_);
if (v___x_4716_ == 0)
{
lean_dec_ref(v_type_4701_);
lean_dec(v___f_4652_);
lean_dec_ref(v_toMonadRef_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4649_);
goto v___jp_4706_;
}
else
{
lean_object* v_type_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_22210__overap_4723_; lean_object* v___x_4724_; 
v_type_4717_ = lean_ctor_get(v___x_4698_, 1);
lean_inc_ref(v_type_4717_);
v___x_4718_ = l_Lean_MessageData_ofExpr(v_type_4717_);
v___x_4719_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4718_);
lean_ctor_set(v___x_4720_, 1, v___x_4719_);
v___x_4721_ = l_Lean_MessageData_ofExpr(v_type_4701_);
v___x_4722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4720_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
v___x_22210__overap_4723_ = l_Lean_addTrace___redArg(v___x_4649_, v___x_4650_, v_toMonadRef_4651_, v___f_4652_, v___x_4714_, v___x_4722_);
lean_inc(v___y_4667_);
lean_inc_ref(v___y_4666_);
lean_inc(v___y_4665_);
lean_inc_ref(v___y_4664_);
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
lean_inc(v___y_4659_);
lean_inc(v___y_4658_);
lean_inc_ref(v___y_4657_);
v___x_4724_ = lean_apply_12(v___x_22210__overap_4723_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, lean_box(0));
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4726_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
lean_inc(v_a_4725_);
lean_dec_ref_known(v___x_4724_, 1);
v___x_4726_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4692_, v___f_4705_, v_a_4725_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
v___y_4670_ = v___x_4726_;
goto v___jp_4669_;
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
lean_dec_ref(v___f_4705_);
lean_dec_ref(v_G_4656_);
v_a_4727_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4724_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4724_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4738_; 
lean_inc_ref(v_value_4702_);
lean_dec(v_a_4700_);
lean_dec_ref(v_G_4656_);
lean_dec(v___f_4652_);
lean_dec_ref(v_toMonadRef_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4649_);
lean_dec(v___x_4648_);
v___x_4738_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4702_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4750_; 
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; 
v_unused_4751_ = lean_ctor_get(v___x_4738_, 0);
lean_dec(v_unused_4751_);
v___x_4740_ = v___x_4738_;
v_isShared_4741_ = v_isSharedCheck_4750_;
goto v_resetjp_4739_;
}
else
{
lean_dec(v___x_4738_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4750_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4745_; 
v___x_4742_ = lean_box(v___x_4692_);
v___x_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4742_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v___x_4743_);
v___x_4745_ = v___x_4696_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4749_, 1, v_snd_4694_);
v___x_4745_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4747_; 
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 0, v___x_4745_);
v___x_4747_ = v___x_4740_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4745_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_del_object(v___x_4696_);
lean_dec(v_snd_4694_);
v_a_4752_ = lean_ctor_get(v___x_4738_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4738_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4738_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_del_object(v___x_4696_);
lean_dec(v_snd_4694_);
lean_dec_ref(v_G_4656_);
lean_dec(v___f_4652_);
lean_dec_ref(v_toMonadRef_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4649_);
lean_dec(v___x_4648_);
v_a_4760_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4699_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4699_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
}
}
v___jp_4669_:
{
if (lean_obj_tag(v___y_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4683_; 
v_a_4671_ = lean_ctor_get(v___y_4670_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___y_4670_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4673_ = v___y_4670_;
v_isShared_4674_ = v_isSharedCheck_4683_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___y_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4683_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
if (lean_obj_tag(v_a_4671_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4677_; 
lean_dec_ref(v_G_4656_);
v_a_4675_ = lean_ctor_get(v_a_4671_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v_a_4671_, 1);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v_a_4675_);
v___x_4677_ = v___x_4673_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4675_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
lean_del_object(v___x_4673_);
v_a_4679_ = lean_ctor_get(v_a_4671_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v_a_4671_, 1);
v___x_4680_ = lean_unsigned_to_nat(1u);
v___x_4681_ = lean_nat_add(v_next_4653_, v___x_4680_);
lean_inc(v___y_4667_);
lean_inc_ref(v___y_4666_);
lean_inc(v___y_4665_);
lean_inc_ref(v___y_4664_);
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
lean_inc(v___y_4659_);
lean_inc(v___y_4658_);
lean_inc_ref(v___y_4657_);
v___x_4682_ = lean_apply_16(v_G_4656_, v___x_4681_, v_a_4679_, lean_box(0), lean_box(0), v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, lean_box(0));
return v___x_4682_;
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_dec_ref(v_G_4656_);
v_a_4684_ = lean_ctor_get(v___y_4670_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___y_4670_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___y_4670_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___y_4670_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4643_ = stack[0].m_obj;
lean_object* v_hypotheses_4644_ = stack[1].m_obj;
uint8_t v_cacheId_4645_ = stack[2].m_num;
lean_object* v_methods_4646_ = stack[3].m_obj;
lean_object* v_config_4647_ = stack[4].m_obj;
lean_object* v___x_4648_ = stack[5].m_obj;
lean_object* v___x_4649_ = stack[6].m_obj;
lean_object* v___x_4650_ = stack[7].m_obj;
lean_object* v_toMonadRef_4651_ = stack[8].m_obj;
lean_object* v___f_4652_ = stack[9].m_obj;
lean_object* v_next_4653_ = stack[10].m_obj;
lean_object* v_acc_4654_ = stack[11].m_obj;
lean_object* v_G_4656_ = stack[13].m_obj;
lean_object* v___y_4657_ = stack[14].m_obj;
lean_object* v___y_4658_ = stack[15].m_obj;
lean_object* v___y_4659_ = stack[16].m_obj;
lean_object* v___y_4660_ = stack[17].m_obj;
lean_object* v___y_4661_ = stack[18].m_obj;
lean_object* v___y_4662_ = stack[19].m_obj;
lean_object* v___y_4663_ = stack[20].m_obj;
lean_object* v___y_4664_ = stack[21].m_obj;
lean_object* v___y_4665_ = stack[22].m_obj;
lean_object* v___y_4666_ = stack[23].m_obj;
lean_object* v___y_4667_ = stack[24].m_obj;
lean_object* v_res_4770_;
v_res_4770_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4643_, v_hypotheses_4644_, v_cacheId_4645_, v_methods_4646_, v_config_4647_, v___x_4648_, v___x_4649_, v___x_4650_, v_toMonadRef_4651_, v___f_4652_, v_next_4653_, v_acc_4654_, lean_box(0), v_G_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
stack->m_obj
 = v_res_4770_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4771_ = _args[0];
lean_object* v_hypotheses_4772_ = _args[1];
lean_object* v_cacheId_4773_ = _args[2];
lean_object* v_methods_4774_ = _args[3];
lean_object* v_config_4775_ = _args[4];
lean_object* v___x_4776_ = _args[5];
lean_object* v___x_4777_ = _args[6];
lean_object* v___x_4778_ = _args[7];
lean_object* v_toMonadRef_4779_ = _args[8];
lean_object* v___f_4780_ = _args[9];
lean_object* v_next_4781_ = _args[10];
lean_object* v_acc_4782_ = _args[11];
lean_object* v_h_4783_ = _args[12];
lean_object* v_G_4784_ = _args[13];
lean_object* v___y_4785_ = _args[14];
lean_object* v___y_4786_ = _args[15];
lean_object* v___y_4787_ = _args[16];
lean_object* v___y_4788_ = _args[17];
lean_object* v___y_4789_ = _args[18];
lean_object* v___y_4790_ = _args[19];
lean_object* v___y_4791_ = _args[20];
lean_object* v___y_4792_ = _args[21];
lean_object* v___y_4793_ = _args[22];
lean_object* v___y_4794_ = _args[23];
lean_object* v___y_4795_ = _args[24];
lean_object* v___y_4796_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4797_; lean_object* v_res_4798_; 
v_cacheId_boxed_4797_ = lean_unbox(v_cacheId_4773_);
v_res_4798_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4771_, v_hypotheses_4772_, v_cacheId_boxed_4797_, v_methods_4774_, v_config_4775_, v___x_4776_, v___x_4777_, v___x_4778_, v_toMonadRef_4779_, v___f_4780_, v_next_4781_, v_acc_4782_, v_h_4783_, v_G_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
lean_dec(v___y_4791_);
lean_dec_ref(v___y_4790_);
lean_dec(v___y_4789_);
lean_dec_ref(v___y_4788_);
lean_dec(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v_next_4781_);
lean_dec_ref(v_hypotheses_4772_);
lean_dec(v___x_4771_);
return v_res_4798_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4799_, lean_object* v_methods_4800_, lean_object* v_config_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v___x_4814_; lean_object* v_toApplicative_4815_; lean_object* v_toFunctor_4816_; lean_object* v_toSeq_4817_; lean_object* v_toSeqLeft_4818_; lean_object* v_toSeqRight_4819_; lean_object* v___f_4820_; lean_object* v___f_4821_; lean_object* v___f_4822_; lean_object* v___f_4823_; lean_object* v___x_4824_; lean_object* v___f_4825_; lean_object* v___f_4826_; lean_object* v___f_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v_toApplicative_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4918_; 
v___x_4814_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4815_ = lean_ctor_get(v___x_4814_, 0);
v_toFunctor_4816_ = lean_ctor_get(v_toApplicative_4815_, 0);
v_toSeq_4817_ = lean_ctor_get(v_toApplicative_4815_, 2);
v_toSeqLeft_4818_ = lean_ctor_get(v_toApplicative_4815_, 3);
v_toSeqRight_4819_ = lean_ctor_get(v_toApplicative_4815_, 4);
v___f_4820_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4821_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4816_, 2);
v___f_4822_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4822_, 0, v_toFunctor_4816_);
v___f_4823_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4823_, 0, v_toFunctor_4816_);
v___x_4824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___f_4822_);
lean_ctor_set(v___x_4824_, 1, v___f_4823_);
lean_inc(v_toSeqRight_4819_);
v___f_4825_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4825_, 0, v_toSeqRight_4819_);
lean_inc(v_toSeqLeft_4818_);
v___f_4826_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4826_, 0, v_toSeqLeft_4818_);
lean_inc(v_toSeq_4817_);
v___f_4827_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4827_, 0, v_toSeq_4817_);
v___x_4828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4824_);
lean_ctor_set(v___x_4828_, 1, v___f_4820_);
lean_ctor_set(v___x_4828_, 2, v___f_4827_);
lean_ctor_set(v___x_4828_, 3, v___f_4826_);
lean_ctor_set(v___x_4828_, 4, v___f_4825_);
v___x_4829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
lean_ctor_set(v___x_4829_, 1, v___f_4821_);
v___x_4830_ = l_StateRefT_x27_instMonad___redArg(v___x_4829_);
v_toApplicative_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4918_ == 0)
{
lean_object* v_unused_4919_; 
v_unused_4919_ = lean_ctor_get(v___x_4830_, 1);
lean_dec(v_unused_4919_);
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4918_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_toApplicative_4831_);
lean_dec(v___x_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4918_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v_toFunctor_4835_; lean_object* v_toSeq_4836_; lean_object* v_toSeqLeft_4837_; lean_object* v_toSeqRight_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4916_; 
v_toFunctor_4835_ = lean_ctor_get(v_toApplicative_4831_, 0);
v_toSeq_4836_ = lean_ctor_get(v_toApplicative_4831_, 2);
v_toSeqLeft_4837_ = lean_ctor_get(v_toApplicative_4831_, 3);
v_toSeqRight_4838_ = lean_ctor_get(v_toApplicative_4831_, 4);
v_isSharedCheck_4916_ = !lean_is_exclusive(v_toApplicative_4831_);
if (v_isSharedCheck_4916_ == 0)
{
lean_object* v_unused_4917_; 
v_unused_4917_ = lean_ctor_get(v_toApplicative_4831_, 1);
lean_dec(v_unused_4917_);
v___x_4840_ = v_toApplicative_4831_;
v_isShared_4841_ = v_isSharedCheck_4916_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_toSeqRight_4838_);
lean_inc(v_toSeqLeft_4837_);
lean_inc(v_toSeq_4836_);
lean_inc(v_toFunctor_4835_);
lean_dec(v_toApplicative_4831_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4916_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___f_4842_; lean_object* v___f_4843_; lean_object* v___f_4844_; lean_object* v___f_4845_; lean_object* v___x_4846_; lean_object* v___f_4847_; lean_object* v___f_4848_; lean_object* v___f_4849_; lean_object* v___x_4851_; 
v___f_4842_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4843_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4835_);
v___f_4844_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4844_, 0, v_toFunctor_4835_);
v___f_4845_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4845_, 0, v_toFunctor_4835_);
v___x_4846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___f_4844_);
lean_ctor_set(v___x_4846_, 1, v___f_4845_);
v___f_4847_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4847_, 0, v_toSeqRight_4838_);
v___f_4848_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4848_, 0, v_toSeqLeft_4837_);
v___f_4849_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4849_, 0, v_toSeq_4836_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 4, v___f_4847_);
lean_ctor_set(v___x_4840_, 3, v___f_4848_);
lean_ctor_set(v___x_4840_, 2, v___f_4849_);
lean_ctor_set(v___x_4840_, 1, v___f_4842_);
lean_ctor_set(v___x_4840_, 0, v___x_4846_);
v___x_4851_ = v___x_4840_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v___x_4846_);
lean_ctor_set(v_reuseFailAlloc_4915_, 1, v___f_4842_);
lean_ctor_set(v_reuseFailAlloc_4915_, 2, v___f_4849_);
lean_ctor_set(v_reuseFailAlloc_4915_, 3, v___f_4848_);
lean_ctor_set(v_reuseFailAlloc_4915_, 4, v___f_4847_);
v___x_4851_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
lean_object* v___x_4853_; 
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 1, v___f_4843_);
lean_ctor_set(v___x_4833_, 0, v___x_4851_);
v___x_4853_ = v___x_4833_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4914_, 1, v___f_4843_);
v___x_4853_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v_toMonadRef_4862_; lean_object* v___f_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v_hypotheses_4866_; lean_object* v___x_4867_; lean_object* v_newHyps_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___f_4872_; lean_object* v___x_4873_; lean_object* v___x_22108__overap_4874_; lean_object* v___x_4875_; 
v___x_4854_ = l_StateRefT_x27_instMonad___redArg(v___x_4853_);
v___x_4855_ = l_ReaderT_instMonad___redArg(v___x_4854_);
v___x_4856_ = l_StateRefT_x27_instMonad___redArg(v___x_4855_);
v___x_4857_ = l_ReaderT_instMonad___redArg(v___x_4856_);
v___x_4858_ = l_ReaderT_instMonad___redArg(v___x_4857_);
v___x_4859_ = l_StateRefT_x27_instMonad___redArg(v___x_4858_);
v___x_4860_ = l_ReaderT_instMonad___redArg(v___x_4859_);
v___x_4861_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4862_ = lean_ctor_get(v___x_4861_, 0);
v___f_4863_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4864_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4865_ = lean_st_ref_get(v_a_4803_);
v_hypotheses_4866_ = lean_ctor_get(v___x_4865_, 3);
lean_inc_ref(v_hypotheses_4866_);
lean_dec(v___x_4865_);
v___x_4867_ = lean_array_get_size(v_hypotheses_4866_);
v_newHyps_4868_ = lean_mk_empty_array_with_capacity(v___x_4867_);
v___x_4869_ = lean_unsigned_to_nat(0u);
v___x_4870_ = lean_box(0);
v___x_4871_ = lean_box(v_cacheId_4799_);
lean_inc_ref(v_toMonadRef_4862_);
v___f_4872_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4872_, 0, v___x_4867_);
lean_closure_set(v___f_4872_, 1, v_hypotheses_4866_);
lean_closure_set(v___f_4872_, 2, v___x_4871_);
lean_closure_set(v___f_4872_, 3, v_methods_4800_);
lean_closure_set(v___f_4872_, 4, v_config_4801_);
lean_closure_set(v___f_4872_, 5, v___x_4870_);
lean_closure_set(v___f_4872_, 6, v___x_4860_);
lean_closure_set(v___f_4872_, 7, v___x_4864_);
lean_closure_set(v___f_4872_, 8, v_toMonadRef_4862_);
lean_closure_set(v___f_4872_, 9, v___f_4863_);
v___x_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4870_);
lean_ctor_set(v___x_4873_, 1, v_newHyps_4868_);
v___x_22108__overap_4874_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4872_, v___x_4869_, v___x_4873_, lean_box(0));
lean_inc(v_a_4812_);
lean_inc_ref(v_a_4811_);
lean_inc(v_a_4810_);
lean_inc_ref(v_a_4809_);
lean_inc(v_a_4808_);
lean_inc_ref(v_a_4807_);
lean_inc(v_a_4806_);
lean_inc_ref(v_a_4805_);
lean_inc(v_a_4804_);
lean_inc(v_a_4803_);
lean_inc_ref(v_a_4802_);
v___x_4875_ = lean_apply_12(v___x_22108__overap_4874_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, lean_box(0));
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4905_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4878_ = v___x_4875_;
v_isShared_4879_ = v_isSharedCheck_4905_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4875_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4905_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v_fst_4880_; 
v_fst_4880_ = lean_ctor_get(v_a_4876_, 0);
if (lean_obj_tag(v_fst_4880_) == 0)
{
lean_object* v_snd_4881_; lean_object* v___x_4882_; lean_object* v_caches_4883_; lean_object* v_typeAnalysis_4884_; lean_object* v_target_4885_; uint8_t v_didChange_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4899_; 
v_snd_4881_ = lean_ctor_get(v_a_4876_, 1);
lean_inc(v_snd_4881_);
lean_dec(v_a_4876_);
v___x_4882_ = lean_st_ref_take(v_a_4803_);
v_caches_4883_ = lean_ctor_get(v___x_4882_, 0);
v_typeAnalysis_4884_ = lean_ctor_get(v___x_4882_, 1);
v_target_4885_ = lean_ctor_get(v___x_4882_, 2);
v_didChange_4886_ = lean_ctor_get_uint8(v___x_4882_, sizeof(void*)*4);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; 
v_unused_4900_ = lean_ctor_get(v___x_4882_, 3);
lean_dec(v_unused_4900_);
v___x_4888_ = v___x_4882_;
v_isShared_4889_ = v_isSharedCheck_4899_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_target_4885_);
lean_inc(v_typeAnalysis_4884_);
lean_inc(v_caches_4883_);
lean_dec(v___x_4882_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4899_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 3, v_snd_4881_);
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_caches_4883_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v_typeAnalysis_4884_);
lean_ctor_set(v_reuseFailAlloc_4898_, 2, v_target_4885_);
lean_ctor_set(v_reuseFailAlloc_4898_, 3, v_snd_4881_);
lean_ctor_set_uint8(v_reuseFailAlloc_4898_, sizeof(void*)*4, v_didChange_4886_);
v___x_4891_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
lean_object* v___x_4892_; uint8_t v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4896_; 
v___x_4892_ = lean_st_ref_put(v_a_4803_, v___x_4891_);
v___x_4893_ = 0;
v___x_4894_ = lean_box(v___x_4893_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4894_);
v___x_4896_ = v___x_4878_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v___x_4894_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
else
{
lean_object* v_val_4901_; lean_object* v___x_4903_; 
lean_inc_ref(v_fst_4880_);
lean_dec(v_a_4876_);
v_val_4901_ = lean_ctor_get(v_fst_4880_, 0);
lean_inc(v_val_4901_);
lean_dec_ref_known(v_fst_4880_, 1);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v_val_4901_);
v___x_4903_ = v___x_4878_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_val_4901_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4913_; 
v_a_4906_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4908_ = v___x_4875_;
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4875_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4911_; 
if (v_isShared_4909_ == 0)
{
v___x_4911_ = v___x_4908_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_a_4906_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps_0interp(lean_interpreter_value* stack)
{
uint8_t v_cacheId_4799_ = stack[0].m_num;
lean_object* v_methods_4800_ = stack[1].m_obj;
lean_object* v_config_4801_ = stack[2].m_obj;
lean_object* v_a_4802_ = stack[3].m_obj;
lean_object* v_a_4803_ = stack[4].m_obj;
lean_object* v_a_4804_ = stack[5].m_obj;
lean_object* v_a_4805_ = stack[6].m_obj;
lean_object* v_a_4806_ = stack[7].m_obj;
lean_object* v_a_4807_ = stack[8].m_obj;
lean_object* v_a_4808_ = stack[9].m_obj;
lean_object* v_a_4809_ = stack[10].m_obj;
lean_object* v_a_4810_ = stack[11].m_obj;
lean_object* v_a_4811_ = stack[12].m_obj;
lean_object* v_a_4812_ = stack[13].m_obj;
lean_object* v_res_4920_;
v_res_4920_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_4799_, v_methods_4800_, v_config_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
stack->m_obj
 = v_res_4920_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4921_, lean_object* v_methods_4922_, lean_object* v_config_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_){
_start:
{
uint8_t v_cacheId_boxed_4936_; lean_object* v_res_4937_; 
v_cacheId_boxed_4936_ = lean_unbox(v_cacheId_4921_);
v_res_4937_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4936_, v_methods_4922_, v_config_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
lean_dec(v_a_4934_);
lean_dec_ref(v_a_4933_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec(v_a_4925_);
lean_dec_ref(v_a_4924_);
return v_res_4937_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v___x_4944_; lean_object* v_env_4945_; uint8_t v___x_4946_; lean_object* v_env_4947_; lean_object* v___x_4948_; lean_object* v_toCold_4949_; lean_object* v_mctx_4950_; lean_object* v_lctx_4951_; lean_object* v_options_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4944_ = lean_st_ref_get(v___y_4942_);
v_env_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc_ref(v_env_4945_);
lean_dec(v___x_4944_);
v___x_4946_ = 0;
v_env_4947_ = l_Lean_Environment_setRecordingDeps(v_env_4945_, v___x_4946_);
v___x_4948_ = lean_st_ref_get(v___y_4940_);
v_toCold_4949_ = lean_ctor_get(v___y_4941_, 0);
v_mctx_4950_ = lean_ctor_get(v___x_4948_, 0);
lean_inc_ref(v_mctx_4950_);
lean_dec(v___x_4948_);
v_lctx_4951_ = lean_ctor_get(v___y_4939_, 2);
v_options_4952_ = lean_ctor_get(v_toCold_4949_, 2);
lean_inc_ref(v_options_4952_);
lean_inc_ref(v_lctx_4951_);
v___x_4953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4953_, 0, v_env_4947_);
lean_ctor_set(v___x_4953_, 1, v_mctx_4950_);
lean_ctor_set(v___x_4953_, 2, v_lctx_4951_);
lean_ctor_set(v___x_4953_, 3, v_options_4952_);
v___x_4954_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
lean_ctor_set(v___x_4954_, 1, v_msgData_4938_);
v___x_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
return v___x_4955_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4938_ = stack[0].m_obj;
lean_object* v___y_4939_ = stack[1].m_obj;
lean_object* v___y_4940_ = stack[2].m_obj;
lean_object* v___y_4941_ = stack[3].m_obj;
lean_object* v___y_4942_ = stack[4].m_obj;
lean_object* v_res_4956_;
v_res_4956_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
stack->m_obj
 = v_res_4956_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
return v_res_4963_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4964_; double v___x_4965_; 
v___x_4964_ = lean_unsigned_to_nat(0u);
v___x_4965_ = lean_float_of_nat(v___x_4964_);
return v___x_4965_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4969_, lean_object* v_msg_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v_ref_4976_; lean_object* v___x_4977_; lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_5023_; 
v_ref_4976_ = lean_ctor_get(v___y_4973_, 2);
v___x_4977_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_4980_ = v___x_4977_;
v_isShared_4981_ = v_isSharedCheck_5023_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4977_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_5023_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4982_; lean_object* v_traceState_4983_; lean_object* v_env_4984_; lean_object* v_nextMacroScope_4985_; lean_object* v_ngen_4986_; lean_object* v_auxDeclNGen_4987_; lean_object* v_cache_4988_; lean_object* v_recordedDeps_4989_; lean_object* v_messages_4990_; lean_object* v_infoState_4991_; lean_object* v_snapshotTasks_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5022_; 
v___x_4982_ = lean_st_ref_take(v___y_4974_);
v_traceState_4983_ = lean_ctor_get(v___x_4982_, 4);
v_env_4984_ = lean_ctor_get(v___x_4982_, 0);
v_nextMacroScope_4985_ = lean_ctor_get(v___x_4982_, 1);
v_ngen_4986_ = lean_ctor_get(v___x_4982_, 2);
v_auxDeclNGen_4987_ = lean_ctor_get(v___x_4982_, 3);
v_cache_4988_ = lean_ctor_get(v___x_4982_, 5);
v_recordedDeps_4989_ = lean_ctor_get(v___x_4982_, 6);
v_messages_4990_ = lean_ctor_get(v___x_4982_, 7);
v_infoState_4991_ = lean_ctor_get(v___x_4982_, 8);
v_snapshotTasks_4992_ = lean_ctor_get(v___x_4982_, 9);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_4994_ = v___x_4982_;
v_isShared_4995_ = v_isSharedCheck_5022_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_snapshotTasks_4992_);
lean_inc(v_infoState_4991_);
lean_inc(v_messages_4990_);
lean_inc(v_recordedDeps_4989_);
lean_inc(v_cache_4988_);
lean_inc(v_traceState_4983_);
lean_inc(v_auxDeclNGen_4987_);
lean_inc(v_ngen_4986_);
lean_inc(v_nextMacroScope_4985_);
lean_inc(v_env_4984_);
lean_dec(v___x_4982_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5022_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
uint64_t v_tid_4996_; lean_object* v_traces_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5021_; 
v_tid_4996_ = lean_ctor_get_uint64(v_traceState_4983_, sizeof(void*)*1);
v_traces_4997_ = lean_ctor_get(v_traceState_4983_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v_traceState_4983_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_4999_ = v_traceState_4983_;
v_isShared_5000_ = v_isSharedCheck_5021_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_traces_4997_);
lean_dec(v_traceState_4983_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5021_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; double v___x_5003_; uint8_t v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5001_ = lean_box(0);
v___x_5002_ = lean_box(0);
v___x_5003_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5004_ = 0;
v___x_5005_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5006_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5006_, 0, v_cls_4969_);
lean_ctor_set(v___x_5006_, 1, v___x_5002_);
lean_ctor_set(v___x_5006_, 2, v___x_5005_);
lean_ctor_set_float(v___x_5006_, sizeof(void*)*3, v___x_5003_);
lean_ctor_set_float(v___x_5006_, sizeof(void*)*3 + 8, v___x_5003_);
lean_ctor_set_uint8(v___x_5006_, sizeof(void*)*3 + 16, v___x_5004_);
v___x_5007_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5008_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5006_);
lean_ctor_set(v___x_5008_, 1, v_a_4978_);
lean_ctor_set(v___x_5008_, 2, v___x_5007_);
lean_inc(v_ref_4976_);
v___x_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5009_, 0, v_ref_4976_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
v___x_5010_ = l_Lean_PersistentArray_push___redArg(v_traces_4997_, v___x_5009_);
if (v_isShared_5000_ == 0)
{
lean_ctor_set(v___x_4999_, 0, v___x_5010_);
v___x_5012_ = v___x_4999_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v___x_5010_);
lean_ctor_set_uint64(v_reuseFailAlloc_5020_, sizeof(void*)*1, v_tid_4996_);
v___x_5012_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
lean_object* v___x_5014_; 
if (v_isShared_4995_ == 0)
{
lean_ctor_set(v___x_4994_, 4, v___x_5012_);
v___x_5014_ = v___x_4994_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_env_4984_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v_nextMacroScope_4985_);
lean_ctor_set(v_reuseFailAlloc_5019_, 2, v_ngen_4986_);
lean_ctor_set(v_reuseFailAlloc_5019_, 3, v_auxDeclNGen_4987_);
lean_ctor_set(v_reuseFailAlloc_5019_, 4, v___x_5012_);
lean_ctor_set(v_reuseFailAlloc_5019_, 5, v_cache_4988_);
lean_ctor_set(v_reuseFailAlloc_5019_, 6, v_recordedDeps_4989_);
lean_ctor_set(v_reuseFailAlloc_5019_, 7, v_messages_4990_);
lean_ctor_set(v_reuseFailAlloc_5019_, 8, v_infoState_4991_);
lean_ctor_set(v_reuseFailAlloc_5019_, 9, v_snapshotTasks_4992_);
v___x_5014_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
lean_object* v___x_5015_; lean_object* v___x_5017_; 
v___x_5015_ = lean_st_ref_put(v___y_4974_, v___x_5014_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 0, v___x_5001_);
v___x_5017_ = v___x_4980_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5001_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4969_ = stack[0].m_obj;
lean_object* v_msg_4970_ = stack[1].m_obj;
lean_object* v___y_4971_ = stack[2].m_obj;
lean_object* v___y_4972_ = stack[3].m_obj;
lean_object* v___y_4973_ = stack[4].m_obj;
lean_object* v___y_4974_ = stack[5].m_obj;
lean_object* v_res_5024_;
v_res_5024_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4969_, v_msg_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
stack->m_obj
 = v_res_5024_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5025_, lean_object* v_msg_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5025_, v_msg_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
return v_res_5032_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_5033_, lean_object* v___f_5034_, lean_object* v_____r_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v___x_5049_; lean_object* v_caches_5050_; lean_object* v_typeAnalysis_5051_; lean_object* v_target_5052_; lean_object* v_hypotheses_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5063_; 
v___x_5049_ = lean_st_ref_take(v___y_5038_);
v_caches_5050_ = lean_ctor_get(v___x_5049_, 0);
v_typeAnalysis_5051_ = lean_ctor_get(v___x_5049_, 1);
v_target_5052_ = lean_ctor_get(v___x_5049_, 2);
v_hypotheses_5053_ = lean_ctor_get(v___x_5049_, 3);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5055_ = v___x_5049_;
v_isShared_5056_ = v_isSharedCheck_5063_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_hypotheses_5053_);
lean_inc(v_target_5052_);
lean_inc(v_typeAnalysis_5051_);
lean_inc(v_caches_5050_);
lean_dec(v___x_5049_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5063_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5057_; lean_object* v___x_5059_; 
v___x_5057_ = lean_box(0);
if (v_isShared_5056_ == 0)
{
v___x_5059_ = v___x_5055_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_caches_5050_);
lean_ctor_set(v_reuseFailAlloc_5062_, 1, v_typeAnalysis_5051_);
lean_ctor_set(v_reuseFailAlloc_5062_, 2, v_target_5052_);
lean_ctor_set(v_reuseFailAlloc_5062_, 3, v_hypotheses_5053_);
v___x_5059_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; 
lean_ctor_set_uint8(v___x_5059_, sizeof(void*)*4, v___x_5033_);
v___x_5060_ = lean_st_ref_put(v___y_5038_, v___x_5059_);
lean_inc(v___y_5047_);
lean_inc_ref(v___y_5046_);
lean_inc(v___y_5045_);
lean_inc_ref(v___y_5044_);
lean_inc(v___y_5043_);
lean_inc_ref(v___y_5042_);
lean_inc(v___y_5041_);
lean_inc_ref(v___y_5040_);
lean_inc(v___y_5039_);
lean_inc(v___y_5038_);
lean_inc_ref(v___y_5037_);
lean_inc(v___y_5036_);
v___x_5061_ = lean_apply_14(v___f_5034_, v___x_5057_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, lean_box(0));
return v___x_5061_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_5033_ = stack[0].m_num;
lean_object* v___f_5034_ = stack[1].m_obj;
lean_object* v_____r_5035_ = stack[2].m_obj;
lean_object* v___y_5036_ = stack[3].m_obj;
lean_object* v___y_5037_ = stack[4].m_obj;
lean_object* v___y_5038_ = stack[5].m_obj;
lean_object* v___y_5039_ = stack[6].m_obj;
lean_object* v___y_5040_ = stack[7].m_obj;
lean_object* v___y_5041_ = stack[8].m_obj;
lean_object* v___y_5042_ = stack[9].m_obj;
lean_object* v___y_5043_ = stack[10].m_obj;
lean_object* v___y_5044_ = stack[11].m_obj;
lean_object* v___y_5045_ = stack[12].m_obj;
lean_object* v___y_5046_ = stack[13].m_obj;
lean_object* v___y_5047_ = stack[14].m_obj;
lean_object* v_res_5064_;
v_res_5064_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5033_, v___f_5034_, v_____r_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
stack->m_obj
 = v_res_5064_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_5065_, lean_object* v___f_5066_, lean_object* v_____r_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
uint8_t v___x_35999__boxed_5081_; lean_object* v_res_5082_; 
v___x_35999__boxed_5081_ = lean_unbox(v___x_5065_);
v_res_5082_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35999__boxed_5081_, v___f_5066_, v_____r_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
lean_dec(v___y_5079_);
lean_dec_ref(v___y_5078_);
lean_dec(v___y_5077_);
lean_dec_ref(v___y_5076_);
lean_dec(v___y_5075_);
lean_dec_ref(v___y_5074_);
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
lean_dec(v___y_5070_);
lean_dec_ref(v___y_5069_);
lean_dec(v___y_5068_);
return v_res_5082_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_5083_, lean_object* v_a_5084_, lean_object* v___x_5085_, lean_object* v_____r_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5100_ = lean_array_push(v_snd_5083_, v_a_5084_);
v___x_5101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5085_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5101_);
v___x_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5102_);
return v___x_5103_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_5083_ = stack[0].m_obj;
lean_object* v_a_5084_ = stack[1].m_obj;
lean_object* v___x_5085_ = stack[2].m_obj;
lean_object* v_____r_5086_ = stack[3].m_obj;
lean_object* v___y_5087_ = stack[4].m_obj;
lean_object* v___y_5088_ = stack[5].m_obj;
lean_object* v___y_5089_ = stack[6].m_obj;
lean_object* v___y_5090_ = stack[7].m_obj;
lean_object* v___y_5091_ = stack[8].m_obj;
lean_object* v___y_5092_ = stack[9].m_obj;
lean_object* v___y_5093_ = stack[10].m_obj;
lean_object* v___y_5094_ = stack[11].m_obj;
lean_object* v___y_5095_ = stack[12].m_obj;
lean_object* v___y_5096_ = stack[13].m_obj;
lean_object* v___y_5097_ = stack[14].m_obj;
lean_object* v___y_5098_ = stack[15].m_obj;
lean_object* v_res_5104_;
v_res_5104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5083_, v_a_5084_, v___x_5085_, v_____r_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
stack->m_obj
 = v_res_5104_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_5105_ = _args[0];
lean_object* v_a_5106_ = _args[1];
lean_object* v___x_5107_ = _args[2];
lean_object* v_____r_5108_ = _args[3];
lean_object* v___y_5109_ = _args[4];
lean_object* v___y_5110_ = _args[5];
lean_object* v___y_5111_ = _args[6];
lean_object* v___y_5112_ = _args[7];
lean_object* v___y_5113_ = _args[8];
lean_object* v___y_5114_ = _args[9];
lean_object* v___y_5115_ = _args[10];
lean_object* v___y_5116_ = _args[11];
lean_object* v___y_5117_ = _args[12];
lean_object* v___y_5118_ = _args[13];
lean_object* v___y_5119_ = _args[14];
lean_object* v___y_5120_ = _args[15];
lean_object* v___y_5121_ = _args[16];
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5105_, v_a_5106_, v___x_5107_, v_____r_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec(v___y_5118_);
lean_dec_ref(v___y_5117_);
lean_dec(v___y_5116_);
lean_dec_ref(v___y_5115_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v___y_5112_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
lean_dec(v___y_5109_);
return v_res_5122_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5123_, lean_object* v___x_5124_, lean_object* v_methods_5125_, lean_object* v_config_5126_, lean_object* v_a_5127_, lean_object* v_b_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
lean_object* v___y_5143_; uint8_t v___x_5165_; 
v___x_5165_ = lean_nat_dec_lt(v_a_5127_, v_upperBound_5123_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; 
lean_dec(v_a_5127_);
lean_dec_ref(v_config_5126_);
lean_dec_ref(v_methods_5125_);
v___x_5166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5166_, 0, v_b_5128_);
return v___x_5166_;
}
else
{
lean_object* v_snd_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5266_; 
v_snd_5167_ = lean_ctor_get(v_b_5128_, 1);
v_isSharedCheck_5266_ = !lean_is_exclusive(v_b_5128_);
if (v_isSharedCheck_5266_ == 0)
{
lean_object* v_unused_5267_; 
v_unused_5267_ = lean_ctor_get(v_b_5128_, 0);
lean_dec(v_unused_5267_);
v___x_5169_ = v_b_5128_;
v_isShared_5170_ = v_isSharedCheck_5266_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_snd_5167_);
lean_dec(v_b_5128_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5266_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v_type_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5171_ = lean_box(0);
v___x_5172_ = lean_array_fget_borrowed(v___x_5124_, v_a_5127_);
v___x_5173_ = lean_st_ref_take(v___y_5129_);
v___x_5174_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5175_ = lean_st_ref_put(v___y_5129_, v___x_5174_);
v_type_5176_ = lean_ctor_get(v___x_5172_, 1);
v___x_5177_ = lean_unsigned_to_nat(0u);
v___x_5178_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5178_, 0, v___x_5177_);
lean_ctor_set(v___x_5178_, 1, v___x_5173_);
lean_ctor_set(v___x_5178_, 2, v___x_5174_);
lean_ctor_set(v___x_5178_, 3, v___x_5174_);
lean_inc_ref(v_type_5176_);
v___x_5179_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5179_, 0, v_type_5176_);
lean_inc_ref(v_config_5126_);
lean_inc_ref(v_methods_5125_);
v___x_5180_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5179_, v_methods_5125_, v_config_5126_, v___x_5178_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v_a_5181_; lean_object* v_snd_5182_; lean_object* v_fst_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5257_; 
v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
lean_inc(v_a_5181_);
lean_dec_ref_known(v___x_5180_, 1);
v_snd_5182_ = lean_ctor_get(v_a_5181_, 1);
v_fst_5183_ = lean_ctor_get(v_a_5181_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v_a_5181_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5185_ = v_a_5181_;
v_isShared_5186_ = v_isSharedCheck_5257_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_snd_5182_);
lean_inc(v_fst_5183_);
lean_dec(v_a_5181_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5257_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v_persistentCache_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; 
v_persistentCache_5187_ = lean_ctor_get(v_snd_5182_, 1);
lean_inc_ref(v_persistentCache_5187_);
lean_dec(v_snd_5182_);
v___x_5188_ = lean_st_ref_swap(v___y_5129_, v_persistentCache_5187_);
lean_dec(v___x_5188_);
lean_inc(v___x_5172_);
v___x_5189_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5172_, v_fst_5183_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_object* v_a_5190_; lean_object* v_type_5191_; lean_object* v_value_5192_; uint8_t v___x_5193_; 
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_a_5190_);
lean_dec_ref_known(v___x_5189_, 1);
v_type_5191_ = lean_ctor_get(v_a_5190_, 1);
v_value_5192_ = lean_ctor_get(v_a_5190_, 2);
lean_inc_ref(v_type_5191_);
v___x_5193_ = l_Lean_Expr_isFalse(v_type_5191_);
if (v___x_5193_ == 0)
{
lean_object* v___f_5194_; uint8_t v___x_5224_; 
lean_del_object(v___x_5185_);
lean_inc(v_a_5190_);
lean_inc(v_snd_5167_);
v___f_5194_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5194_, 0, v_snd_5167_);
lean_closure_set(v___f_5194_, 1, v_a_5190_);
lean_closure_set(v___f_5194_, 2, v___x_5171_);
v___x_5224_ = lean_expr_eqv(v_type_5176_, v_type_5191_);
if (v___x_5224_ == 0)
{
lean_inc_ref(v_type_5191_);
lean_dec(v_a_5190_);
lean_dec(v_snd_5167_);
goto v___jp_5198_;
}
else
{
if (v___x_5193_ == 0)
{
lean_object* v___x_5225_; lean_object* v___x_5226_; 
lean_dec_ref(v___f_5194_);
lean_del_object(v___x_5169_);
v___x_5225_ = lean_box(0);
v___x_5226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5167_, v_a_5190_, v___x_5171_, v___x_5225_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
v___y_5143_ = v___x_5226_;
goto v___jp_5142_;
}
else
{
lean_inc_ref(v_type_5191_);
lean_dec(v_a_5190_);
lean_dec(v_snd_5167_);
goto v___jp_5198_;
}
}
v___jp_5195_:
{
lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___x_5196_ = lean_box(0);
v___x_5197_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5165_, v___f_5194_, v___x_5196_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
v___y_5143_ = v___x_5197_;
goto v___jp_5142_;
}
v___jp_5198_:
{
lean_object* v_toCold_5199_; lean_object* v_options_5200_; uint8_t v_hasTrace_5201_; 
v_toCold_5199_ = lean_ctor_get(v___y_5139_, 0);
v_options_5200_ = lean_ctor_get(v_toCold_5199_, 2);
v_hasTrace_5201_ = lean_ctor_get_uint8(v_options_5200_, sizeof(void*)*1);
if (v_hasTrace_5201_ == 0)
{
lean_dec_ref(v_type_5191_);
lean_del_object(v___x_5169_);
goto v___jp_5195_;
}
else
{
lean_object* v_inheritedTraceOptions_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; uint8_t v___x_5205_; 
v_inheritedTraceOptions_5202_ = lean_ctor_get(v_toCold_5199_, 11);
v___x_5203_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5204_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5205_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5202_, v_options_5200_, v___x_5204_);
if (v___x_5205_ == 0)
{
lean_dec_ref(v_type_5191_);
lean_del_object(v___x_5169_);
goto v___jp_5195_;
}
else
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5209_; 
lean_inc_ref(v_type_5176_);
v___x_5206_ = l_Lean_MessageData_ofExpr(v_type_5176_);
v___x_5207_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5170_ == 0)
{
lean_ctor_set_tag(v___x_5169_, 7);
lean_ctor_set(v___x_5169_, 1, v___x_5207_);
lean_ctor_set(v___x_5169_, 0, v___x_5206_);
v___x_5209_ = v___x_5169_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v___x_5206_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v___x_5207_);
v___x_5209_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5210_ = l_Lean_MessageData_ofExpr(v_type_5191_);
v___x_5211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5211_, 0, v___x_5209_);
lean_ctor_set(v___x_5211_, 1, v___x_5210_);
v___x_5212_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5203_, v___x_5211_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v___x_5214_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_a_5213_);
lean_dec_ref_known(v___x_5212_, 1);
v___x_5214_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5165_, v___f_5194_, v_a_5213_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
v___y_5143_ = v___x_5214_;
goto v___jp_5142_;
}
else
{
lean_object* v_a_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5222_; 
lean_dec_ref(v___f_5194_);
lean_dec(v_a_5127_);
lean_dec_ref(v_config_5126_);
lean_dec_ref(v_methods_5125_);
v_a_5215_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5217_ = v___x_5212_;
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_a_5215_);
lean_dec(v___x_5212_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5220_; 
if (v_isShared_5218_ == 0)
{
v___x_5220_ = v___x_5217_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
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
lean_object* v___x_5227_; 
lean_inc_ref(v_value_5192_);
lean_dec(v_a_5190_);
lean_del_object(v___x_5169_);
lean_dec(v_a_5127_);
lean_dec_ref(v_config_5126_);
lean_dec_ref(v_methods_5125_);
v___x_5227_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5192_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5239_; 
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5239_ == 0)
{
lean_object* v_unused_5240_; 
v_unused_5240_ = lean_ctor_get(v___x_5227_, 0);
lean_dec(v_unused_5240_);
v___x_5229_ = v___x_5227_;
v_isShared_5230_ = v_isSharedCheck_5239_;
goto v_resetjp_5228_;
}
else
{
lean_dec(v___x_5227_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5239_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5234_; 
v___x_5231_ = lean_box(v___x_5165_);
v___x_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 1, v_snd_5167_);
lean_ctor_set(v___x_5185_, 0, v___x_5232_);
v___x_5234_ = v___x_5185_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5232_);
lean_ctor_set(v_reuseFailAlloc_5238_, 1, v_snd_5167_);
v___x_5234_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
lean_object* v___x_5236_; 
if (v_isShared_5230_ == 0)
{
lean_ctor_set(v___x_5229_, 0, v___x_5234_);
v___x_5236_ = v___x_5229_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5234_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
}
}
else
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5248_; 
lean_del_object(v___x_5185_);
lean_dec(v_snd_5167_);
v_a_5241_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5248_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5243_ = v___x_5227_;
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v___x_5227_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5246_; 
if (v_isShared_5244_ == 0)
{
v___x_5246_ = v___x_5243_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_a_5241_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
}
}
}
}
}
else
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5256_; 
lean_del_object(v___x_5185_);
lean_del_object(v___x_5169_);
lean_dec(v_snd_5167_);
lean_dec(v_a_5127_);
lean_dec_ref(v_config_5126_);
lean_dec_ref(v_methods_5125_);
v_a_5249_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5189_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5189_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5254_; 
if (v_isShared_5252_ == 0)
{
v___x_5254_ = v___x_5251_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5249_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
}
}
else
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5265_; 
lean_del_object(v___x_5169_);
lean_dec(v_snd_5167_);
lean_dec(v_a_5127_);
lean_dec_ref(v_config_5126_);
lean_dec_ref(v_methods_5125_);
v_a_5258_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5260_ = v___x_5180_;
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v___x_5180_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5263_; 
if (v_isShared_5261_ == 0)
{
v___x_5263_ = v___x_5260_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5258_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
}
}
v___jp_5142_:
{
if (lean_obj_tag(v___y_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5156_; 
v_a_5144_ = lean_ctor_get(v___y_5143_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___y_5143_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5146_ = v___y_5143_;
v_isShared_5147_ = v_isSharedCheck_5156_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___y_5143_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5156_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
if (lean_obj_tag(v_a_5144_) == 0)
{
lean_object* v_a_5148_; lean_object* v___x_5150_; 
lean_dec(v_a_5127_);
lean_dec_ref(v_config_5126_);
lean_dec_ref(v_methods_5125_);
v_a_5148_ = lean_ctor_get(v_a_5144_, 0);
lean_inc(v_a_5148_);
lean_dec_ref_known(v_a_5144_, 1);
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 0, v_a_5148_);
v___x_5150_ = v___x_5146_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5148_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
else
{
lean_object* v_a_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; 
lean_del_object(v___x_5146_);
v_a_5152_ = lean_ctor_get(v_a_5144_, 0);
lean_inc(v_a_5152_);
lean_dec_ref_known(v_a_5144_, 1);
v___x_5153_ = lean_unsigned_to_nat(1u);
v___x_5154_ = lean_nat_add(v_a_5127_, v___x_5153_);
lean_dec(v_a_5127_);
v_a_5127_ = v___x_5154_;
v_b_5128_ = v_a_5152_;
goto _start;
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec(v_a_5127_);
lean_dec_ref(v_config_5126_);
lean_dec_ref(v_methods_5125_);
v_a_5157_ = lean_ctor_get(v___y_5143_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___y_5143_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___y_5143_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___y_5143_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5123_ = stack[0].m_obj;
lean_object* v___x_5124_ = stack[1].m_obj;
lean_object* v_methods_5125_ = stack[2].m_obj;
lean_object* v_config_5126_ = stack[3].m_obj;
lean_object* v_a_5127_ = stack[4].m_obj;
lean_object* v_b_5128_ = stack[5].m_obj;
lean_object* v___y_5129_ = stack[6].m_obj;
lean_object* v___y_5130_ = stack[7].m_obj;
lean_object* v___y_5131_ = stack[8].m_obj;
lean_object* v___y_5132_ = stack[9].m_obj;
lean_object* v___y_5133_ = stack[10].m_obj;
lean_object* v___y_5134_ = stack[11].m_obj;
lean_object* v___y_5135_ = stack[12].m_obj;
lean_object* v___y_5136_ = stack[13].m_obj;
lean_object* v___y_5137_ = stack[14].m_obj;
lean_object* v___y_5138_ = stack[15].m_obj;
lean_object* v___y_5139_ = stack[16].m_obj;
lean_object* v___y_5140_ = stack[17].m_obj;
lean_object* v_res_5268_;
v_res_5268_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5123_, v___x_5124_, v_methods_5125_, v_config_5126_, v_a_5127_, v_b_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
stack->m_obj
 = v_res_5268_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5269_ = _args[0];
lean_object* v___x_5270_ = _args[1];
lean_object* v_methods_5271_ = _args[2];
lean_object* v_config_5272_ = _args[3];
lean_object* v_a_5273_ = _args[4];
lean_object* v_b_5274_ = _args[5];
lean_object* v___y_5275_ = _args[6];
lean_object* v___y_5276_ = _args[7];
lean_object* v___y_5277_ = _args[8];
lean_object* v___y_5278_ = _args[9];
lean_object* v___y_5279_ = _args[10];
lean_object* v___y_5280_ = _args[11];
lean_object* v___y_5281_ = _args[12];
lean_object* v___y_5282_ = _args[13];
lean_object* v___y_5283_ = _args[14];
lean_object* v___y_5284_ = _args[15];
lean_object* v___y_5285_ = _args[16];
lean_object* v___y_5286_ = _args[17];
lean_object* v___y_5287_ = _args[18];
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5269_, v___x_5270_, v_methods_5271_, v_config_5272_, v_a_5273_, v_b_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec_ref(v___x_5270_);
lean_dec(v_upperBound_5269_);
return v_res_5288_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_5289_, lean_object* v_config_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v___x_5304_; lean_object* v_hypotheses_5305_; lean_object* v___x_5306_; lean_object* v_newHyps_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5304_ = lean_st_ref_get(v_a_5293_);
v_hypotheses_5305_ = lean_ctor_get(v___x_5304_, 3);
lean_inc_ref(v_hypotheses_5305_);
lean_dec(v___x_5304_);
v___x_5306_ = lean_array_get_size(v_hypotheses_5305_);
v_newHyps_5307_ = lean_mk_empty_array_with_capacity(v___x_5306_);
v___x_5308_ = lean_unsigned_to_nat(0u);
v___x_5309_ = lean_box(0);
v___x_5310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5309_);
lean_ctor_set(v___x_5310_, 1, v_newHyps_5307_);
v___x_5311_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_5306_, v_hypotheses_5305_, v_methods_5289_, v_config_5290_, v___x_5308_, v___x_5310_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
lean_dec_ref(v_hypotheses_5305_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5341_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5314_ = v___x_5311_;
v_isShared_5315_ = v_isSharedCheck_5341_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5311_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5341_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v_fst_5316_; 
v_fst_5316_ = lean_ctor_get(v_a_5312_, 0);
if (lean_obj_tag(v_fst_5316_) == 0)
{
lean_object* v_snd_5317_; lean_object* v___x_5318_; lean_object* v_caches_5319_; lean_object* v_typeAnalysis_5320_; lean_object* v_target_5321_; uint8_t v_didChange_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5335_; 
v_snd_5317_ = lean_ctor_get(v_a_5312_, 1);
lean_inc(v_snd_5317_);
lean_dec(v_a_5312_);
v___x_5318_ = lean_st_ref_take(v_a_5293_);
v_caches_5319_ = lean_ctor_get(v___x_5318_, 0);
v_typeAnalysis_5320_ = lean_ctor_get(v___x_5318_, 1);
v_target_5321_ = lean_ctor_get(v___x_5318_, 2);
v_didChange_5322_ = lean_ctor_get_uint8(v___x_5318_, sizeof(void*)*4);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5335_ == 0)
{
lean_object* v_unused_5336_; 
v_unused_5336_ = lean_ctor_get(v___x_5318_, 3);
lean_dec(v_unused_5336_);
v___x_5324_ = v___x_5318_;
v_isShared_5325_ = v_isSharedCheck_5335_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_target_5321_);
lean_inc(v_typeAnalysis_5320_);
lean_inc(v_caches_5319_);
lean_dec(v___x_5318_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5335_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 3, v_snd_5317_);
v___x_5327_ = v___x_5324_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_caches_5319_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v_typeAnalysis_5320_);
lean_ctor_set(v_reuseFailAlloc_5334_, 2, v_target_5321_);
lean_ctor_set(v_reuseFailAlloc_5334_, 3, v_snd_5317_);
lean_ctor_set_uint8(v_reuseFailAlloc_5334_, sizeof(void*)*4, v_didChange_5322_);
v___x_5327_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
lean_object* v___x_5328_; uint8_t v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5332_; 
v___x_5328_ = lean_st_ref_put(v_a_5293_, v___x_5327_);
v___x_5329_ = 0;
v___x_5330_ = lean_box(v___x_5329_);
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 0, v___x_5330_);
v___x_5332_ = v___x_5314_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5330_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
else
{
lean_object* v_val_5337_; lean_object* v___x_5339_; 
lean_inc_ref(v_fst_5316_);
lean_dec(v_a_5312_);
v_val_5337_ = lean_ctor_get(v_fst_5316_, 0);
lean_inc(v_val_5337_);
lean_dec_ref_known(v_fst_5316_, 1);
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 0, v_val_5337_);
v___x_5339_ = v___x_5314_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_val_5337_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
}
else
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5349_; 
v_a_5342_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5344_ = v___x_5311_;
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5311_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5347_; 
if (v_isShared_5345_ == 0)
{
v___x_5347_ = v___x_5344_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_methods_5289_ = stack[0].m_obj;
lean_object* v_config_5290_ = stack[1].m_obj;
lean_object* v_a_5291_ = stack[2].m_obj;
lean_object* v_a_5292_ = stack[3].m_obj;
lean_object* v_a_5293_ = stack[4].m_obj;
lean_object* v_a_5294_ = stack[5].m_obj;
lean_object* v_a_5295_ = stack[6].m_obj;
lean_object* v_a_5296_ = stack[7].m_obj;
lean_object* v_a_5297_ = stack[8].m_obj;
lean_object* v_a_5298_ = stack[9].m_obj;
lean_object* v_a_5299_ = stack[10].m_obj;
lean_object* v_a_5300_ = stack[11].m_obj;
lean_object* v_a_5301_ = stack[12].m_obj;
lean_object* v_a_5302_ = stack[13].m_obj;
lean_object* v_res_5350_;
v_res_5350_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5289_, v_config_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
stack->m_obj
 = v_res_5350_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_5351_, lean_object* v_config_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5351_, v_config_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_);
lean_dec(v_a_5364_);
lean_dec_ref(v_a_5363_);
lean_dec(v_a_5362_);
lean_dec_ref(v_a_5361_);
lean_dec(v_a_5360_);
lean_dec_ref(v_a_5359_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec(v_a_5355_);
lean_dec_ref(v_a_5354_);
lean_dec(v_a_5353_);
return v_res_5366_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_5367_, lean_object* v_msg_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5367_, v_msg_5368_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_);
return v___x_5382_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5367_ = stack[0].m_obj;
lean_object* v_msg_5368_ = stack[1].m_obj;
lean_object* v___y_5369_ = stack[2].m_obj;
lean_object* v___y_5370_ = stack[3].m_obj;
lean_object* v___y_5371_ = stack[4].m_obj;
lean_object* v___y_5372_ = stack[5].m_obj;
lean_object* v___y_5373_ = stack[6].m_obj;
lean_object* v___y_5374_ = stack[7].m_obj;
lean_object* v___y_5375_ = stack[8].m_obj;
lean_object* v___y_5376_ = stack[9].m_obj;
lean_object* v___y_5377_ = stack[10].m_obj;
lean_object* v___y_5378_ = stack[11].m_obj;
lean_object* v___y_5379_ = stack[12].m_obj;
lean_object* v___y_5380_ = stack[13].m_obj;
lean_object* v_res_5383_;
v_res_5383_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5367_, v_msg_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_);
stack->m_obj
 = v_res_5383_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_5384_, lean_object* v_msg_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
lean_object* v_res_5399_; 
v_res_5399_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5384_, v_msg_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5396_);
lean_dec(v___y_5395_);
lean_dec_ref(v___y_5394_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
lean_dec(v___y_5389_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
return v_res_5399_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_upperBound_5400_, lean_object* v___x_5401_, lean_object* v_methods_5402_, lean_object* v_config_5403_, lean_object* v_inst_5404_, lean_object* v_R_5405_, lean_object* v_a_5406_, lean_object* v_b_5407_, lean_object* v_c_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_){
_start:
{
lean_object* v___x_5422_; 
v___x_5422_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5400_, v___x_5401_, v_methods_5402_, v_config_5403_, v_a_5406_, v_b_5407_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
return v___x_5422_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5400_ = stack[0].m_obj;
lean_object* v___x_5401_ = stack[1].m_obj;
lean_object* v_methods_5402_ = stack[2].m_obj;
lean_object* v_config_5403_ = stack[3].m_obj;
lean_object* v_a_5406_ = stack[6].m_obj;
lean_object* v_b_5407_ = stack[7].m_obj;
lean_object* v___y_5409_ = stack[9].m_obj;
lean_object* v___y_5410_ = stack[10].m_obj;
lean_object* v___y_5411_ = stack[11].m_obj;
lean_object* v___y_5412_ = stack[12].m_obj;
lean_object* v___y_5413_ = stack[13].m_obj;
lean_object* v___y_5414_ = stack[14].m_obj;
lean_object* v___y_5415_ = stack[15].m_obj;
lean_object* v___y_5416_ = stack[16].m_obj;
lean_object* v___y_5417_ = stack[17].m_obj;
lean_object* v___y_5418_ = stack[18].m_obj;
lean_object* v___y_5419_ = stack[19].m_obj;
lean_object* v___y_5420_ = stack[20].m_obj;
lean_object* v_res_5423_;
v_res_5423_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5400_, v___x_5401_, v_methods_5402_, v_config_5403_, lean_box(0), lean_box(0), v_a_5406_, v_b_5407_, lean_box(0), v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
stack->m_obj
 = v_res_5423_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5424_ = _args[0];
lean_object* v___x_5425_ = _args[1];
lean_object* v_methods_5426_ = _args[2];
lean_object* v_config_5427_ = _args[3];
lean_object* v_inst_5428_ = _args[4];
lean_object* v_R_5429_ = _args[5];
lean_object* v_a_5430_ = _args[6];
lean_object* v_b_5431_ = _args[7];
lean_object* v_c_5432_ = _args[8];
lean_object* v___y_5433_ = _args[9];
lean_object* v___y_5434_ = _args[10];
lean_object* v___y_5435_ = _args[11];
lean_object* v___y_5436_ = _args[12];
lean_object* v___y_5437_ = _args[13];
lean_object* v___y_5438_ = _args[14];
lean_object* v___y_5439_ = _args[15];
lean_object* v___y_5440_ = _args[16];
lean_object* v___y_5441_ = _args[17];
lean_object* v___y_5442_ = _args[18];
lean_object* v___y_5443_ = _args[19];
lean_object* v___y_5444_ = _args[20];
lean_object* v___y_5445_ = _args[21];
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5424_, v___x_5425_, v_methods_5426_, v_config_5427_, v_inst_5428_, v_R_5429_, v_a_5430_, v_b_5431_, v_c_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec(v___y_5435_);
lean_dec_ref(v___y_5434_);
lean_dec(v___y_5433_);
lean_dec_ref(v___x_5425_);
lean_dec(v_upperBound_5424_);
return v_res_5446_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_5447_, lean_object* v_config_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_){
_start:
{
lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; 
v___x_5461_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5462_ = lean_st_mk_ref(v___x_5461_);
v___x_5463_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5447_, v_config_5448_, v___x_5462_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5472_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5466_ = v___x_5463_;
v_isShared_5467_ = v_isSharedCheck_5472_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5463_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5472_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5468_; lean_object* v___x_5470_; 
v___x_5468_ = lean_st_ref_get(v___x_5462_);
lean_dec(v___x_5462_);
lean_dec(v___x_5468_);
if (v_isShared_5467_ == 0)
{
v___x_5470_ = v___x_5466_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_a_5464_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
else
{
lean_dec(v___x_5462_);
return v___x_5463_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_methods_5447_ = stack[0].m_obj;
lean_object* v_config_5448_ = stack[1].m_obj;
lean_object* v_a_5449_ = stack[2].m_obj;
lean_object* v_a_5450_ = stack[3].m_obj;
lean_object* v_a_5451_ = stack[4].m_obj;
lean_object* v_a_5452_ = stack[5].m_obj;
lean_object* v_a_5453_ = stack[6].m_obj;
lean_object* v_a_5454_ = stack[7].m_obj;
lean_object* v_a_5455_ = stack[8].m_obj;
lean_object* v_a_5456_ = stack[9].m_obj;
lean_object* v_a_5457_ = stack[10].m_obj;
lean_object* v_a_5458_ = stack[11].m_obj;
lean_object* v_a_5459_ = stack[12].m_obj;
lean_object* v_res_5473_;
v_res_5473_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5447_, v_config_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_);
stack->m_obj
 = v_res_5473_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_5474_, lean_object* v_config_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_){
_start:
{
lean_object* v_res_5488_; 
v_res_5488_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5474_, v_config_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_, v_a_5486_);
lean_dec(v_a_5486_);
lean_dec_ref(v_a_5485_);
lean_dec(v_a_5484_);
lean_dec_ref(v_a_5483_);
lean_dec(v_a_5482_);
lean_dec_ref(v_a_5481_);
lean_dec(v_a_5480_);
lean_dec_ref(v_a_5479_);
lean_dec(v_a_5478_);
lean_dec(v_a_5477_);
lean_dec_ref(v_a_5476_);
return v_res_5488_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_5489_, lean_object* v_msg_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_){
_start:
{
lean_object* v_ref_5496_; lean_object* v___x_5497_; lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5543_; 
v_ref_5496_ = lean_ctor_get(v___y_5493_, 2);
v___x_5497_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_);
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5497_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5500_ = v___x_5497_;
v_isShared_5501_ = v_isSharedCheck_5543_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5497_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5543_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5502_; lean_object* v_traceState_5503_; lean_object* v_env_5504_; lean_object* v_nextMacroScope_5505_; lean_object* v_ngen_5506_; lean_object* v_auxDeclNGen_5507_; lean_object* v_cache_5508_; lean_object* v_recordedDeps_5509_; lean_object* v_messages_5510_; lean_object* v_infoState_5511_; lean_object* v_snapshotTasks_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5542_; 
v___x_5502_ = lean_st_ref_take(v___y_5494_);
v_traceState_5503_ = lean_ctor_get(v___x_5502_, 4);
v_env_5504_ = lean_ctor_get(v___x_5502_, 0);
v_nextMacroScope_5505_ = lean_ctor_get(v___x_5502_, 1);
v_ngen_5506_ = lean_ctor_get(v___x_5502_, 2);
v_auxDeclNGen_5507_ = lean_ctor_get(v___x_5502_, 3);
v_cache_5508_ = lean_ctor_get(v___x_5502_, 5);
v_recordedDeps_5509_ = lean_ctor_get(v___x_5502_, 6);
v_messages_5510_ = lean_ctor_get(v___x_5502_, 7);
v_infoState_5511_ = lean_ctor_get(v___x_5502_, 8);
v_snapshotTasks_5512_ = lean_ctor_get(v___x_5502_, 9);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5514_ = v___x_5502_;
v_isShared_5515_ = v_isSharedCheck_5542_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_snapshotTasks_5512_);
lean_inc(v_infoState_5511_);
lean_inc(v_messages_5510_);
lean_inc(v_recordedDeps_5509_);
lean_inc(v_cache_5508_);
lean_inc(v_traceState_5503_);
lean_inc(v_auxDeclNGen_5507_);
lean_inc(v_ngen_5506_);
lean_inc(v_nextMacroScope_5505_);
lean_inc(v_env_5504_);
lean_dec(v___x_5502_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5542_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
uint64_t v_tid_5516_; lean_object* v_traces_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5541_; 
v_tid_5516_ = lean_ctor_get_uint64(v_traceState_5503_, sizeof(void*)*1);
v_traces_5517_ = lean_ctor_get(v_traceState_5503_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v_traceState_5503_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5519_ = v_traceState_5503_;
v_isShared_5520_ = v_isSharedCheck_5541_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_traces_5517_);
lean_dec(v_traceState_5503_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5541_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; double v___x_5523_; uint8_t v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5532_; 
v___x_5521_ = lean_box(0);
v___x_5522_ = lean_box(0);
v___x_5523_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5524_ = 0;
v___x_5525_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5526_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5526_, 0, v_cls_5489_);
lean_ctor_set(v___x_5526_, 1, v___x_5522_);
lean_ctor_set(v___x_5526_, 2, v___x_5525_);
lean_ctor_set_float(v___x_5526_, sizeof(void*)*3, v___x_5523_);
lean_ctor_set_float(v___x_5526_, sizeof(void*)*3 + 8, v___x_5523_);
lean_ctor_set_uint8(v___x_5526_, sizeof(void*)*3 + 16, v___x_5524_);
v___x_5527_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5528_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5526_);
lean_ctor_set(v___x_5528_, 1, v_a_5498_);
lean_ctor_set(v___x_5528_, 2, v___x_5527_);
lean_inc(v_ref_5496_);
v___x_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5529_, 0, v_ref_5496_);
lean_ctor_set(v___x_5529_, 1, v___x_5528_);
v___x_5530_ = l_Lean_PersistentArray_push___redArg(v_traces_5517_, v___x_5529_);
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 0, v___x_5530_);
v___x_5532_ = v___x_5519_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5530_);
lean_ctor_set_uint64(v_reuseFailAlloc_5540_, sizeof(void*)*1, v_tid_5516_);
v___x_5532_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
lean_object* v___x_5534_; 
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 4, v___x_5532_);
v___x_5534_ = v___x_5514_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_env_5504_);
lean_ctor_set(v_reuseFailAlloc_5539_, 1, v_nextMacroScope_5505_);
lean_ctor_set(v_reuseFailAlloc_5539_, 2, v_ngen_5506_);
lean_ctor_set(v_reuseFailAlloc_5539_, 3, v_auxDeclNGen_5507_);
lean_ctor_set(v_reuseFailAlloc_5539_, 4, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5539_, 5, v_cache_5508_);
lean_ctor_set(v_reuseFailAlloc_5539_, 6, v_recordedDeps_5509_);
lean_ctor_set(v_reuseFailAlloc_5539_, 7, v_messages_5510_);
lean_ctor_set(v_reuseFailAlloc_5539_, 8, v_infoState_5511_);
lean_ctor_set(v_reuseFailAlloc_5539_, 9, v_snapshotTasks_5512_);
v___x_5534_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5535_; lean_object* v___x_5537_; 
v___x_5535_ = lean_st_ref_put(v___y_5494_, v___x_5534_);
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 0, v___x_5521_);
v___x_5537_ = v___x_5500_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v___x_5521_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5489_ = stack[0].m_obj;
lean_object* v_msg_5490_ = stack[1].m_obj;
lean_object* v___y_5491_ = stack[2].m_obj;
lean_object* v___y_5492_ = stack[3].m_obj;
lean_object* v___y_5493_ = stack[4].m_obj;
lean_object* v___y_5494_ = stack[5].m_obj;
lean_object* v_res_5544_;
v_res_5544_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5489_, v_msg_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_);
stack->m_obj
 = v_res_5544_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5545_, lean_object* v_msg_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_){
_start:
{
lean_object* v_res_5552_; 
v_res_5552_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5545_, v_msg_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
lean_dec(v___y_5550_);
lean_dec_ref(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec_ref(v___y_5547_);
return v_res_5552_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5553_, lean_object* v___x_5554_, lean_object* v_methods_5555_, lean_object* v_config_5556_, lean_object* v_a_5557_, lean_object* v_b_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_){
_start:
{
lean_object* v___y_5573_; uint8_t v___x_5595_; 
v___x_5595_ = lean_nat_dec_lt(v_a_5557_, v_upperBound_5553_);
if (v___x_5595_ == 0)
{
lean_object* v___x_5596_; 
lean_dec(v_a_5557_);
lean_dec_ref(v_config_5556_);
lean_dec_ref(v_methods_5555_);
v___x_5596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5596_, 0, v_b_5558_);
return v___x_5596_;
}
else
{
lean_object* v_snd_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5703_; 
v_snd_5597_ = lean_ctor_get(v_b_5558_, 1);
v_isSharedCheck_5703_ = !lean_is_exclusive(v_b_5558_);
if (v_isSharedCheck_5703_ == 0)
{
lean_object* v_unused_5704_; 
v_unused_5704_ = lean_ctor_get(v_b_5558_, 0);
lean_dec(v_unused_5704_);
v___x_5599_ = v_b_5558_;
v_isShared_5600_ = v_isSharedCheck_5703_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_snd_5597_);
lean_dec(v_b_5558_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5703_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v_type_5606_; lean_object* v___x_5607_; lean_object* v___x_5609_; 
v___x_5601_ = lean_box(0);
v___x_5602_ = lean_array_fget_borrowed(v___x_5554_, v_a_5557_);
v___x_5603_ = lean_st_ref_take(v___y_5559_);
v___x_5604_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5605_ = lean_st_ref_put(v___y_5559_, v___x_5604_);
v_type_5606_ = lean_ctor_get(v___x_5602_, 1);
v___x_5607_ = lean_unsigned_to_nat(0u);
if (v_isShared_5600_ == 0)
{
lean_ctor_set(v___x_5599_, 1, v___x_5603_);
lean_ctor_set(v___x_5599_, 0, v___x_5607_);
v___x_5609_ = v___x_5599_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5607_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v___x_5603_);
v___x_5609_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
lean_object* v___x_5610_; lean_object* v___x_5611_; 
lean_inc_ref(v_type_5606_);
v___x_5610_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5610_, 0, v_type_5606_);
lean_inc_ref(v_config_5556_);
lean_inc_ref(v_methods_5555_);
v___x_5611_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5610_, v_methods_5555_, v_config_5556_, v___x_5609_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v_a_5612_; lean_object* v_snd_5613_; lean_object* v_fst_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5693_; 
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
lean_inc(v_a_5612_);
lean_dec_ref_known(v___x_5611_, 1);
v_snd_5613_ = lean_ctor_get(v_a_5612_, 1);
v_fst_5614_ = lean_ctor_get(v_a_5612_, 0);
v_isSharedCheck_5693_ = !lean_is_exclusive(v_a_5612_);
if (v_isSharedCheck_5693_ == 0)
{
v___x_5616_ = v_a_5612_;
v_isShared_5617_ = v_isSharedCheck_5693_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_snd_5613_);
lean_inc(v_fst_5614_);
lean_dec(v_a_5612_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5693_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v_cache_5618_; lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5691_; 
v_cache_5618_ = lean_ctor_get(v_snd_5613_, 1);
v_isSharedCheck_5691_ = !lean_is_exclusive(v_snd_5613_);
if (v_isSharedCheck_5691_ == 0)
{
lean_object* v_unused_5692_; 
v_unused_5692_ = lean_ctor_get(v_snd_5613_, 0);
lean_dec(v_unused_5692_);
v___x_5620_ = v_snd_5613_;
v_isShared_5621_ = v_isSharedCheck_5691_;
goto v_resetjp_5619_;
}
else
{
lean_inc(v_cache_5618_);
lean_dec(v_snd_5613_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5691_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5622_; lean_object* v___x_5623_; 
v___x_5622_ = lean_st_ref_swap(v___y_5559_, v_cache_5618_);
lean_dec(v___x_5622_);
lean_inc(v___x_5602_);
v___x_5623_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5602_, v_fst_5614_);
lean_dec(v_fst_5614_);
if (lean_obj_tag(v___x_5623_) == 0)
{
lean_object* v_a_5624_; lean_object* v_type_5625_; lean_object* v_value_5626_; uint8_t v___x_5627_; 
v_a_5624_ = lean_ctor_get(v___x_5623_, 0);
lean_inc(v_a_5624_);
lean_dec_ref_known(v___x_5623_, 1);
v_type_5625_ = lean_ctor_get(v_a_5624_, 1);
v_value_5626_ = lean_ctor_get(v_a_5624_, 2);
lean_inc_ref(v_type_5625_);
v___x_5627_ = l_Lean_Expr_isFalse(v_type_5625_);
if (v___x_5627_ == 0)
{
lean_object* v___f_5628_; uint8_t v___x_5658_; 
lean_del_object(v___x_5616_);
lean_inc(v_a_5624_);
lean_inc(v_snd_5597_);
v___f_5628_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5628_, 0, v_snd_5597_);
lean_closure_set(v___f_5628_, 1, v_a_5624_);
lean_closure_set(v___f_5628_, 2, v___x_5601_);
v___x_5658_ = lean_expr_eqv(v_type_5606_, v_type_5625_);
if (v___x_5658_ == 0)
{
lean_inc_ref(v_type_5625_);
lean_dec(v_a_5624_);
lean_dec(v_snd_5597_);
goto v___jp_5632_;
}
else
{
if (v___x_5627_ == 0)
{
lean_object* v___x_5659_; lean_object* v___x_5660_; 
lean_dec_ref(v___f_5628_);
lean_del_object(v___x_5620_);
v___x_5659_ = lean_box(0);
v___x_5660_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5597_, v_a_5624_, v___x_5601_, v___x_5659_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
v___y_5573_ = v___x_5660_;
goto v___jp_5572_;
}
else
{
lean_inc_ref(v_type_5625_);
lean_dec(v_a_5624_);
lean_dec(v_snd_5597_);
goto v___jp_5632_;
}
}
v___jp_5629_:
{
lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5630_ = lean_box(0);
v___x_5631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5595_, v___f_5628_, v___x_5630_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
v___y_5573_ = v___x_5631_;
goto v___jp_5572_;
}
v___jp_5632_:
{
lean_object* v_toCold_5633_; lean_object* v_options_5634_; uint8_t v_hasTrace_5635_; 
v_toCold_5633_ = lean_ctor_get(v___y_5569_, 0);
v_options_5634_ = lean_ctor_get(v_toCold_5633_, 2);
v_hasTrace_5635_ = lean_ctor_get_uint8(v_options_5634_, sizeof(void*)*1);
if (v_hasTrace_5635_ == 0)
{
lean_dec_ref(v_type_5625_);
lean_del_object(v___x_5620_);
goto v___jp_5629_;
}
else
{
lean_object* v_inheritedTraceOptions_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; uint8_t v___x_5639_; 
v_inheritedTraceOptions_5636_ = lean_ctor_get(v_toCold_5633_, 11);
v___x_5637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5638_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5639_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5636_, v_options_5634_, v___x_5638_);
if (v___x_5639_ == 0)
{
lean_dec_ref(v_type_5625_);
lean_del_object(v___x_5620_);
goto v___jp_5629_;
}
else
{
lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5643_; 
lean_inc_ref(v_type_5606_);
v___x_5640_ = l_Lean_MessageData_ofExpr(v_type_5606_);
v___x_5641_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5621_ == 0)
{
lean_ctor_set_tag(v___x_5620_, 7);
lean_ctor_set(v___x_5620_, 1, v___x_5641_);
lean_ctor_set(v___x_5620_, 0, v___x_5640_);
v___x_5643_ = v___x_5620_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v___x_5640_);
lean_ctor_set(v_reuseFailAlloc_5657_, 1, v___x_5641_);
v___x_5643_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; 
v___x_5644_ = l_Lean_MessageData_ofExpr(v_type_5625_);
v___x_5645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5643_);
lean_ctor_set(v___x_5645_, 1, v___x_5644_);
v___x_5646_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5637_, v___x_5645_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_object* v_a_5647_; lean_object* v___x_5648_; 
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
lean_inc(v_a_5647_);
lean_dec_ref_known(v___x_5646_, 1);
v___x_5648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5595_, v___f_5628_, v_a_5647_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
v___y_5573_ = v___x_5648_;
goto v___jp_5572_;
}
else
{
lean_object* v_a_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5656_; 
lean_dec_ref(v___f_5628_);
lean_dec(v_a_5557_);
lean_dec_ref(v_config_5556_);
lean_dec_ref(v_methods_5555_);
v_a_5649_ = lean_ctor_get(v___x_5646_, 0);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5651_ = v___x_5646_;
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_a_5649_);
lean_dec(v___x_5646_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
lean_object* v___x_5654_; 
if (v_isShared_5652_ == 0)
{
v___x_5654_ = v___x_5651_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
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
lean_object* v___x_5661_; 
lean_inc_ref(v_value_5626_);
lean_dec(v_a_5624_);
lean_del_object(v___x_5620_);
lean_dec(v_a_5557_);
lean_dec_ref(v_config_5556_);
lean_dec_ref(v_methods_5555_);
v___x_5661_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5626_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_5661_) == 0)
{
lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5673_; 
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5661_);
if (v_isSharedCheck_5673_ == 0)
{
lean_object* v_unused_5674_; 
v_unused_5674_ = lean_ctor_get(v___x_5661_, 0);
lean_dec(v_unused_5674_);
v___x_5663_ = v___x_5661_;
v_isShared_5664_ = v_isSharedCheck_5673_;
goto v_resetjp_5662_;
}
else
{
lean_dec(v___x_5661_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5673_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5668_; 
v___x_5665_ = lean_box(v___x_5595_);
v___x_5666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5665_);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 1, v_snd_5597_);
lean_ctor_set(v___x_5616_, 0, v___x_5666_);
v___x_5668_ = v___x_5616_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v___x_5666_);
lean_ctor_set(v_reuseFailAlloc_5672_, 1, v_snd_5597_);
v___x_5668_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
lean_object* v___x_5670_; 
if (v_isShared_5664_ == 0)
{
lean_ctor_set(v___x_5663_, 0, v___x_5668_);
v___x_5670_ = v___x_5663_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v___x_5668_);
v___x_5670_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
return v___x_5670_;
}
}
}
}
else
{
lean_object* v_a_5675_; lean_object* v___x_5677_; uint8_t v_isShared_5678_; uint8_t v_isSharedCheck_5682_; 
lean_del_object(v___x_5616_);
lean_dec(v_snd_5597_);
v_a_5675_ = lean_ctor_get(v___x_5661_, 0);
v_isSharedCheck_5682_ = !lean_is_exclusive(v___x_5661_);
if (v_isSharedCheck_5682_ == 0)
{
v___x_5677_ = v___x_5661_;
v_isShared_5678_ = v_isSharedCheck_5682_;
goto v_resetjp_5676_;
}
else
{
lean_inc(v_a_5675_);
lean_dec(v___x_5661_);
v___x_5677_ = lean_box(0);
v_isShared_5678_ = v_isSharedCheck_5682_;
goto v_resetjp_5676_;
}
v_resetjp_5676_:
{
lean_object* v___x_5680_; 
if (v_isShared_5678_ == 0)
{
v___x_5680_ = v___x_5677_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_a_5675_);
v___x_5680_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
return v___x_5680_;
}
}
}
}
}
else
{
lean_object* v_a_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5690_; 
lean_del_object(v___x_5620_);
lean_del_object(v___x_5616_);
lean_dec(v_snd_5597_);
lean_dec(v_a_5557_);
lean_dec_ref(v_config_5556_);
lean_dec_ref(v_methods_5555_);
v_a_5683_ = lean_ctor_get(v___x_5623_, 0);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5623_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5685_ = v___x_5623_;
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_a_5683_);
lean_dec(v___x_5623_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5688_; 
if (v_isShared_5686_ == 0)
{
v___x_5688_ = v___x_5685_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5683_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
}
}
}
}
else
{
lean_object* v_a_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5701_; 
lean_dec(v_snd_5597_);
lean_dec(v_a_5557_);
lean_dec_ref(v_config_5556_);
lean_dec_ref(v_methods_5555_);
v_a_5694_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5701_ == 0)
{
v___x_5696_ = v___x_5611_;
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_a_5694_);
lean_dec(v___x_5611_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5699_; 
if (v_isShared_5697_ == 0)
{
v___x_5699_ = v___x_5696_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_a_5694_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
}
}
}
v___jp_5572_:
{
if (lean_obj_tag(v___y_5573_) == 0)
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5586_; 
v_a_5574_ = lean_ctor_get(v___y_5573_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___y_5573_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5576_ = v___y_5573_;
v_isShared_5577_ = v_isSharedCheck_5586_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___y_5573_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5586_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
if (lean_obj_tag(v_a_5574_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5580_; 
lean_dec(v_a_5557_);
lean_dec_ref(v_config_5556_);
lean_dec_ref(v_methods_5555_);
v_a_5578_ = lean_ctor_get(v_a_5574_, 0);
lean_inc(v_a_5578_);
lean_dec_ref_known(v_a_5574_, 1);
if (v_isShared_5577_ == 0)
{
lean_ctor_set(v___x_5576_, 0, v_a_5578_);
v___x_5580_ = v___x_5576_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5578_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
else
{
lean_object* v_a_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; 
lean_del_object(v___x_5576_);
v_a_5582_ = lean_ctor_get(v_a_5574_, 0);
lean_inc(v_a_5582_);
lean_dec_ref_known(v_a_5574_, 1);
v___x_5583_ = lean_unsigned_to_nat(1u);
v___x_5584_ = lean_nat_add(v_a_5557_, v___x_5583_);
lean_dec(v_a_5557_);
v_a_5557_ = v___x_5584_;
v_b_5558_ = v_a_5582_;
goto _start;
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
lean_dec(v_a_5557_);
lean_dec_ref(v_config_5556_);
lean_dec_ref(v_methods_5555_);
v_a_5587_ = lean_ctor_get(v___y_5573_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___y_5573_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___y_5573_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v___y_5573_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5592_; 
if (v_isShared_5590_ == 0)
{
v___x_5592_ = v___x_5589_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
return v___x_5592_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5553_ = stack[0].m_obj;
lean_object* v___x_5554_ = stack[1].m_obj;
lean_object* v_methods_5555_ = stack[2].m_obj;
lean_object* v_config_5556_ = stack[3].m_obj;
lean_object* v_a_5557_ = stack[4].m_obj;
lean_object* v_b_5558_ = stack[5].m_obj;
lean_object* v___y_5559_ = stack[6].m_obj;
lean_object* v___y_5560_ = stack[7].m_obj;
lean_object* v___y_5561_ = stack[8].m_obj;
lean_object* v___y_5562_ = stack[9].m_obj;
lean_object* v___y_5563_ = stack[10].m_obj;
lean_object* v___y_5564_ = stack[11].m_obj;
lean_object* v___y_5565_ = stack[12].m_obj;
lean_object* v___y_5566_ = stack[13].m_obj;
lean_object* v___y_5567_ = stack[14].m_obj;
lean_object* v___y_5568_ = stack[15].m_obj;
lean_object* v___y_5569_ = stack[16].m_obj;
lean_object* v___y_5570_ = stack[17].m_obj;
lean_object* v_res_5705_;
v_res_5705_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5553_, v___x_5554_, v_methods_5555_, v_config_5556_, v_a_5557_, v_b_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
stack->m_obj
 = v_res_5705_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5706_ = _args[0];
lean_object* v___x_5707_ = _args[1];
lean_object* v_methods_5708_ = _args[2];
lean_object* v_config_5709_ = _args[3];
lean_object* v_a_5710_ = _args[4];
lean_object* v_b_5711_ = _args[5];
lean_object* v___y_5712_ = _args[6];
lean_object* v___y_5713_ = _args[7];
lean_object* v___y_5714_ = _args[8];
lean_object* v___y_5715_ = _args[9];
lean_object* v___y_5716_ = _args[10];
lean_object* v___y_5717_ = _args[11];
lean_object* v___y_5718_ = _args[12];
lean_object* v___y_5719_ = _args[13];
lean_object* v___y_5720_ = _args[14];
lean_object* v___y_5721_ = _args[15];
lean_object* v___y_5722_ = _args[16];
lean_object* v___y_5723_ = _args[17];
lean_object* v___y_5724_ = _args[18];
_start:
{
lean_object* v_res_5725_; 
v_res_5725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5706_, v___x_5707_, v_methods_5708_, v_config_5709_, v_a_5710_, v_b_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
lean_dec(v___y_5723_);
lean_dec_ref(v___y_5722_);
lean_dec(v___y_5721_);
lean_dec_ref(v___y_5720_);
lean_dec(v___y_5719_);
lean_dec_ref(v___y_5718_);
lean_dec(v___y_5717_);
lean_dec_ref(v___y_5716_);
lean_dec(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec(v___y_5712_);
lean_dec_ref(v___x_5707_);
lean_dec(v_upperBound_5706_);
return v_res_5725_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5726_, lean_object* v_config_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_){
_start:
{
lean_object* v___x_5741_; lean_object* v_hypotheses_5742_; lean_object* v___x_5743_; lean_object* v_newHyps_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; 
v___x_5741_ = lean_st_ref_get(v_a_5730_);
v_hypotheses_5742_ = lean_ctor_get(v___x_5741_, 3);
lean_inc_ref(v_hypotheses_5742_);
lean_dec(v___x_5741_);
v___x_5743_ = lean_array_get_size(v_hypotheses_5742_);
v_newHyps_5744_ = lean_mk_empty_array_with_capacity(v___x_5743_);
v___x_5745_ = lean_unsigned_to_nat(0u);
v___x_5746_ = lean_box(0);
v___x_5747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5746_);
lean_ctor_set(v___x_5747_, 1, v_newHyps_5744_);
v___x_5748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5743_, v_hypotheses_5742_, v_methods_5726_, v_config_5727_, v___x_5745_, v___x_5747_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_);
lean_dec_ref(v_hypotheses_5742_);
if (lean_obj_tag(v___x_5748_) == 0)
{
lean_object* v_a_5749_; lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5778_; 
v_a_5749_ = lean_ctor_get(v___x_5748_, 0);
v_isSharedCheck_5778_ = !lean_is_exclusive(v___x_5748_);
if (v_isSharedCheck_5778_ == 0)
{
v___x_5751_ = v___x_5748_;
v_isShared_5752_ = v_isSharedCheck_5778_;
goto v_resetjp_5750_;
}
else
{
lean_inc(v_a_5749_);
lean_dec(v___x_5748_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5778_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v_fst_5753_; 
v_fst_5753_ = lean_ctor_get(v_a_5749_, 0);
if (lean_obj_tag(v_fst_5753_) == 0)
{
lean_object* v_snd_5754_; lean_object* v___x_5755_; lean_object* v_caches_5756_; lean_object* v_typeAnalysis_5757_; lean_object* v_target_5758_; uint8_t v_didChange_5759_; lean_object* v___x_5761_; uint8_t v_isShared_5762_; uint8_t v_isSharedCheck_5772_; 
v_snd_5754_ = lean_ctor_get(v_a_5749_, 1);
lean_inc(v_snd_5754_);
lean_dec(v_a_5749_);
v___x_5755_ = lean_st_ref_take(v_a_5730_);
v_caches_5756_ = lean_ctor_get(v___x_5755_, 0);
v_typeAnalysis_5757_ = lean_ctor_get(v___x_5755_, 1);
v_target_5758_ = lean_ctor_get(v___x_5755_, 2);
v_didChange_5759_ = lean_ctor_get_uint8(v___x_5755_, sizeof(void*)*4);
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5755_);
if (v_isSharedCheck_5772_ == 0)
{
lean_object* v_unused_5773_; 
v_unused_5773_ = lean_ctor_get(v___x_5755_, 3);
lean_dec(v_unused_5773_);
v___x_5761_ = v___x_5755_;
v_isShared_5762_ = v_isSharedCheck_5772_;
goto v_resetjp_5760_;
}
else
{
lean_inc(v_target_5758_);
lean_inc(v_typeAnalysis_5757_);
lean_inc(v_caches_5756_);
lean_dec(v___x_5755_);
v___x_5761_ = lean_box(0);
v_isShared_5762_ = v_isSharedCheck_5772_;
goto v_resetjp_5760_;
}
v_resetjp_5760_:
{
lean_object* v___x_5764_; 
if (v_isShared_5762_ == 0)
{
lean_ctor_set(v___x_5761_, 3, v_snd_5754_);
v___x_5764_ = v___x_5761_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_caches_5756_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v_typeAnalysis_5757_);
lean_ctor_set(v_reuseFailAlloc_5771_, 2, v_target_5758_);
lean_ctor_set(v_reuseFailAlloc_5771_, 3, v_snd_5754_);
lean_ctor_set_uint8(v_reuseFailAlloc_5771_, sizeof(void*)*4, v_didChange_5759_);
v___x_5764_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
lean_object* v___x_5765_; uint8_t v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5769_; 
v___x_5765_ = lean_st_ref_put(v_a_5730_, v___x_5764_);
v___x_5766_ = 0;
v___x_5767_ = lean_box(v___x_5766_);
if (v_isShared_5752_ == 0)
{
lean_ctor_set(v___x_5751_, 0, v___x_5767_);
v___x_5769_ = v___x_5751_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5767_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
return v___x_5769_;
}
}
}
}
else
{
lean_object* v_val_5774_; lean_object* v___x_5776_; 
lean_inc_ref(v_fst_5753_);
lean_dec(v_a_5749_);
v_val_5774_ = lean_ctor_get(v_fst_5753_, 0);
lean_inc(v_val_5774_);
lean_dec_ref_known(v_fst_5753_, 1);
if (v_isShared_5752_ == 0)
{
lean_ctor_set(v___x_5751_, 0, v_val_5774_);
v___x_5776_ = v___x_5751_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_val_5774_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
}
else
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5786_; 
v_a_5779_ = lean_ctor_get(v___x_5748_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5748_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5781_ = v___x_5748_;
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5748_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v___x_5784_; 
if (v_isShared_5782_ == 0)
{
v___x_5784_ = v___x_5781_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_a_5779_);
v___x_5784_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
return v___x_5784_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_methods_5726_ = stack[0].m_obj;
lean_object* v_config_5727_ = stack[1].m_obj;
lean_object* v_a_5728_ = stack[2].m_obj;
lean_object* v_a_5729_ = stack[3].m_obj;
lean_object* v_a_5730_ = stack[4].m_obj;
lean_object* v_a_5731_ = stack[5].m_obj;
lean_object* v_a_5732_ = stack[6].m_obj;
lean_object* v_a_5733_ = stack[7].m_obj;
lean_object* v_a_5734_ = stack[8].m_obj;
lean_object* v_a_5735_ = stack[9].m_obj;
lean_object* v_a_5736_ = stack[10].m_obj;
lean_object* v_a_5737_ = stack[11].m_obj;
lean_object* v_a_5738_ = stack[12].m_obj;
lean_object* v_a_5739_ = stack[13].m_obj;
lean_object* v_res_5787_;
v_res_5787_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5726_, v_config_5727_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_);
stack->m_obj
 = v_res_5787_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5788_, lean_object* v_config_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_){
_start:
{
lean_object* v_res_5803_; 
v_res_5803_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5788_, v_config_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_, v_a_5799_, v_a_5800_, v_a_5801_);
lean_dec(v_a_5801_);
lean_dec_ref(v_a_5800_);
lean_dec(v_a_5799_);
lean_dec_ref(v_a_5798_);
lean_dec(v_a_5797_);
lean_dec_ref(v_a_5796_);
lean_dec(v_a_5795_);
lean_dec_ref(v_a_5794_);
lean_dec(v_a_5793_);
lean_dec(v_a_5792_);
lean_dec_ref(v_a_5791_);
lean_dec(v_a_5790_);
return v_res_5803_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5804_, lean_object* v_msg_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_){
_start:
{
lean_object* v___x_5819_; 
v___x_5819_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5804_, v_msg_5805_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
return v___x_5819_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5804_ = stack[0].m_obj;
lean_object* v_msg_5805_ = stack[1].m_obj;
lean_object* v___y_5806_ = stack[2].m_obj;
lean_object* v___y_5807_ = stack[3].m_obj;
lean_object* v___y_5808_ = stack[4].m_obj;
lean_object* v___y_5809_ = stack[5].m_obj;
lean_object* v___y_5810_ = stack[6].m_obj;
lean_object* v___y_5811_ = stack[7].m_obj;
lean_object* v___y_5812_ = stack[8].m_obj;
lean_object* v___y_5813_ = stack[9].m_obj;
lean_object* v___y_5814_ = stack[10].m_obj;
lean_object* v___y_5815_ = stack[11].m_obj;
lean_object* v___y_5816_ = stack[12].m_obj;
lean_object* v___y_5817_ = stack[13].m_obj;
lean_object* v_res_5820_;
v_res_5820_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5804_, v_msg_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
stack->m_obj
 = v_res_5820_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5821_, lean_object* v_msg_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_){
_start:
{
lean_object* v_res_5836_; 
v_res_5836_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5821_, v_msg_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_);
lean_dec(v___y_5834_);
lean_dec_ref(v___y_5833_);
lean_dec(v___y_5832_);
lean_dec_ref(v___y_5831_);
lean_dec(v___y_5830_);
lean_dec_ref(v___y_5829_);
lean_dec(v___y_5828_);
lean_dec_ref(v___y_5827_);
lean_dec(v___y_5826_);
lean_dec(v___y_5825_);
lean_dec_ref(v___y_5824_);
lean_dec(v___y_5823_);
return v_res_5836_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5837_, lean_object* v___x_5838_, lean_object* v_methods_5839_, lean_object* v_config_5840_, lean_object* v_inst_5841_, lean_object* v_R_5842_, lean_object* v_a_5843_, lean_object* v_b_5844_, lean_object* v_c_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_){
_start:
{
lean_object* v___x_5859_; 
v___x_5859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5837_, v___x_5838_, v_methods_5839_, v_config_5840_, v_a_5843_, v_b_5844_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_);
return v___x_5859_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5837_ = stack[0].m_obj;
lean_object* v___x_5838_ = stack[1].m_obj;
lean_object* v_methods_5839_ = stack[2].m_obj;
lean_object* v_config_5840_ = stack[3].m_obj;
lean_object* v_a_5843_ = stack[6].m_obj;
lean_object* v_b_5844_ = stack[7].m_obj;
lean_object* v___y_5846_ = stack[9].m_obj;
lean_object* v___y_5847_ = stack[10].m_obj;
lean_object* v___y_5848_ = stack[11].m_obj;
lean_object* v___y_5849_ = stack[12].m_obj;
lean_object* v___y_5850_ = stack[13].m_obj;
lean_object* v___y_5851_ = stack[14].m_obj;
lean_object* v___y_5852_ = stack[15].m_obj;
lean_object* v___y_5853_ = stack[16].m_obj;
lean_object* v___y_5854_ = stack[17].m_obj;
lean_object* v___y_5855_ = stack[18].m_obj;
lean_object* v___y_5856_ = stack[19].m_obj;
lean_object* v___y_5857_ = stack[20].m_obj;
lean_object* v_res_5860_;
v_res_5860_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5837_, v___x_5838_, v_methods_5839_, v_config_5840_, lean_box(0), lean_box(0), v_a_5843_, v_b_5844_, lean_box(0), v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_);
stack->m_obj
 = v_res_5860_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5861_ = _args[0];
lean_object* v___x_5862_ = _args[1];
lean_object* v_methods_5863_ = _args[2];
lean_object* v_config_5864_ = _args[3];
lean_object* v_inst_5865_ = _args[4];
lean_object* v_R_5866_ = _args[5];
lean_object* v_a_5867_ = _args[6];
lean_object* v_b_5868_ = _args[7];
lean_object* v_c_5869_ = _args[8];
lean_object* v___y_5870_ = _args[9];
lean_object* v___y_5871_ = _args[10];
lean_object* v___y_5872_ = _args[11];
lean_object* v___y_5873_ = _args[12];
lean_object* v___y_5874_ = _args[13];
lean_object* v___y_5875_ = _args[14];
lean_object* v___y_5876_ = _args[15];
lean_object* v___y_5877_ = _args[16];
lean_object* v___y_5878_ = _args[17];
lean_object* v___y_5879_ = _args[18];
lean_object* v___y_5880_ = _args[19];
lean_object* v___y_5881_ = _args[20];
lean_object* v___y_5882_ = _args[21];
_start:
{
lean_object* v_res_5883_; 
v_res_5883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5861_, v___x_5862_, v_methods_5863_, v_config_5864_, v_inst_5865_, v_R_5866_, v_a_5867_, v_b_5868_, v_c_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_);
lean_dec(v___y_5881_);
lean_dec_ref(v___y_5880_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec(v___y_5877_);
lean_dec_ref(v___y_5876_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec(v___y_5873_);
lean_dec(v___y_5872_);
lean_dec_ref(v___y_5871_);
lean_dec(v___y_5870_);
lean_dec_ref(v___x_5862_);
lean_dec(v_upperBound_5861_);
return v_res_5883_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5884_, lean_object* v_config_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_, lean_object* v_a_5892_, lean_object* v_a_5893_, lean_object* v_a_5894_, lean_object* v_a_5895_, lean_object* v_a_5896_){
_start:
{
lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; 
v___x_5898_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5899_ = lean_st_mk_ref(v___x_5898_);
v___x_5900_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5884_, v_config_5885_, v___x_5899_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, v_a_5894_, v_a_5895_, v_a_5896_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_object* v_a_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5909_; 
v_a_5901_ = lean_ctor_get(v___x_5900_, 0);
v_isSharedCheck_5909_ = !lean_is_exclusive(v___x_5900_);
if (v_isSharedCheck_5909_ == 0)
{
v___x_5903_ = v___x_5900_;
v_isShared_5904_ = v_isSharedCheck_5909_;
goto v_resetjp_5902_;
}
else
{
lean_inc(v_a_5901_);
lean_dec(v___x_5900_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5909_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v___x_5905_; lean_object* v___x_5907_; 
v___x_5905_ = lean_st_ref_get(v___x_5899_);
lean_dec(v___x_5899_);
lean_dec(v___x_5905_);
if (v_isShared_5904_ == 0)
{
v___x_5907_ = v___x_5903_;
goto v_reusejp_5906_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_a_5901_);
v___x_5907_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5906_;
}
v_reusejp_5906_:
{
return v___x_5907_;
}
}
}
else
{
lean_dec(v___x_5899_);
return v___x_5900_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_methods_5884_ = stack[0].m_obj;
lean_object* v_config_5885_ = stack[1].m_obj;
lean_object* v_a_5886_ = stack[2].m_obj;
lean_object* v_a_5887_ = stack[3].m_obj;
lean_object* v_a_5888_ = stack[4].m_obj;
lean_object* v_a_5889_ = stack[5].m_obj;
lean_object* v_a_5890_ = stack[6].m_obj;
lean_object* v_a_5891_ = stack[7].m_obj;
lean_object* v_a_5892_ = stack[8].m_obj;
lean_object* v_a_5893_ = stack[9].m_obj;
lean_object* v_a_5894_ = stack[10].m_obj;
lean_object* v_a_5895_ = stack[11].m_obj;
lean_object* v_a_5896_ = stack[12].m_obj;
lean_object* v_res_5910_;
v_res_5910_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5884_, v_config_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, v_a_5894_, v_a_5895_, v_a_5896_);
stack->m_obj
 = v_res_5910_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5911_, lean_object* v_config_5912_, lean_object* v_a_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_){
_start:
{
lean_object* v_res_5925_; 
v_res_5925_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5911_, v_config_5912_, v_a_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_, v_a_5922_, v_a_5923_);
lean_dec(v_a_5923_);
lean_dec_ref(v_a_5922_);
lean_dec(v_a_5921_);
lean_dec_ref(v_a_5920_);
lean_dec(v_a_5919_);
lean_dec_ref(v_a_5918_);
lean_dec(v_a_5917_);
lean_dec_ref(v_a_5916_);
lean_dec(v_a_5915_);
lean_dec(v_a_5914_);
lean_dec_ref(v_a_5913_);
return v_res_5925_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; 
v___x_5927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5928_ = l_Lean_stringToMessageData(v___x_5927_);
return v___x_5928_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5929_, lean_object* v_x_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_){
_start:
{
lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; 
v___x_5943_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5944_ = l_Lean_MessageData_ofName(v_name_5929_);
v___x_5945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5943_);
lean_ctor_set(v___x_5945_, 1, v___x_5944_);
v___x_5946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5945_);
return v___x_5946_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_5929_ = stack[0].m_obj;
lean_object* v_x_5930_ = stack[1].m_obj;
lean_object* v___y_5931_ = stack[2].m_obj;
lean_object* v___y_5932_ = stack[3].m_obj;
lean_object* v___y_5933_ = stack[4].m_obj;
lean_object* v___y_5934_ = stack[5].m_obj;
lean_object* v___y_5935_ = stack[6].m_obj;
lean_object* v___y_5936_ = stack[7].m_obj;
lean_object* v___y_5937_ = stack[8].m_obj;
lean_object* v___y_5938_ = stack[9].m_obj;
lean_object* v___y_5939_ = stack[10].m_obj;
lean_object* v___y_5940_ = stack[11].m_obj;
lean_object* v___y_5941_ = stack[12].m_obj;
lean_object* v_res_5947_;
v_res_5947_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5929_, v_x_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_);
stack->m_obj
 = v_res_5947_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5948_, lean_object* v_x_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_){
_start:
{
lean_object* v_res_5962_; 
v_res_5962_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5948_, v_x_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_, v___y_5960_);
lean_dec(v___y_5960_);
lean_dec_ref(v___y_5959_);
lean_dec(v___y_5958_);
lean_dec_ref(v___y_5957_);
lean_dec(v___y_5956_);
lean_dec_ref(v___y_5955_);
lean_dec(v___y_5954_);
lean_dec_ref(v___y_5953_);
lean_dec(v___y_5952_);
lean_dec(v___y_5951_);
lean_dec_ref(v___y_5950_);
lean_dec_ref(v_x_5949_);
return v_res_5962_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5963_; 
v___x_5963_ = l_instMonadExceptOfEIO___redArg();
return v___x_5963_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5964_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5965_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5964_);
return v___x_5965_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___x_5966_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5967_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5966_);
return v___x_5967_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5968_; lean_object* v___x_5969_; 
v___x_5968_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5969_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5968_);
return v___x_5969_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; 
v___x_5970_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5971_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5970_);
return v___x_5971_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5972_; lean_object* v___x_5973_; 
v___x_5972_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5973_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5972_);
return v___x_5973_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; 
v___x_5974_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5975_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5974_);
return v___x_5975_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5976_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5977_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5976_);
return v___x_5977_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5978_; lean_object* v___x_5979_; 
v___x_5978_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5979_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5978_);
return v___x_5979_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5980_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5981_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5980_);
return v___x_5981_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5982_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5983_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5982_);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5984_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5985_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5984_);
return v___x_5985_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5987_; double v___x_5988_; 
v___x_5987_ = lean_unsigned_to_nat(1000000000u);
v___x_5988_ = lean_float_of_nat(v___x_5987_);
return v___x_5988_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_){
_start:
{
lean_object* v___x_6002_; lean_object* v_toApplicative_6003_; lean_object* v_toFunctor_6004_; lean_object* v_toSeq_6005_; lean_object* v_toSeqLeft_6006_; lean_object* v_toSeqRight_6007_; lean_object* v___f_6008_; lean_object* v___f_6009_; lean_object* v___f_6010_; lean_object* v___f_6011_; lean_object* v___x_6012_; lean_object* v___f_6013_; lean_object* v___f_6014_; lean_object* v___f_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v_toApplicative_6019_; lean_object* v___x_6021_; uint8_t v_isShared_6022_; uint8_t v_isSharedCheck_6162_; 
v___x_6002_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_6003_ = lean_ctor_get(v___x_6002_, 0);
v_toFunctor_6004_ = lean_ctor_get(v_toApplicative_6003_, 0);
v_toSeq_6005_ = lean_ctor_get(v_toApplicative_6003_, 2);
v_toSeqLeft_6006_ = lean_ctor_get(v_toApplicative_6003_, 3);
v_toSeqRight_6007_ = lean_ctor_get(v_toApplicative_6003_, 4);
v___f_6008_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_6009_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_6004_, 2);
v___f_6010_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_6010_, 0, v_toFunctor_6004_);
v___f_6011_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_6011_, 0, v_toFunctor_6004_);
v___x_6012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___f_6010_);
lean_ctor_set(v___x_6012_, 1, v___f_6011_);
lean_inc(v_toSeqRight_6007_);
v___f_6013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_6013_, 0, v_toSeqRight_6007_);
lean_inc(v_toSeqLeft_6006_);
v___f_6014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_6014_, 0, v_toSeqLeft_6006_);
lean_inc(v_toSeq_6005_);
v___f_6015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_6015_, 0, v_toSeq_6005_);
v___x_6016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6012_);
lean_ctor_set(v___x_6016_, 1, v___f_6008_);
lean_ctor_set(v___x_6016_, 2, v___f_6015_);
lean_ctor_set(v___x_6016_, 3, v___f_6014_);
lean_ctor_set(v___x_6016_, 4, v___f_6013_);
v___x_6017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___f_6009_);
v___x_6018_ = l_StateRefT_x27_instMonad___redArg(v___x_6017_);
v_toApplicative_6019_ = lean_ctor_get(v___x_6018_, 0);
v_isSharedCheck_6162_ = !lean_is_exclusive(v___x_6018_);
if (v_isSharedCheck_6162_ == 0)
{
lean_object* v_unused_6163_; 
v_unused_6163_ = lean_ctor_get(v___x_6018_, 1);
lean_dec(v_unused_6163_);
v___x_6021_ = v___x_6018_;
v_isShared_6022_ = v_isSharedCheck_6162_;
goto v_resetjp_6020_;
}
else
{
lean_inc(v_toApplicative_6019_);
lean_dec(v___x_6018_);
v___x_6021_ = lean_box(0);
v_isShared_6022_ = v_isSharedCheck_6162_;
goto v_resetjp_6020_;
}
v_resetjp_6020_:
{
lean_object* v_toFunctor_6023_; lean_object* v_toSeq_6024_; lean_object* v_toSeqLeft_6025_; lean_object* v_toSeqRight_6026_; lean_object* v___x_6028_; uint8_t v_isShared_6029_; uint8_t v_isSharedCheck_6160_; 
v_toFunctor_6023_ = lean_ctor_get(v_toApplicative_6019_, 0);
v_toSeq_6024_ = lean_ctor_get(v_toApplicative_6019_, 2);
v_toSeqLeft_6025_ = lean_ctor_get(v_toApplicative_6019_, 3);
v_toSeqRight_6026_ = lean_ctor_get(v_toApplicative_6019_, 4);
v_isSharedCheck_6160_ = !lean_is_exclusive(v_toApplicative_6019_);
if (v_isSharedCheck_6160_ == 0)
{
lean_object* v_unused_6161_; 
v_unused_6161_ = lean_ctor_get(v_toApplicative_6019_, 1);
lean_dec(v_unused_6161_);
v___x_6028_ = v_toApplicative_6019_;
v_isShared_6029_ = v_isSharedCheck_6160_;
goto v_resetjp_6027_;
}
else
{
lean_inc(v_toSeqRight_6026_);
lean_inc(v_toSeqLeft_6025_);
lean_inc(v_toSeq_6024_);
lean_inc(v_toFunctor_6023_);
lean_dec(v_toApplicative_6019_);
v___x_6028_ = lean_box(0);
v_isShared_6029_ = v_isSharedCheck_6160_;
goto v_resetjp_6027_;
}
v_resetjp_6027_:
{
lean_object* v___f_6030_; lean_object* v___f_6031_; lean_object* v___f_6032_; lean_object* v___f_6033_; lean_object* v___x_6034_; lean_object* v___f_6035_; lean_object* v___f_6036_; lean_object* v___f_6037_; lean_object* v___x_6039_; 
v___f_6030_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_6031_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_6023_);
v___f_6032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_6032_, 0, v_toFunctor_6023_);
v___f_6033_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_6033_, 0, v_toFunctor_6023_);
v___x_6034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___f_6032_);
lean_ctor_set(v___x_6034_, 1, v___f_6033_);
v___f_6035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_6035_, 0, v_toSeqRight_6026_);
v___f_6036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_6036_, 0, v_toSeqLeft_6025_);
v___f_6037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_6037_, 0, v_toSeq_6024_);
if (v_isShared_6029_ == 0)
{
lean_ctor_set(v___x_6028_, 4, v___f_6035_);
lean_ctor_set(v___x_6028_, 3, v___f_6036_);
lean_ctor_set(v___x_6028_, 2, v___f_6037_);
lean_ctor_set(v___x_6028_, 1, v___f_6030_);
lean_ctor_set(v___x_6028_, 0, v___x_6034_);
v___x_6039_ = v___x_6028_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6159_; 
v_reuseFailAlloc_6159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6159_, 0, v___x_6034_);
lean_ctor_set(v_reuseFailAlloc_6159_, 1, v___f_6030_);
lean_ctor_set(v_reuseFailAlloc_6159_, 2, v___f_6037_);
lean_ctor_set(v_reuseFailAlloc_6159_, 3, v___f_6036_);
lean_ctor_set(v_reuseFailAlloc_6159_, 4, v___f_6035_);
v___x_6039_ = v_reuseFailAlloc_6159_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
lean_object* v___x_6041_; 
if (v_isShared_6022_ == 0)
{
lean_ctor_set(v___x_6021_, 1, v___f_6031_);
lean_ctor_set(v___x_6021_, 0, v___x_6039_);
v___x_6041_ = v___x_6021_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6158_; 
v_reuseFailAlloc_6158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6158_, 0, v___x_6039_);
lean_ctor_set(v_reuseFailAlloc_6158_, 1, v___f_6031_);
v___x_6041_ = v_reuseFailAlloc_6158_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v_toMonadRef_6051_; lean_object* v___x_6052_; lean_object* v_name_6053_; lean_object* v_run_x27_6054_; lean_object* v___x_6056_; uint8_t v_isShared_6057_; uint8_t v_isSharedCheck_6157_; 
v___x_6042_ = l_StateRefT_x27_instMonad___redArg(v___x_6041_);
v___x_6043_ = l_ReaderT_instMonad___redArg(v___x_6042_);
v___x_6044_ = l_StateRefT_x27_instMonad___redArg(v___x_6043_);
v___x_6045_ = l_ReaderT_instMonad___redArg(v___x_6044_);
v___x_6046_ = l_ReaderT_instMonad___redArg(v___x_6045_);
v___x_6047_ = l_StateRefT_x27_instMonad___redArg(v___x_6046_);
v___x_6048_ = l_ReaderT_instMonad___redArg(v___x_6047_);
v___x_6049_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_6050_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_6051_ = lean_ctor_get(v___x_6050_, 0);
v___x_6052_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_name_6053_ = lean_ctor_get(v_pass_5989_, 0);
v_run_x27_6054_ = lean_ctor_get(v_pass_5989_, 1);
v_isSharedCheck_6157_ = !lean_is_exclusive(v_pass_5989_);
if (v_isSharedCheck_6157_ == 0)
{
v___x_6056_ = v_pass_5989_;
v_isShared_6057_ = v_isSharedCheck_6157_;
goto v_resetjp_6055_;
}
else
{
lean_inc(v_run_x27_6054_);
lean_inc(v_name_6053_);
lean_dec(v_pass_5989_);
v___x_6056_ = lean_box(0);
v_isShared_6057_ = v_isSharedCheck_6157_;
goto v_resetjp_6055_;
}
v_resetjp_6055_:
{
lean_object* v___x_6058_; lean_object* v_toCold_6059_; lean_object* v_options_6060_; uint8_t v_hasTrace_6061_; 
v___x_6058_ = l_Lean_KVMap_instValueBool;
v_toCold_6059_ = lean_ctor_get(v_a_5999_, 0);
v_options_6060_ = lean_ctor_get(v_toCold_6059_, 2);
v_hasTrace_6061_ = lean_ctor_get_uint8(v_options_6060_, sizeof(void*)*1);
if (v_hasTrace_6061_ == 0)
{
lean_object* v___x_6062_; 
lean_del_object(v___x_6056_);
lean_dec(v_name_6053_);
lean_dec_ref(v___x_6048_);
lean_inc(v_a_6000_);
lean_inc_ref(v_a_5999_);
lean_inc(v_a_5998_);
lean_inc_ref(v_a_5997_);
lean_inc(v_a_5996_);
lean_inc_ref(v_a_5995_);
lean_inc(v_a_5994_);
lean_inc_ref(v_a_5993_);
lean_inc(v_a_5992_);
lean_inc(v_a_5991_);
lean_inc_ref(v_a_5990_);
v___x_6062_ = lean_apply_12(v_run_x27_6054_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, lean_box(0));
return v___x_6062_;
}
else
{
lean_object* v_inheritedTraceOptions_6063_; lean_object* v___f_6064_; lean_object* v___f_6065_; lean_object* v___f_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; uint8_t v___x_6070_; lean_object* v___y_6072_; lean_object* v___y_6073_; lean_object* v_a_6074_; lean_object* v___y_6090_; lean_object* v___y_6091_; lean_object* v_a_6092_; 
v_inheritedTraceOptions_6063_ = lean_ctor_get(v_toCold_6059_, 11);
v___f_6064_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6064_, 0, v_name_6053_);
v___f_6065_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_6066_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_6067_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6068_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6069_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6063_, v_options_6060_, v___x_6069_);
if (v___x_6070_ == 0)
{
lean_object* v___x_6153_; lean_object* v___x_6154_; uint8_t v___x_6155_; 
v___x_6153_ = l_Lean_trace_profiler;
v___x_6154_ = l_Lean_Option_get___redArg(v___x_6058_, v_options_6060_, v___x_6153_);
v___x_6155_ = lean_unbox(v___x_6154_);
lean_dec(v___x_6154_);
if (v___x_6155_ == 0)
{
lean_object* v___x_6156_; 
lean_dec_ref(v___f_6064_);
lean_del_object(v___x_6056_);
lean_dec_ref(v___x_6048_);
lean_inc(v_a_6000_);
lean_inc_ref(v_a_5999_);
lean_inc(v_a_5998_);
lean_inc_ref(v_a_5997_);
lean_inc(v_a_5996_);
lean_inc_ref(v_a_5995_);
lean_inc(v_a_5994_);
lean_inc_ref(v_a_5993_);
lean_inc(v_a_5992_);
lean_inc(v_a_5991_);
lean_inc_ref(v_a_5990_);
v___x_6156_ = lean_apply_12(v_run_x27_6054_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, lean_box(0));
return v___x_6156_;
}
else
{
goto v___jp_6102_;
}
}
else
{
goto v___jp_6102_;
}
v___jp_6071_:
{
lean_object* v___x_6075_; double v___x_6076_; double v___x_6077_; double v___x_6078_; double v___x_6079_; double v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6084_; 
v___x_6075_ = lean_io_mono_nanos_now();
v___x_6076_ = lean_float_of_nat(v___y_6072_);
v___x_6077_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6078_ = lean_float_div(v___x_6076_, v___x_6077_);
v___x_6079_ = lean_float_of_nat(v___x_6075_);
v___x_6080_ = lean_float_div(v___x_6079_, v___x_6077_);
v___x_6081_ = lean_box_float(v___x_6078_);
v___x_6082_ = lean_box_float(v___x_6080_);
if (v_isShared_6057_ == 0)
{
lean_ctor_set(v___x_6056_, 1, v___x_6082_);
lean_ctor_set(v___x_6056_, 0, v___x_6081_);
v___x_6084_ = v___x_6056_;
goto v_reusejp_6083_;
}
else
{
lean_object* v_reuseFailAlloc_6088_; 
v_reuseFailAlloc_6088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6088_, 0, v___x_6081_);
lean_ctor_set(v_reuseFailAlloc_6088_, 1, v___x_6082_);
v___x_6084_ = v_reuseFailAlloc_6088_;
goto v_reusejp_6083_;
}
v_reusejp_6083_:
{
lean_object* v___x_6085_; lean_object* v___x_28875__overap_6086_; lean_object* v___x_6087_; 
v___x_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6085_, 0, v_a_6074_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
lean_inc_ref(v_toMonadRef_6051_);
v___x_28875__overap_6086_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_6048_, v___x_6049_, v_toMonadRef_6051_, v___f_6065_, lean_box(0), v___x_6052_, v___f_6066_, v___x_6067_, v_hasTrace_6061_, v___x_6068_, v_options_6060_, v___x_6070_, v___y_6073_, v___f_6064_, v___x_6085_);
lean_inc(v_a_6000_);
lean_inc_ref(v_a_5999_);
lean_inc(v_a_5998_);
lean_inc_ref(v_a_5997_);
lean_inc(v_a_5996_);
lean_inc_ref(v_a_5995_);
lean_inc(v_a_5994_);
lean_inc_ref(v_a_5993_);
lean_inc(v_a_5992_);
lean_inc(v_a_5991_);
lean_inc_ref(v_a_5990_);
v___x_6087_ = lean_apply_12(v___x_28875__overap_6086_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, lean_box(0));
return v___x_6087_;
}
}
v___jp_6089_:
{
lean_object* v___x_6093_; double v___x_6094_; double v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_28896__overap_6100_; lean_object* v___x_6101_; 
v___x_6093_ = lean_io_get_num_heartbeats();
v___x_6094_ = lean_float_of_nat(v___y_6090_);
v___x_6095_ = lean_float_of_nat(v___x_6093_);
v___x_6096_ = lean_box_float(v___x_6094_);
v___x_6097_ = lean_box_float(v___x_6095_);
v___x_6098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6096_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
v___x_6099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6099_, 0, v_a_6092_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
lean_inc_ref(v_toMonadRef_6051_);
v___x_28896__overap_6100_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_6048_, v___x_6049_, v_toMonadRef_6051_, v___f_6065_, lean_box(0), v___x_6052_, v___f_6066_, v___x_6067_, v_hasTrace_6061_, v___x_6068_, v_options_6060_, v___x_6070_, v___y_6091_, v___f_6064_, v___x_6099_);
lean_inc(v_a_6000_);
lean_inc_ref(v_a_5999_);
lean_inc(v_a_5998_);
lean_inc_ref(v_a_5997_);
lean_inc(v_a_5996_);
lean_inc_ref(v_a_5995_);
lean_inc(v_a_5994_);
lean_inc_ref(v_a_5993_);
lean_inc(v_a_5992_);
lean_inc(v_a_5991_);
lean_inc_ref(v_a_5990_);
v___x_6101_ = lean_apply_12(v___x_28896__overap_6100_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, lean_box(0));
return v___x_6101_;
}
v___jp_6102_:
{
lean_object* v___x_28853__overap_6103_; lean_object* v___x_6104_; 
lean_inc_ref(v___x_6048_);
v___x_28853__overap_6103_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_6048_, v___x_6049_);
lean_inc(v_a_6000_);
lean_inc_ref(v_a_5999_);
lean_inc(v_a_5998_);
lean_inc_ref(v_a_5997_);
lean_inc(v_a_5996_);
lean_inc_ref(v_a_5995_);
lean_inc(v_a_5994_);
lean_inc_ref(v_a_5993_);
lean_inc(v_a_5992_);
lean_inc(v_a_5991_);
lean_inc_ref(v_a_5990_);
v___x_6104_ = lean_apply_12(v___x_28853__overap_6103_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, lean_box(0));
if (lean_obj_tag(v___x_6104_) == 0)
{
lean_object* v_a_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; uint8_t v___x_6108_; 
v_a_6105_ = lean_ctor_get(v___x_6104_, 0);
lean_inc(v_a_6105_);
lean_dec_ref_known(v___x_6104_, 1);
v___x_6106_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6107_ = l_Lean_Option_get___redArg(v___x_6058_, v_options_6060_, v___x_6106_);
v___x_6108_ = lean_unbox(v___x_6107_);
lean_dec(v___x_6107_);
if (v___x_6108_ == 0)
{
lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6109_ = lean_io_mono_nanos_now();
lean_inc(v_a_6000_);
lean_inc_ref(v_a_5999_);
lean_inc(v_a_5998_);
lean_inc_ref(v_a_5997_);
lean_inc(v_a_5996_);
lean_inc_ref(v_a_5995_);
lean_inc(v_a_5994_);
lean_inc_ref(v_a_5993_);
lean_inc(v_a_5992_);
lean_inc(v_a_5991_);
lean_inc_ref(v_a_5990_);
v___x_6110_ = lean_apply_12(v_run_x27_6054_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, lean_box(0));
if (lean_obj_tag(v___x_6110_) == 0)
{
lean_object* v_a_6111_; lean_object* v___x_6113_; uint8_t v_isShared_6114_; uint8_t v_isSharedCheck_6118_; 
v_a_6111_ = lean_ctor_get(v___x_6110_, 0);
v_isSharedCheck_6118_ = !lean_is_exclusive(v___x_6110_);
if (v_isSharedCheck_6118_ == 0)
{
v___x_6113_ = v___x_6110_;
v_isShared_6114_ = v_isSharedCheck_6118_;
goto v_resetjp_6112_;
}
else
{
lean_inc(v_a_6111_);
lean_dec(v___x_6110_);
v___x_6113_ = lean_box(0);
v_isShared_6114_ = v_isSharedCheck_6118_;
goto v_resetjp_6112_;
}
v_resetjp_6112_:
{
lean_object* v___x_6116_; 
if (v_isShared_6114_ == 0)
{
lean_ctor_set_tag(v___x_6113_, 1);
v___x_6116_ = v___x_6113_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6111_);
v___x_6116_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
v___y_6072_ = v___x_6109_;
v___y_6073_ = v_a_6105_;
v_a_6074_ = v___x_6116_;
goto v___jp_6071_;
}
}
}
else
{
lean_object* v_a_6119_; lean_object* v___x_6121_; uint8_t v_isShared_6122_; uint8_t v_isSharedCheck_6126_; 
v_a_6119_ = lean_ctor_get(v___x_6110_, 0);
v_isSharedCheck_6126_ = !lean_is_exclusive(v___x_6110_);
if (v_isSharedCheck_6126_ == 0)
{
v___x_6121_ = v___x_6110_;
v_isShared_6122_ = v_isSharedCheck_6126_;
goto v_resetjp_6120_;
}
else
{
lean_inc(v_a_6119_);
lean_dec(v___x_6110_);
v___x_6121_ = lean_box(0);
v_isShared_6122_ = v_isSharedCheck_6126_;
goto v_resetjp_6120_;
}
v_resetjp_6120_:
{
lean_object* v___x_6124_; 
if (v_isShared_6122_ == 0)
{
lean_ctor_set_tag(v___x_6121_, 0);
v___x_6124_ = v___x_6121_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_a_6119_);
v___x_6124_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
v___y_6072_ = v___x_6109_;
v___y_6073_ = v_a_6105_;
v_a_6074_ = v___x_6124_;
goto v___jp_6071_;
}
}
}
}
else
{
lean_object* v___x_6127_; lean_object* v___x_6128_; 
lean_del_object(v___x_6056_);
v___x_6127_ = lean_io_get_num_heartbeats();
lean_inc(v_a_6000_);
lean_inc_ref(v_a_5999_);
lean_inc(v_a_5998_);
lean_inc_ref(v_a_5997_);
lean_inc(v_a_5996_);
lean_inc_ref(v_a_5995_);
lean_inc(v_a_5994_);
lean_inc_ref(v_a_5993_);
lean_inc(v_a_5992_);
lean_inc(v_a_5991_);
lean_inc_ref(v_a_5990_);
v___x_6128_ = lean_apply_12(v_run_x27_6054_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, lean_box(0));
if (lean_obj_tag(v___x_6128_) == 0)
{
lean_object* v_a_6129_; lean_object* v___x_6131_; uint8_t v_isShared_6132_; uint8_t v_isSharedCheck_6136_; 
v_a_6129_ = lean_ctor_get(v___x_6128_, 0);
v_isSharedCheck_6136_ = !lean_is_exclusive(v___x_6128_);
if (v_isSharedCheck_6136_ == 0)
{
v___x_6131_ = v___x_6128_;
v_isShared_6132_ = v_isSharedCheck_6136_;
goto v_resetjp_6130_;
}
else
{
lean_inc(v_a_6129_);
lean_dec(v___x_6128_);
v___x_6131_ = lean_box(0);
v_isShared_6132_ = v_isSharedCheck_6136_;
goto v_resetjp_6130_;
}
v_resetjp_6130_:
{
lean_object* v___x_6134_; 
if (v_isShared_6132_ == 0)
{
lean_ctor_set_tag(v___x_6131_, 1);
v___x_6134_ = v___x_6131_;
goto v_reusejp_6133_;
}
else
{
lean_object* v_reuseFailAlloc_6135_; 
v_reuseFailAlloc_6135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_a_6129_);
v___x_6134_ = v_reuseFailAlloc_6135_;
goto v_reusejp_6133_;
}
v_reusejp_6133_:
{
v___y_6090_ = v___x_6127_;
v___y_6091_ = v_a_6105_;
v_a_6092_ = v___x_6134_;
goto v___jp_6089_;
}
}
}
else
{
lean_object* v_a_6137_; lean_object* v___x_6139_; uint8_t v_isShared_6140_; uint8_t v_isSharedCheck_6144_; 
v_a_6137_ = lean_ctor_get(v___x_6128_, 0);
v_isSharedCheck_6144_ = !lean_is_exclusive(v___x_6128_);
if (v_isSharedCheck_6144_ == 0)
{
v___x_6139_ = v___x_6128_;
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
else
{
lean_inc(v_a_6137_);
lean_dec(v___x_6128_);
v___x_6139_ = lean_box(0);
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
v_resetjp_6138_:
{
lean_object* v___x_6142_; 
if (v_isShared_6140_ == 0)
{
lean_ctor_set_tag(v___x_6139_, 0);
v___x_6142_ = v___x_6139_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v_a_6137_);
v___x_6142_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
v___y_6090_ = v___x_6127_;
v___y_6091_ = v_a_6105_;
v_a_6092_ = v___x_6142_;
goto v___jp_6089_;
}
}
}
}
}
else
{
lean_object* v_a_6145_; lean_object* v___x_6147_; uint8_t v_isShared_6148_; uint8_t v_isSharedCheck_6152_; 
lean_dec_ref(v___f_6064_);
lean_del_object(v___x_6056_);
lean_dec_ref(v_run_x27_6054_);
lean_dec_ref(v___x_6048_);
v_a_6145_ = lean_ctor_get(v___x_6104_, 0);
v_isSharedCheck_6152_ = !lean_is_exclusive(v___x_6104_);
if (v_isSharedCheck_6152_ == 0)
{
v___x_6147_ = v___x_6104_;
v_isShared_6148_ = v_isSharedCheck_6152_;
goto v_resetjp_6146_;
}
else
{
lean_inc(v_a_6145_);
lean_dec(v___x_6104_);
v___x_6147_ = lean_box(0);
v_isShared_6148_ = v_isSharedCheck_6152_;
goto v_resetjp_6146_;
}
v_resetjp_6146_:
{
lean_object* v___x_6150_; 
if (v_isShared_6148_ == 0)
{
v___x_6150_ = v___x_6147_;
goto v_reusejp_6149_;
}
else
{
lean_object* v_reuseFailAlloc_6151_; 
v_reuseFailAlloc_6151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6151_, 0, v_a_6145_);
v___x_6150_ = v_reuseFailAlloc_6151_;
goto v_reusejp_6149_;
}
v_reusejp_6149_:
{
return v___x_6150_;
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
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_pass_5989_ = stack[0].m_obj;
lean_object* v_a_5990_ = stack[1].m_obj;
lean_object* v_a_5991_ = stack[2].m_obj;
lean_object* v_a_5992_ = stack[3].m_obj;
lean_object* v_a_5993_ = stack[4].m_obj;
lean_object* v_a_5994_ = stack[5].m_obj;
lean_object* v_a_5995_ = stack[6].m_obj;
lean_object* v_a_5996_ = stack[7].m_obj;
lean_object* v_a_5997_ = stack[8].m_obj;
lean_object* v_a_5998_ = stack[9].m_obj;
lean_object* v_a_5999_ = stack[10].m_obj;
lean_object* v_a_6000_ = stack[11].m_obj;
lean_object* v_res_6164_;
v_res_6164_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_);
stack->m_obj
 = v_res_6164_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_, lean_object* v_a_6168_, lean_object* v_a_6169_, lean_object* v_a_6170_, lean_object* v_a_6171_, lean_object* v_a_6172_, lean_object* v_a_6173_, lean_object* v_a_6174_, lean_object* v_a_6175_, lean_object* v_a_6176_, lean_object* v_a_6177_){
_start:
{
lean_object* v_res_6178_; 
v_res_6178_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6165_, v_a_6166_, v_a_6167_, v_a_6168_, v_a_6169_, v_a_6170_, v_a_6171_, v_a_6172_, v_a_6173_, v_a_6174_, v_a_6175_, v_a_6176_);
lean_dec(v_a_6176_);
lean_dec_ref(v_a_6175_);
lean_dec(v_a_6174_);
lean_dec_ref(v_a_6173_);
lean_dec(v_a_6172_);
lean_dec_ref(v_a_6171_);
lean_dec(v_a_6170_);
lean_dec_ref(v_a_6169_);
lean_dec(v_a_6168_);
lean_dec(v_a_6167_);
lean_dec_ref(v_a_6166_);
return v_res_6178_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; 
v___x_6179_ = lean_unsigned_to_nat(32u);
v___x_6180_ = lean_mk_empty_array_with_capacity(v___x_6179_);
v___x_6181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6180_);
return v___x_6181_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; 
v___x_6182_ = ((size_t)5ULL);
v___x_6183_ = lean_unsigned_to_nat(0u);
v___x_6184_ = lean_unsigned_to_nat(32u);
v___x_6185_ = lean_mk_empty_array_with_capacity(v___x_6184_);
v___x_6186_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6187_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6187_, 0, v___x_6186_);
lean_ctor_set(v___x_6187_, 1, v___x_6185_);
lean_ctor_set(v___x_6187_, 2, v___x_6183_);
lean_ctor_set(v___x_6187_, 3, v___x_6183_);
lean_ctor_set_usize(v___x_6187_, 4, v___x_6182_);
return v___x_6187_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6188_){
_start:
{
lean_object* v___x_6190_; lean_object* v_traceState_6191_; lean_object* v_traces_6192_; lean_object* v___x_6193_; lean_object* v_traceState_6194_; lean_object* v_env_6195_; lean_object* v_nextMacroScope_6196_; lean_object* v_ngen_6197_; lean_object* v_auxDeclNGen_6198_; lean_object* v_cache_6199_; lean_object* v_recordedDeps_6200_; lean_object* v_messages_6201_; lean_object* v_infoState_6202_; lean_object* v_snapshotTasks_6203_; lean_object* v___x_6205_; uint8_t v_isShared_6206_; uint8_t v_isSharedCheck_6222_; 
v___x_6190_ = lean_st_ref_get(v___y_6188_);
v_traceState_6191_ = lean_ctor_get(v___x_6190_, 4);
lean_inc_ref(v_traceState_6191_);
lean_dec(v___x_6190_);
v_traces_6192_ = lean_ctor_get(v_traceState_6191_, 0);
lean_inc_ref(v_traces_6192_);
lean_dec_ref(v_traceState_6191_);
v___x_6193_ = lean_st_ref_take(v___y_6188_);
v_traceState_6194_ = lean_ctor_get(v___x_6193_, 4);
v_env_6195_ = lean_ctor_get(v___x_6193_, 0);
v_nextMacroScope_6196_ = lean_ctor_get(v___x_6193_, 1);
v_ngen_6197_ = lean_ctor_get(v___x_6193_, 2);
v_auxDeclNGen_6198_ = lean_ctor_get(v___x_6193_, 3);
v_cache_6199_ = lean_ctor_get(v___x_6193_, 5);
v_recordedDeps_6200_ = lean_ctor_get(v___x_6193_, 6);
v_messages_6201_ = lean_ctor_get(v___x_6193_, 7);
v_infoState_6202_ = lean_ctor_get(v___x_6193_, 8);
v_snapshotTasks_6203_ = lean_ctor_get(v___x_6193_, 9);
v_isSharedCheck_6222_ = !lean_is_exclusive(v___x_6193_);
if (v_isSharedCheck_6222_ == 0)
{
v___x_6205_ = v___x_6193_;
v_isShared_6206_ = v_isSharedCheck_6222_;
goto v_resetjp_6204_;
}
else
{
lean_inc(v_snapshotTasks_6203_);
lean_inc(v_infoState_6202_);
lean_inc(v_messages_6201_);
lean_inc(v_recordedDeps_6200_);
lean_inc(v_cache_6199_);
lean_inc(v_traceState_6194_);
lean_inc(v_auxDeclNGen_6198_);
lean_inc(v_ngen_6197_);
lean_inc(v_nextMacroScope_6196_);
lean_inc(v_env_6195_);
lean_dec(v___x_6193_);
v___x_6205_ = lean_box(0);
v_isShared_6206_ = v_isSharedCheck_6222_;
goto v_resetjp_6204_;
}
v_resetjp_6204_:
{
uint64_t v_tid_6207_; lean_object* v___x_6209_; uint8_t v_isShared_6210_; uint8_t v_isSharedCheck_6220_; 
v_tid_6207_ = lean_ctor_get_uint64(v_traceState_6194_, sizeof(void*)*1);
v_isSharedCheck_6220_ = !lean_is_exclusive(v_traceState_6194_);
if (v_isSharedCheck_6220_ == 0)
{
lean_object* v_unused_6221_; 
v_unused_6221_ = lean_ctor_get(v_traceState_6194_, 0);
lean_dec(v_unused_6221_);
v___x_6209_ = v_traceState_6194_;
v_isShared_6210_ = v_isSharedCheck_6220_;
goto v_resetjp_6208_;
}
else
{
lean_dec(v_traceState_6194_);
v___x_6209_ = lean_box(0);
v_isShared_6210_ = v_isSharedCheck_6220_;
goto v_resetjp_6208_;
}
v_resetjp_6208_:
{
lean_object* v___x_6211_; lean_object* v___x_6213_; 
v___x_6211_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6210_ == 0)
{
lean_ctor_set(v___x_6209_, 0, v___x_6211_);
v___x_6213_ = v___x_6209_;
goto v_reusejp_6212_;
}
else
{
lean_object* v_reuseFailAlloc_6219_; 
v_reuseFailAlloc_6219_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6219_, 0, v___x_6211_);
lean_ctor_set_uint64(v_reuseFailAlloc_6219_, sizeof(void*)*1, v_tid_6207_);
v___x_6213_ = v_reuseFailAlloc_6219_;
goto v_reusejp_6212_;
}
v_reusejp_6212_:
{
lean_object* v___x_6215_; 
if (v_isShared_6206_ == 0)
{
lean_ctor_set(v___x_6205_, 4, v___x_6213_);
v___x_6215_ = v___x_6205_;
goto v_reusejp_6214_;
}
else
{
lean_object* v_reuseFailAlloc_6218_; 
v_reuseFailAlloc_6218_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6218_, 0, v_env_6195_);
lean_ctor_set(v_reuseFailAlloc_6218_, 1, v_nextMacroScope_6196_);
lean_ctor_set(v_reuseFailAlloc_6218_, 2, v_ngen_6197_);
lean_ctor_set(v_reuseFailAlloc_6218_, 3, v_auxDeclNGen_6198_);
lean_ctor_set(v_reuseFailAlloc_6218_, 4, v___x_6213_);
lean_ctor_set(v_reuseFailAlloc_6218_, 5, v_cache_6199_);
lean_ctor_set(v_reuseFailAlloc_6218_, 6, v_recordedDeps_6200_);
lean_ctor_set(v_reuseFailAlloc_6218_, 7, v_messages_6201_);
lean_ctor_set(v_reuseFailAlloc_6218_, 8, v_infoState_6202_);
lean_ctor_set(v_reuseFailAlloc_6218_, 9, v_snapshotTasks_6203_);
v___x_6215_ = v_reuseFailAlloc_6218_;
goto v_reusejp_6214_;
}
v_reusejp_6214_:
{
lean_object* v___x_6216_; lean_object* v___x_6217_; 
v___x_6216_ = lean_st_ref_put(v___y_6188_, v___x_6215_);
v___x_6217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6217_, 0, v_traces_6192_);
return v___x_6217_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_6188_ = stack[0].m_obj;
lean_object* v_res_6223_;
v_res_6223_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6188_);
stack->m_obj
 = v_res_6223_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6224_, lean_object* v___y_6225_){
_start:
{
lean_object* v_res_6226_; 
v_res_6226_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6224_);
lean_dec(v___y_6224_);
return v_res_6226_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6237_);
return v___x_6239_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_6227_ = stack[0].m_obj;
lean_object* v___y_6228_ = stack[1].m_obj;
lean_object* v___y_6229_ = stack[2].m_obj;
lean_object* v___y_6230_ = stack[3].m_obj;
lean_object* v___y_6231_ = stack[4].m_obj;
lean_object* v___y_6232_ = stack[5].m_obj;
lean_object* v___y_6233_ = stack[6].m_obj;
lean_object* v___y_6234_ = stack[7].m_obj;
lean_object* v___y_6235_ = stack[8].m_obj;
lean_object* v___y_6236_ = stack[9].m_obj;
lean_object* v___y_6237_ = stack[10].m_obj;
lean_object* v_res_6240_;
v_res_6240_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
stack->m_obj
 = v_res_6240_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_){
_start:
{
lean_object* v_res_6253_; 
v_res_6253_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
lean_dec(v___y_6249_);
lean_dec_ref(v___y_6248_);
lean_dec(v___y_6247_);
lean_dec_ref(v___y_6246_);
lean_dec(v___y_6245_);
lean_dec_ref(v___y_6244_);
lean_dec(v___y_6243_);
lean_dec(v___y_6242_);
lean_dec_ref(v___y_6241_);
return v_res_6253_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6254_, lean_object* v_opt_6255_){
_start:
{
lean_object* v_name_6256_; lean_object* v_defValue_6257_; lean_object* v_map_6258_; lean_object* v___x_6259_; 
v_name_6256_ = lean_ctor_get(v_opt_6255_, 0);
v_defValue_6257_ = lean_ctor_get(v_opt_6255_, 1);
v_map_6258_ = lean_ctor_get(v_opts_6254_, 0);
v___x_6259_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6258_, v_name_6256_);
if (lean_obj_tag(v___x_6259_) == 0)
{
uint8_t v___x_6260_; 
v___x_6260_ = lean_unbox(v_defValue_6257_);
return v___x_6260_;
}
else
{
lean_object* v_val_6261_; 
v_val_6261_ = lean_ctor_get(v___x_6259_, 0);
lean_inc(v_val_6261_);
lean_dec_ref_known(v___x_6259_, 1);
if (lean_obj_tag(v_val_6261_) == 1)
{
uint8_t v_v_6262_; 
v_v_6262_ = lean_ctor_get_uint8(v_val_6261_, 0);
lean_dec_ref_known(v_val_6261_, 0);
return v_v_6262_;
}
else
{
uint8_t v___x_6263_; 
lean_dec(v_val_6261_);
v___x_6263_ = lean_unbox(v_defValue_6257_);
return v___x_6263_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_6254_ = stack[0].m_obj;
lean_object* v_opt_6255_ = stack[1].m_obj;
uint8_t v_res_6264_;
v_res_6264_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6254_, v_opt_6255_);
stack->m_num = v_res_6264_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6265_, lean_object* v_opt_6266_){
_start:
{
uint8_t v_res_6267_; lean_object* v_r_6268_; 
v_res_6267_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6265_, v_opt_6266_);
lean_dec_ref(v_opt_6266_);
lean_dec_ref(v_opts_6265_);
v_r_6268_ = lean_box(v_res_6267_);
return v_r_6268_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6269_, lean_object* v_msg_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_){
_start:
{
lean_object* v_ref_6276_; lean_object* v___x_6277_; lean_object* v_a_6278_; lean_object* v___x_6280_; uint8_t v_isShared_6281_; uint8_t v_isSharedCheck_6323_; 
v_ref_6276_ = lean_ctor_get(v___y_6273_, 2);
v___x_6277_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_);
v_a_6278_ = lean_ctor_get(v___x_6277_, 0);
v_isSharedCheck_6323_ = !lean_is_exclusive(v___x_6277_);
if (v_isSharedCheck_6323_ == 0)
{
v___x_6280_ = v___x_6277_;
v_isShared_6281_ = v_isSharedCheck_6323_;
goto v_resetjp_6279_;
}
else
{
lean_inc(v_a_6278_);
lean_dec(v___x_6277_);
v___x_6280_ = lean_box(0);
v_isShared_6281_ = v_isSharedCheck_6323_;
goto v_resetjp_6279_;
}
v_resetjp_6279_:
{
lean_object* v___x_6282_; lean_object* v_traceState_6283_; lean_object* v_env_6284_; lean_object* v_nextMacroScope_6285_; lean_object* v_ngen_6286_; lean_object* v_auxDeclNGen_6287_; lean_object* v_cache_6288_; lean_object* v_recordedDeps_6289_; lean_object* v_messages_6290_; lean_object* v_infoState_6291_; lean_object* v_snapshotTasks_6292_; lean_object* v___x_6294_; uint8_t v_isShared_6295_; uint8_t v_isSharedCheck_6322_; 
v___x_6282_ = lean_st_ref_take(v___y_6274_);
v_traceState_6283_ = lean_ctor_get(v___x_6282_, 4);
v_env_6284_ = lean_ctor_get(v___x_6282_, 0);
v_nextMacroScope_6285_ = lean_ctor_get(v___x_6282_, 1);
v_ngen_6286_ = lean_ctor_get(v___x_6282_, 2);
v_auxDeclNGen_6287_ = lean_ctor_get(v___x_6282_, 3);
v_cache_6288_ = lean_ctor_get(v___x_6282_, 5);
v_recordedDeps_6289_ = lean_ctor_get(v___x_6282_, 6);
v_messages_6290_ = lean_ctor_get(v___x_6282_, 7);
v_infoState_6291_ = lean_ctor_get(v___x_6282_, 8);
v_snapshotTasks_6292_ = lean_ctor_get(v___x_6282_, 9);
v_isSharedCheck_6322_ = !lean_is_exclusive(v___x_6282_);
if (v_isSharedCheck_6322_ == 0)
{
v___x_6294_ = v___x_6282_;
v_isShared_6295_ = v_isSharedCheck_6322_;
goto v_resetjp_6293_;
}
else
{
lean_inc(v_snapshotTasks_6292_);
lean_inc(v_infoState_6291_);
lean_inc(v_messages_6290_);
lean_inc(v_recordedDeps_6289_);
lean_inc(v_cache_6288_);
lean_inc(v_traceState_6283_);
lean_inc(v_auxDeclNGen_6287_);
lean_inc(v_ngen_6286_);
lean_inc(v_nextMacroScope_6285_);
lean_inc(v_env_6284_);
lean_dec(v___x_6282_);
v___x_6294_ = lean_box(0);
v_isShared_6295_ = v_isSharedCheck_6322_;
goto v_resetjp_6293_;
}
v_resetjp_6293_:
{
uint64_t v_tid_6296_; lean_object* v_traces_6297_; lean_object* v___x_6299_; uint8_t v_isShared_6300_; uint8_t v_isSharedCheck_6321_; 
v_tid_6296_ = lean_ctor_get_uint64(v_traceState_6283_, sizeof(void*)*1);
v_traces_6297_ = lean_ctor_get(v_traceState_6283_, 0);
v_isSharedCheck_6321_ = !lean_is_exclusive(v_traceState_6283_);
if (v_isSharedCheck_6321_ == 0)
{
v___x_6299_ = v_traceState_6283_;
v_isShared_6300_ = v_isSharedCheck_6321_;
goto v_resetjp_6298_;
}
else
{
lean_inc(v_traces_6297_);
lean_dec(v_traceState_6283_);
v___x_6299_ = lean_box(0);
v_isShared_6300_ = v_isSharedCheck_6321_;
goto v_resetjp_6298_;
}
v_resetjp_6298_:
{
lean_object* v___x_6301_; lean_object* v___x_6302_; double v___x_6303_; uint8_t v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6312_; 
v___x_6301_ = lean_box(0);
v___x_6302_ = lean_box(0);
v___x_6303_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6304_ = 0;
v___x_6305_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6306_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6306_, 0, v_cls_6269_);
lean_ctor_set(v___x_6306_, 1, v___x_6302_);
lean_ctor_set(v___x_6306_, 2, v___x_6305_);
lean_ctor_set_float(v___x_6306_, sizeof(void*)*3, v___x_6303_);
lean_ctor_set_float(v___x_6306_, sizeof(void*)*3 + 8, v___x_6303_);
lean_ctor_set_uint8(v___x_6306_, sizeof(void*)*3 + 16, v___x_6304_);
v___x_6307_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6308_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6308_, 0, v___x_6306_);
lean_ctor_set(v___x_6308_, 1, v_a_6278_);
lean_ctor_set(v___x_6308_, 2, v___x_6307_);
lean_inc(v_ref_6276_);
v___x_6309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6309_, 0, v_ref_6276_);
lean_ctor_set(v___x_6309_, 1, v___x_6308_);
v___x_6310_ = l_Lean_PersistentArray_push___redArg(v_traces_6297_, v___x_6309_);
if (v_isShared_6300_ == 0)
{
lean_ctor_set(v___x_6299_, 0, v___x_6310_);
v___x_6312_ = v___x_6299_;
goto v_reusejp_6311_;
}
else
{
lean_object* v_reuseFailAlloc_6320_; 
v_reuseFailAlloc_6320_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6320_, 0, v___x_6310_);
lean_ctor_set_uint64(v_reuseFailAlloc_6320_, sizeof(void*)*1, v_tid_6296_);
v___x_6312_ = v_reuseFailAlloc_6320_;
goto v_reusejp_6311_;
}
v_reusejp_6311_:
{
lean_object* v___x_6314_; 
if (v_isShared_6295_ == 0)
{
lean_ctor_set(v___x_6294_, 4, v___x_6312_);
v___x_6314_ = v___x_6294_;
goto v_reusejp_6313_;
}
else
{
lean_object* v_reuseFailAlloc_6319_; 
v_reuseFailAlloc_6319_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6319_, 0, v_env_6284_);
lean_ctor_set(v_reuseFailAlloc_6319_, 1, v_nextMacroScope_6285_);
lean_ctor_set(v_reuseFailAlloc_6319_, 2, v_ngen_6286_);
lean_ctor_set(v_reuseFailAlloc_6319_, 3, v_auxDeclNGen_6287_);
lean_ctor_set(v_reuseFailAlloc_6319_, 4, v___x_6312_);
lean_ctor_set(v_reuseFailAlloc_6319_, 5, v_cache_6288_);
lean_ctor_set(v_reuseFailAlloc_6319_, 6, v_recordedDeps_6289_);
lean_ctor_set(v_reuseFailAlloc_6319_, 7, v_messages_6290_);
lean_ctor_set(v_reuseFailAlloc_6319_, 8, v_infoState_6291_);
lean_ctor_set(v_reuseFailAlloc_6319_, 9, v_snapshotTasks_6292_);
v___x_6314_ = v_reuseFailAlloc_6319_;
goto v_reusejp_6313_;
}
v_reusejp_6313_:
{
lean_object* v___x_6315_; lean_object* v___x_6317_; 
v___x_6315_ = lean_st_ref_put(v___y_6274_, v___x_6314_);
if (v_isShared_6281_ == 0)
{
lean_ctor_set(v___x_6280_, 0, v___x_6301_);
v___x_6317_ = v___x_6280_;
goto v_reusejp_6316_;
}
else
{
lean_object* v_reuseFailAlloc_6318_; 
v_reuseFailAlloc_6318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6318_, 0, v___x_6301_);
v___x_6317_ = v_reuseFailAlloc_6318_;
goto v_reusejp_6316_;
}
v_reusejp_6316_:
{
return v___x_6317_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_6269_ = stack[0].m_obj;
lean_object* v_msg_6270_ = stack[1].m_obj;
lean_object* v___y_6271_ = stack[2].m_obj;
lean_object* v___y_6272_ = stack[3].m_obj;
lean_object* v___y_6273_ = stack[4].m_obj;
lean_object* v___y_6274_ = stack[5].m_obj;
lean_object* v_res_6324_;
v_res_6324_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6269_, v_msg_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_);
stack->m_obj
 = v_res_6324_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6325_, lean_object* v_msg_6326_, lean_object* v___y_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_){
_start:
{
lean_object* v_res_6332_; 
v_res_6332_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6325_, v_msg_6326_, v___y_6327_, v___y_6328_, v___y_6329_, v___y_6330_);
lean_dec(v___y_6330_);
lean_dec_ref(v___y_6329_);
lean_dec(v___y_6328_);
lean_dec_ref(v___y_6327_);
return v_res_6332_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6333_){
_start:
{
if (lean_obj_tag(v_e_6333_) == 0)
{
uint8_t v___x_6334_; 
v___x_6334_ = 2;
return v___x_6334_;
}
else
{
lean_object* v_a_6335_; uint8_t v___x_6336_; 
v_a_6335_ = lean_ctor_get(v_e_6333_, 0);
v___x_6336_ = lean_unbox(v_a_6335_);
if (v___x_6336_ == 0)
{
uint8_t v___x_6337_; 
v___x_6337_ = 1;
return v___x_6337_;
}
else
{
uint8_t v___x_6338_; 
v___x_6338_ = 0;
return v___x_6338_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_6333_ = stack[0].m_obj;
uint8_t v_res_6339_;
v_res_6339_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6333_);
stack->m_num = v_res_6339_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6340_){
_start:
{
uint8_t v_res_6341_; lean_object* v_r_6342_; 
v_res_6341_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6340_);
lean_dec_ref(v_e_6340_);
v_r_6342_ = lean_box(v_res_6341_);
return v_r_6342_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6343_){
_start:
{
if (lean_obj_tag(v_x_6343_) == 0)
{
lean_object* v_a_6345_; lean_object* v___x_6347_; uint8_t v_isShared_6348_; uint8_t v_isSharedCheck_6352_; 
v_a_6345_ = lean_ctor_get(v_x_6343_, 0);
v_isSharedCheck_6352_ = !lean_is_exclusive(v_x_6343_);
if (v_isSharedCheck_6352_ == 0)
{
v___x_6347_ = v_x_6343_;
v_isShared_6348_ = v_isSharedCheck_6352_;
goto v_resetjp_6346_;
}
else
{
lean_inc(v_a_6345_);
lean_dec(v_x_6343_);
v___x_6347_ = lean_box(0);
v_isShared_6348_ = v_isSharedCheck_6352_;
goto v_resetjp_6346_;
}
v_resetjp_6346_:
{
lean_object* v___x_6350_; 
if (v_isShared_6348_ == 0)
{
lean_ctor_set_tag(v___x_6347_, 1);
v___x_6350_ = v___x_6347_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6351_; 
v_reuseFailAlloc_6351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6351_, 0, v_a_6345_);
v___x_6350_ = v_reuseFailAlloc_6351_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
return v___x_6350_;
}
}
}
else
{
lean_object* v_a_6353_; lean_object* v___x_6355_; uint8_t v_isShared_6356_; uint8_t v_isSharedCheck_6360_; 
v_a_6353_ = lean_ctor_get(v_x_6343_, 0);
v_isSharedCheck_6360_ = !lean_is_exclusive(v_x_6343_);
if (v_isSharedCheck_6360_ == 0)
{
v___x_6355_ = v_x_6343_;
v_isShared_6356_ = v_isSharedCheck_6360_;
goto v_resetjp_6354_;
}
else
{
lean_inc(v_a_6353_);
lean_dec(v_x_6343_);
v___x_6355_ = lean_box(0);
v_isShared_6356_ = v_isSharedCheck_6360_;
goto v_resetjp_6354_;
}
v_resetjp_6354_:
{
lean_object* v___x_6358_; 
if (v_isShared_6356_ == 0)
{
lean_ctor_set_tag(v___x_6355_, 0);
v___x_6358_ = v___x_6355_;
goto v_reusejp_6357_;
}
else
{
lean_object* v_reuseFailAlloc_6359_; 
v_reuseFailAlloc_6359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6359_, 0, v_a_6353_);
v___x_6358_ = v_reuseFailAlloc_6359_;
goto v_reusejp_6357_;
}
v_reusejp_6357_:
{
return v___x_6358_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_6343_ = stack[0].m_obj;
lean_object* v_res_6361_;
v_res_6361_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6343_);
stack->m_obj
 = v_res_6361_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6362_, lean_object* v___y_6363_){
_start:
{
lean_object* v_res_6364_; 
v_res_6364_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6362_);
return v_res_6364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6365_, lean_object* v_opt_6366_){
_start:
{
lean_object* v_name_6367_; lean_object* v_defValue_6368_; lean_object* v_map_6369_; lean_object* v___x_6370_; 
v_name_6367_ = lean_ctor_get(v_opt_6366_, 0);
v_defValue_6368_ = lean_ctor_get(v_opt_6366_, 1);
v_map_6369_ = lean_ctor_get(v_opts_6365_, 0);
v___x_6370_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6369_, v_name_6367_);
if (lean_obj_tag(v___x_6370_) == 0)
{
lean_inc(v_defValue_6368_);
return v_defValue_6368_;
}
else
{
lean_object* v_val_6371_; 
v_val_6371_ = lean_ctor_get(v___x_6370_, 0);
lean_inc(v_val_6371_);
lean_dec_ref_known(v___x_6370_, 1);
if (lean_obj_tag(v_val_6371_) == 3)
{
lean_object* v_v_6372_; 
v_v_6372_ = lean_ctor_get(v_val_6371_, 0);
lean_inc(v_v_6372_);
lean_dec_ref_known(v_val_6371_, 1);
return v_v_6372_;
}
else
{
lean_dec(v_val_6371_);
lean_inc(v_defValue_6368_);
return v_defValue_6368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6373_, lean_object* v_opt_6374_){
_start:
{
lean_object* v_res_6375_; 
v_res_6375_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6373_, v_opt_6374_);
lean_dec_ref(v_opt_6374_);
lean_dec_ref(v_opts_6373_);
return v_res_6375_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6376_, size_t v_i_6377_, lean_object* v_bs_6378_){
_start:
{
uint8_t v___x_6379_; 
v___x_6379_ = lean_usize_dec_lt(v_i_6377_, v_sz_6376_);
if (v___x_6379_ == 0)
{
return v_bs_6378_;
}
else
{
lean_object* v_v_6380_; lean_object* v_msg_6381_; lean_object* v___x_6382_; lean_object* v_bs_x27_6383_; size_t v___x_6384_; size_t v___x_6385_; lean_object* v___x_6386_; 
v_v_6380_ = lean_array_uget_borrowed(v_bs_6378_, v_i_6377_);
v_msg_6381_ = lean_ctor_get(v_v_6380_, 1);
lean_inc_ref(v_msg_6381_);
v___x_6382_ = lean_unsigned_to_nat(0u);
v_bs_x27_6383_ = lean_array_uset(v_bs_6378_, v_i_6377_, v___x_6382_);
v___x_6384_ = ((size_t)1ULL);
v___x_6385_ = lean_usize_add(v_i_6377_, v___x_6384_);
v___x_6386_ = lean_array_uset(v_bs_x27_6383_, v_i_6377_, v_msg_6381_);
v_i_6377_ = v___x_6385_;
v_bs_6378_ = v___x_6386_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_6376_ = stack[0].m_num;
size_t v_i_6377_ = stack[1].m_num;
lean_object* v_bs_6378_ = stack[2].m_obj;
lean_object* v_res_6388_;
v_res_6388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6376_, v_i_6377_, v_bs_6378_);
stack->m_obj
 = v_res_6388_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6389_, lean_object* v_i_6390_, lean_object* v_bs_6391_){
_start:
{
size_t v_sz_boxed_6392_; size_t v_i_boxed_6393_; lean_object* v_res_6394_; 
v_sz_boxed_6392_ = lean_unbox_usize(v_sz_6389_);
lean_dec(v_sz_6389_);
v_i_boxed_6393_ = lean_unbox_usize(v_i_6390_);
lean_dec(v_i_6390_);
v_res_6394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6392_, v_i_boxed_6393_, v_bs_6391_);
return v_res_6394_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6395_, lean_object* v_data_6396_, lean_object* v_ref_6397_, lean_object* v_msg_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_, lean_object* v___y_6401_, lean_object* v___y_6402_){
_start:
{
lean_object* v_toCold_6404_; lean_object* v_currRecDepth_6405_; lean_object* v_ref_6406_; uint16_t v_optionFlags_6407_; uint8_t v_suppressElabErrors_6408_; uint8_t v_isRecordingDeps_6409_; lean_object* v_ref_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v_traceState_6413_; lean_object* v_traces_6414_; lean_object* v___x_6415_; size_t v_sz_6416_; size_t v___x_6417_; lean_object* v___x_6418_; lean_object* v_msg_6419_; lean_object* v___x_6420_; lean_object* v_a_6421_; lean_object* v___x_6423_; uint8_t v_isShared_6424_; uint8_t v_isSharedCheck_6459_; 
v_toCold_6404_ = lean_ctor_get(v___y_6401_, 0);
v_currRecDepth_6405_ = lean_ctor_get(v___y_6401_, 1);
v_ref_6406_ = lean_ctor_get(v___y_6401_, 2);
v_optionFlags_6407_ = lean_ctor_get_uint16(v___y_6401_, sizeof(void*)*3);
v_suppressElabErrors_6408_ = lean_ctor_get_uint8(v___y_6401_, sizeof(void*)*3 + 2);
v_isRecordingDeps_6409_ = lean_ctor_get_uint8(v___y_6401_, sizeof(void*)*3 + 3);
v_ref_6410_ = l_Lean_replaceRef(v_ref_6397_, v_ref_6406_);
lean_inc(v_currRecDepth_6405_);
lean_inc_ref(v_toCold_6404_);
v___x_6411_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_6411_, 0, v_toCold_6404_);
lean_ctor_set(v___x_6411_, 1, v_currRecDepth_6405_);
lean_ctor_set(v___x_6411_, 2, v_ref_6410_);
lean_ctor_set_uint16(v___x_6411_, sizeof(void*)*3, v_optionFlags_6407_);
lean_ctor_set_uint8(v___x_6411_, sizeof(void*)*3 + 2, v_suppressElabErrors_6408_);
lean_ctor_set_uint8(v___x_6411_, sizeof(void*)*3 + 3, v_isRecordingDeps_6409_);
v___x_6412_ = lean_st_ref_get(v___y_6402_);
v_traceState_6413_ = lean_ctor_get(v___x_6412_, 4);
lean_inc_ref(v_traceState_6413_);
lean_dec(v___x_6412_);
v_traces_6414_ = lean_ctor_get(v_traceState_6413_, 0);
lean_inc_ref(v_traces_6414_);
lean_dec_ref(v_traceState_6413_);
v___x_6415_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6414_);
lean_dec_ref(v_traces_6414_);
v_sz_6416_ = lean_array_size(v___x_6415_);
v___x_6417_ = ((size_t)0ULL);
v___x_6418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6416_, v___x_6417_, v___x_6415_);
v_msg_6419_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6419_, 0, v_data_6396_);
lean_ctor_set(v_msg_6419_, 1, v_msg_6398_);
lean_ctor_set(v_msg_6419_, 2, v___x_6418_);
v___x_6420_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6419_, v___y_6399_, v___y_6400_, v___x_6411_, v___y_6402_);
lean_dec_ref_known(v___x_6411_, 3);
v_a_6421_ = lean_ctor_get(v___x_6420_, 0);
v_isSharedCheck_6459_ = !lean_is_exclusive(v___x_6420_);
if (v_isSharedCheck_6459_ == 0)
{
v___x_6423_ = v___x_6420_;
v_isShared_6424_ = v_isSharedCheck_6459_;
goto v_resetjp_6422_;
}
else
{
lean_inc(v_a_6421_);
lean_dec(v___x_6420_);
v___x_6423_ = lean_box(0);
v_isShared_6424_ = v_isSharedCheck_6459_;
goto v_resetjp_6422_;
}
v_resetjp_6422_:
{
lean_object* v___x_6425_; lean_object* v_traceState_6426_; lean_object* v_env_6427_; lean_object* v_nextMacroScope_6428_; lean_object* v_ngen_6429_; lean_object* v_auxDeclNGen_6430_; lean_object* v_cache_6431_; lean_object* v_recordedDeps_6432_; lean_object* v_messages_6433_; lean_object* v_infoState_6434_; lean_object* v_snapshotTasks_6435_; lean_object* v___x_6437_; uint8_t v_isShared_6438_; uint8_t v_isSharedCheck_6458_; 
v___x_6425_ = lean_st_ref_take(v___y_6402_);
v_traceState_6426_ = lean_ctor_get(v___x_6425_, 4);
v_env_6427_ = lean_ctor_get(v___x_6425_, 0);
v_nextMacroScope_6428_ = lean_ctor_get(v___x_6425_, 1);
v_ngen_6429_ = lean_ctor_get(v___x_6425_, 2);
v_auxDeclNGen_6430_ = lean_ctor_get(v___x_6425_, 3);
v_cache_6431_ = lean_ctor_get(v___x_6425_, 5);
v_recordedDeps_6432_ = lean_ctor_get(v___x_6425_, 6);
v_messages_6433_ = lean_ctor_get(v___x_6425_, 7);
v_infoState_6434_ = lean_ctor_get(v___x_6425_, 8);
v_snapshotTasks_6435_ = lean_ctor_get(v___x_6425_, 9);
v_isSharedCheck_6458_ = !lean_is_exclusive(v___x_6425_);
if (v_isSharedCheck_6458_ == 0)
{
v___x_6437_ = v___x_6425_;
v_isShared_6438_ = v_isSharedCheck_6458_;
goto v_resetjp_6436_;
}
else
{
lean_inc(v_snapshotTasks_6435_);
lean_inc(v_infoState_6434_);
lean_inc(v_messages_6433_);
lean_inc(v_recordedDeps_6432_);
lean_inc(v_cache_6431_);
lean_inc(v_traceState_6426_);
lean_inc(v_auxDeclNGen_6430_);
lean_inc(v_ngen_6429_);
lean_inc(v_nextMacroScope_6428_);
lean_inc(v_env_6427_);
lean_dec(v___x_6425_);
v___x_6437_ = lean_box(0);
v_isShared_6438_ = v_isSharedCheck_6458_;
goto v_resetjp_6436_;
}
v_resetjp_6436_:
{
uint64_t v_tid_6439_; lean_object* v___x_6441_; uint8_t v_isShared_6442_; uint8_t v_isSharedCheck_6456_; 
v_tid_6439_ = lean_ctor_get_uint64(v_traceState_6426_, sizeof(void*)*1);
v_isSharedCheck_6456_ = !lean_is_exclusive(v_traceState_6426_);
if (v_isSharedCheck_6456_ == 0)
{
lean_object* v_unused_6457_; 
v_unused_6457_ = lean_ctor_get(v_traceState_6426_, 0);
lean_dec(v_unused_6457_);
v___x_6441_ = v_traceState_6426_;
v_isShared_6442_ = v_isSharedCheck_6456_;
goto v_resetjp_6440_;
}
else
{
lean_dec(v_traceState_6426_);
v___x_6441_ = lean_box(0);
v_isShared_6442_ = v_isSharedCheck_6456_;
goto v_resetjp_6440_;
}
v_resetjp_6440_:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v___x_6445_; lean_object* v___x_6447_; 
v___x_6443_ = lean_box(0);
v___x_6444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6444_, 0, v_ref_6397_);
lean_ctor_set(v___x_6444_, 1, v_a_6421_);
v___x_6445_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6395_, v___x_6444_);
if (v_isShared_6442_ == 0)
{
lean_ctor_set(v___x_6441_, 0, v___x_6445_);
v___x_6447_ = v___x_6441_;
goto v_reusejp_6446_;
}
else
{
lean_object* v_reuseFailAlloc_6455_; 
v_reuseFailAlloc_6455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6455_, 0, v___x_6445_);
lean_ctor_set_uint64(v_reuseFailAlloc_6455_, sizeof(void*)*1, v_tid_6439_);
v___x_6447_ = v_reuseFailAlloc_6455_;
goto v_reusejp_6446_;
}
v_reusejp_6446_:
{
lean_object* v___x_6449_; 
if (v_isShared_6438_ == 0)
{
lean_ctor_set(v___x_6437_, 4, v___x_6447_);
v___x_6449_ = v___x_6437_;
goto v_reusejp_6448_;
}
else
{
lean_object* v_reuseFailAlloc_6454_; 
v_reuseFailAlloc_6454_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6454_, 0, v_env_6427_);
lean_ctor_set(v_reuseFailAlloc_6454_, 1, v_nextMacroScope_6428_);
lean_ctor_set(v_reuseFailAlloc_6454_, 2, v_ngen_6429_);
lean_ctor_set(v_reuseFailAlloc_6454_, 3, v_auxDeclNGen_6430_);
lean_ctor_set(v_reuseFailAlloc_6454_, 4, v___x_6447_);
lean_ctor_set(v_reuseFailAlloc_6454_, 5, v_cache_6431_);
lean_ctor_set(v_reuseFailAlloc_6454_, 6, v_recordedDeps_6432_);
lean_ctor_set(v_reuseFailAlloc_6454_, 7, v_messages_6433_);
lean_ctor_set(v_reuseFailAlloc_6454_, 8, v_infoState_6434_);
lean_ctor_set(v_reuseFailAlloc_6454_, 9, v_snapshotTasks_6435_);
v___x_6449_ = v_reuseFailAlloc_6454_;
goto v_reusejp_6448_;
}
v_reusejp_6448_:
{
lean_object* v___x_6450_; lean_object* v___x_6452_; 
v___x_6450_ = lean_st_ref_put(v___y_6402_, v___x_6449_);
if (v_isShared_6424_ == 0)
{
lean_ctor_set(v___x_6423_, 0, v___x_6443_);
v___x_6452_ = v___x_6423_;
goto v_reusejp_6451_;
}
else
{
lean_object* v_reuseFailAlloc_6453_; 
v_reuseFailAlloc_6453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6453_, 0, v___x_6443_);
v___x_6452_ = v_reuseFailAlloc_6453_;
goto v_reusejp_6451_;
}
v_reusejp_6451_:
{
return v___x_6452_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_6395_ = stack[0].m_obj;
lean_object* v_data_6396_ = stack[1].m_obj;
lean_object* v_ref_6397_ = stack[2].m_obj;
lean_object* v_msg_6398_ = stack[3].m_obj;
lean_object* v___y_6399_ = stack[4].m_obj;
lean_object* v___y_6400_ = stack[5].m_obj;
lean_object* v___y_6401_ = stack[6].m_obj;
lean_object* v___y_6402_ = stack[7].m_obj;
lean_object* v_res_6460_;
v_res_6460_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6395_, v_data_6396_, v_ref_6397_, v_msg_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_);
stack->m_obj
 = v_res_6460_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6461_, lean_object* v_data_6462_, lean_object* v_ref_6463_, lean_object* v_msg_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_){
_start:
{
lean_object* v_res_6470_; 
v_res_6470_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6461_, v_data_6462_, v_ref_6463_, v_msg_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_);
lean_dec(v___y_6468_);
lean_dec_ref(v___y_6467_);
lean_dec(v___y_6466_);
lean_dec_ref(v___y_6465_);
return v_res_6470_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6472_; lean_object* v___x_6473_; 
v___x_6472_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6473_ = l_Lean_stringToMessageData(v___x_6472_);
return v___x_6473_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6474_; double v___x_6475_; 
v___x_6474_ = lean_unsigned_to_nat(1000u);
v___x_6475_ = lean_float_of_nat(v___x_6474_);
return v___x_6475_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6476_, uint8_t v_collapsed_6477_, lean_object* v_tag_6478_, lean_object* v_opts_6479_, uint8_t v_clsEnabled_6480_, lean_object* v_oldTraces_6481_, lean_object* v_msg_6482_, lean_object* v_resStartStop_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_){
_start:
{
lean_object* v_fst_6496_; lean_object* v_snd_6497_; lean_object* v___y_6499_; lean_object* v___y_6500_; lean_object* v_data_6501_; lean_object* v_fst_6512_; lean_object* v_snd_6513_; lean_object* v___x_6514_; uint8_t v___x_6515_; lean_object* v___y_6517_; lean_object* v_a_6518_; uint8_t v___y_6533_; double v___y_6565_; 
v_fst_6496_ = lean_ctor_get(v_resStartStop_6483_, 0);
lean_inc(v_fst_6496_);
v_snd_6497_ = lean_ctor_get(v_resStartStop_6483_, 1);
lean_inc(v_snd_6497_);
lean_dec_ref(v_resStartStop_6483_);
v_fst_6512_ = lean_ctor_get(v_snd_6497_, 0);
lean_inc(v_fst_6512_);
v_snd_6513_ = lean_ctor_get(v_snd_6497_, 1);
lean_inc(v_snd_6513_);
lean_dec(v_snd_6497_);
v___x_6514_ = l_Lean_trace_profiler;
v___x_6515_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6479_, v___x_6514_);
if (v___x_6515_ == 0)
{
v___y_6533_ = v___x_6515_;
goto v___jp_6532_;
}
else
{
lean_object* v___x_6570_; uint8_t v___x_6571_; 
v___x_6570_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6571_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6479_, v___x_6570_);
if (v___x_6571_ == 0)
{
lean_object* v___x_6572_; lean_object* v___x_6573_; double v___x_6574_; double v___x_6575_; double v___x_6576_; 
v___x_6572_ = l_Lean_trace_profiler_threshold;
v___x_6573_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6479_, v___x_6572_);
v___x_6574_ = lean_float_of_nat(v___x_6573_);
v___x_6575_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6576_ = lean_float_div(v___x_6574_, v___x_6575_);
v___y_6565_ = v___x_6576_;
goto v___jp_6564_;
}
else
{
lean_object* v___x_6577_; lean_object* v___x_6578_; double v___x_6579_; 
v___x_6577_ = l_Lean_trace_profiler_threshold;
v___x_6578_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6479_, v___x_6577_);
v___x_6579_ = lean_float_of_nat(v___x_6578_);
v___y_6565_ = v___x_6579_;
goto v___jp_6564_;
}
}
v___jp_6498_:
{
lean_object* v___x_6502_; 
lean_inc(v___y_6500_);
v___x_6502_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6481_, v_data_6501_, v___y_6500_, v___y_6499_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_);
if (lean_obj_tag(v___x_6502_) == 0)
{
lean_object* v___x_6503_; 
lean_dec_ref_known(v___x_6502_, 1);
v___x_6503_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6496_);
return v___x_6503_;
}
else
{
lean_object* v_a_6504_; lean_object* v___x_6506_; uint8_t v_isShared_6507_; uint8_t v_isSharedCheck_6511_; 
lean_dec(v_fst_6496_);
v_a_6504_ = lean_ctor_get(v___x_6502_, 0);
v_isSharedCheck_6511_ = !lean_is_exclusive(v___x_6502_);
if (v_isSharedCheck_6511_ == 0)
{
v___x_6506_ = v___x_6502_;
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
else
{
lean_inc(v_a_6504_);
lean_dec(v___x_6502_);
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
v___jp_6516_:
{
uint8_t v_result_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; double v___x_6522_; lean_object* v_data_6523_; 
v_result_6519_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6496_);
v___x_6520_ = lean_box(v_result_6519_);
v___x_6521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6521_, 0, v___x_6520_);
v___x_6522_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6478_);
lean_inc_ref(v___x_6521_);
lean_inc(v_cls_6476_);
v_data_6523_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6523_, 0, v_cls_6476_);
lean_ctor_set(v_data_6523_, 1, v___x_6521_);
lean_ctor_set(v_data_6523_, 2, v_tag_6478_);
lean_ctor_set_float(v_data_6523_, sizeof(void*)*3, v___x_6522_);
lean_ctor_set_float(v_data_6523_, sizeof(void*)*3 + 8, v___x_6522_);
lean_ctor_set_uint8(v_data_6523_, sizeof(void*)*3 + 16, v_collapsed_6477_);
if (v___x_6515_ == 0)
{
lean_dec_ref_known(v___x_6521_, 1);
lean_dec(v_snd_6513_);
lean_dec(v_fst_6512_);
lean_dec_ref(v_tag_6478_);
lean_dec(v_cls_6476_);
v___y_6499_ = v_a_6518_;
v___y_6500_ = v___y_6517_;
v_data_6501_ = v_data_6523_;
goto v___jp_6498_;
}
else
{
lean_object* v_data_6524_; double v___x_6525_; double v___x_6526_; 
lean_dec_ref_known(v_data_6523_, 3);
v_data_6524_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6524_, 0, v_cls_6476_);
lean_ctor_set(v_data_6524_, 1, v___x_6521_);
lean_ctor_set(v_data_6524_, 2, v_tag_6478_);
v___x_6525_ = lean_unbox_float(v_fst_6512_);
lean_dec(v_fst_6512_);
lean_ctor_set_float(v_data_6524_, sizeof(void*)*3, v___x_6525_);
v___x_6526_ = lean_unbox_float(v_snd_6513_);
lean_dec(v_snd_6513_);
lean_ctor_set_float(v_data_6524_, sizeof(void*)*3 + 8, v___x_6526_);
lean_ctor_set_uint8(v_data_6524_, sizeof(void*)*3 + 16, v_collapsed_6477_);
v___y_6499_ = v_a_6518_;
v___y_6500_ = v___y_6517_;
v_data_6501_ = v_data_6524_;
goto v___jp_6498_;
}
}
v___jp_6527_:
{
lean_object* v_ref_6528_; lean_object* v___x_6529_; 
v_ref_6528_ = lean_ctor_get(v___y_6493_, 2);
lean_inc(v___y_6494_);
lean_inc_ref(v___y_6493_);
lean_inc(v___y_6492_);
lean_inc_ref(v___y_6491_);
lean_inc(v___y_6490_);
lean_inc_ref(v___y_6489_);
lean_inc(v___y_6488_);
lean_inc_ref(v___y_6487_);
lean_inc(v___y_6486_);
lean_inc(v___y_6485_);
lean_inc_ref(v___y_6484_);
lean_inc(v_fst_6496_);
v___x_6529_ = lean_apply_13(v_msg_6482_, v_fst_6496_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, lean_box(0));
if (lean_obj_tag(v___x_6529_) == 0)
{
lean_object* v_a_6530_; 
v_a_6530_ = lean_ctor_get(v___x_6529_, 0);
lean_inc(v_a_6530_);
lean_dec_ref_known(v___x_6529_, 1);
v___y_6517_ = v_ref_6528_;
v_a_6518_ = v_a_6530_;
goto v___jp_6516_;
}
else
{
lean_object* v___x_6531_; 
lean_dec_ref_known(v___x_6529_, 1);
v___x_6531_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6517_ = v_ref_6528_;
v_a_6518_ = v___x_6531_;
goto v___jp_6516_;
}
}
v___jp_6532_:
{
if (v_clsEnabled_6480_ == 0)
{
if (v___y_6533_ == 0)
{
lean_object* v___x_6534_; lean_object* v_traceState_6535_; lean_object* v_env_6536_; lean_object* v_nextMacroScope_6537_; lean_object* v_ngen_6538_; lean_object* v_auxDeclNGen_6539_; lean_object* v_cache_6540_; lean_object* v_recordedDeps_6541_; lean_object* v_messages_6542_; lean_object* v_infoState_6543_; lean_object* v_snapshotTasks_6544_; lean_object* v___x_6546_; uint8_t v_isShared_6547_; uint8_t v_isSharedCheck_6563_; 
lean_dec(v_snd_6513_);
lean_dec(v_fst_6512_);
lean_dec_ref(v_msg_6482_);
lean_dec_ref(v_tag_6478_);
lean_dec(v_cls_6476_);
v___x_6534_ = lean_st_ref_take(v___y_6494_);
v_traceState_6535_ = lean_ctor_get(v___x_6534_, 4);
v_env_6536_ = lean_ctor_get(v___x_6534_, 0);
v_nextMacroScope_6537_ = lean_ctor_get(v___x_6534_, 1);
v_ngen_6538_ = lean_ctor_get(v___x_6534_, 2);
v_auxDeclNGen_6539_ = lean_ctor_get(v___x_6534_, 3);
v_cache_6540_ = lean_ctor_get(v___x_6534_, 5);
v_recordedDeps_6541_ = lean_ctor_get(v___x_6534_, 6);
v_messages_6542_ = lean_ctor_get(v___x_6534_, 7);
v_infoState_6543_ = lean_ctor_get(v___x_6534_, 8);
v_snapshotTasks_6544_ = lean_ctor_get(v___x_6534_, 9);
v_isSharedCheck_6563_ = !lean_is_exclusive(v___x_6534_);
if (v_isSharedCheck_6563_ == 0)
{
v___x_6546_ = v___x_6534_;
v_isShared_6547_ = v_isSharedCheck_6563_;
goto v_resetjp_6545_;
}
else
{
lean_inc(v_snapshotTasks_6544_);
lean_inc(v_infoState_6543_);
lean_inc(v_messages_6542_);
lean_inc(v_recordedDeps_6541_);
lean_inc(v_cache_6540_);
lean_inc(v_traceState_6535_);
lean_inc(v_auxDeclNGen_6539_);
lean_inc(v_ngen_6538_);
lean_inc(v_nextMacroScope_6537_);
lean_inc(v_env_6536_);
lean_dec(v___x_6534_);
v___x_6546_ = lean_box(0);
v_isShared_6547_ = v_isSharedCheck_6563_;
goto v_resetjp_6545_;
}
v_resetjp_6545_:
{
uint64_t v_tid_6548_; lean_object* v_traces_6549_; lean_object* v___x_6551_; uint8_t v_isShared_6552_; uint8_t v_isSharedCheck_6562_; 
v_tid_6548_ = lean_ctor_get_uint64(v_traceState_6535_, sizeof(void*)*1);
v_traces_6549_ = lean_ctor_get(v_traceState_6535_, 0);
v_isSharedCheck_6562_ = !lean_is_exclusive(v_traceState_6535_);
if (v_isSharedCheck_6562_ == 0)
{
v___x_6551_ = v_traceState_6535_;
v_isShared_6552_ = v_isSharedCheck_6562_;
goto v_resetjp_6550_;
}
else
{
lean_inc(v_traces_6549_);
lean_dec(v_traceState_6535_);
v___x_6551_ = lean_box(0);
v_isShared_6552_ = v_isSharedCheck_6562_;
goto v_resetjp_6550_;
}
v_resetjp_6550_:
{
lean_object* v___x_6553_; lean_object* v___x_6555_; 
v___x_6553_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6481_, v_traces_6549_);
lean_dec_ref(v_traces_6549_);
if (v_isShared_6552_ == 0)
{
lean_ctor_set(v___x_6551_, 0, v___x_6553_);
v___x_6555_ = v___x_6551_;
goto v_reusejp_6554_;
}
else
{
lean_object* v_reuseFailAlloc_6561_; 
v_reuseFailAlloc_6561_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6561_, 0, v___x_6553_);
lean_ctor_set_uint64(v_reuseFailAlloc_6561_, sizeof(void*)*1, v_tid_6548_);
v___x_6555_ = v_reuseFailAlloc_6561_;
goto v_reusejp_6554_;
}
v_reusejp_6554_:
{
lean_object* v___x_6557_; 
if (v_isShared_6547_ == 0)
{
lean_ctor_set(v___x_6546_, 4, v___x_6555_);
v___x_6557_ = v___x_6546_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6560_; 
v_reuseFailAlloc_6560_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6560_, 0, v_env_6536_);
lean_ctor_set(v_reuseFailAlloc_6560_, 1, v_nextMacroScope_6537_);
lean_ctor_set(v_reuseFailAlloc_6560_, 2, v_ngen_6538_);
lean_ctor_set(v_reuseFailAlloc_6560_, 3, v_auxDeclNGen_6539_);
lean_ctor_set(v_reuseFailAlloc_6560_, 4, v___x_6555_);
lean_ctor_set(v_reuseFailAlloc_6560_, 5, v_cache_6540_);
lean_ctor_set(v_reuseFailAlloc_6560_, 6, v_recordedDeps_6541_);
lean_ctor_set(v_reuseFailAlloc_6560_, 7, v_messages_6542_);
lean_ctor_set(v_reuseFailAlloc_6560_, 8, v_infoState_6543_);
lean_ctor_set(v_reuseFailAlloc_6560_, 9, v_snapshotTasks_6544_);
v___x_6557_ = v_reuseFailAlloc_6560_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
lean_object* v___x_6558_; lean_object* v___x_6559_; 
v___x_6558_ = lean_st_ref_put(v___y_6494_, v___x_6557_);
v___x_6559_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6496_);
return v___x_6559_;
}
}
}
}
}
else
{
goto v___jp_6527_;
}
}
else
{
goto v___jp_6527_;
}
}
v___jp_6564_:
{
double v___x_6566_; double v___x_6567_; double v___x_6568_; uint8_t v___x_6569_; 
v___x_6566_ = lean_unbox_float(v_snd_6513_);
v___x_6567_ = lean_unbox_float(v_fst_6512_);
v___x_6568_ = lean_float_sub(v___x_6566_, v___x_6567_);
v___x_6569_ = lean_float_decLt(v___y_6565_, v___x_6568_);
v___y_6533_ = v___x_6569_;
goto v___jp_6532_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_6476_ = stack[0].m_obj;
uint8_t v_collapsed_6477_ = stack[1].m_num;
lean_object* v_tag_6478_ = stack[2].m_obj;
lean_object* v_opts_6479_ = stack[3].m_obj;
uint8_t v_clsEnabled_6480_ = stack[4].m_num;
lean_object* v_oldTraces_6481_ = stack[5].m_obj;
lean_object* v_msg_6482_ = stack[6].m_obj;
lean_object* v_resStartStop_6483_ = stack[7].m_obj;
lean_object* v___y_6484_ = stack[8].m_obj;
lean_object* v___y_6485_ = stack[9].m_obj;
lean_object* v___y_6486_ = stack[10].m_obj;
lean_object* v___y_6487_ = stack[11].m_obj;
lean_object* v___y_6488_ = stack[12].m_obj;
lean_object* v___y_6489_ = stack[13].m_obj;
lean_object* v___y_6490_ = stack[14].m_obj;
lean_object* v___y_6491_ = stack[15].m_obj;
lean_object* v___y_6492_ = stack[16].m_obj;
lean_object* v___y_6493_ = stack[17].m_obj;
lean_object* v___y_6494_ = stack[18].m_obj;
lean_object* v_res_6580_;
v_res_6580_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6476_, v_collapsed_6477_, v_tag_6478_, v_opts_6479_, v_clsEnabled_6480_, v_oldTraces_6481_, v_msg_6482_, v_resStartStop_6483_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_);
stack->m_obj
 = v_res_6580_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6581_ = _args[0];
lean_object* v_collapsed_6582_ = _args[1];
lean_object* v_tag_6583_ = _args[2];
lean_object* v_opts_6584_ = _args[3];
lean_object* v_clsEnabled_6585_ = _args[4];
lean_object* v_oldTraces_6586_ = _args[5];
lean_object* v_msg_6587_ = _args[6];
lean_object* v_resStartStop_6588_ = _args[7];
lean_object* v___y_6589_ = _args[8];
lean_object* v___y_6590_ = _args[9];
lean_object* v___y_6591_ = _args[10];
lean_object* v___y_6592_ = _args[11];
lean_object* v___y_6593_ = _args[12];
lean_object* v___y_6594_ = _args[13];
lean_object* v___y_6595_ = _args[14];
lean_object* v___y_6596_ = _args[15];
lean_object* v___y_6597_ = _args[16];
lean_object* v___y_6598_ = _args[17];
lean_object* v___y_6599_ = _args[18];
lean_object* v___y_6600_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6601_; uint8_t v_clsEnabled_boxed_6602_; lean_object* v_res_6603_; 
v_collapsed_boxed_6601_ = lean_unbox(v_collapsed_6582_);
v_clsEnabled_boxed_6602_ = lean_unbox(v_clsEnabled_6585_);
v_res_6603_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6581_, v_collapsed_boxed_6601_, v_tag_6583_, v_opts_6584_, v_clsEnabled_boxed_6602_, v_oldTraces_6586_, v_msg_6587_, v_resStartStop_6588_, v___y_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_, v___y_6599_);
lean_dec(v___y_6599_);
lean_dec_ref(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec_ref(v___y_6596_);
lean_dec(v___y_6595_);
lean_dec_ref(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec_ref(v___y_6592_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec_ref(v___y_6589_);
lean_dec_ref(v_opts_6584_);
return v_res_6603_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6608_; lean_object* v___x_6609_; 
v___x_6608_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6609_ = l_Lean_stringToMessageData(v___x_6608_);
return v___x_6609_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6610_, lean_object* v_b_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_, lean_object* v___y_6614_, lean_object* v___y_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_, lean_object* v___y_6618_, lean_object* v___y_6619_, lean_object* v___y_6620_, lean_object* v___y_6621_, lean_object* v___y_6622_){
_start:
{
if (lean_obj_tag(v_as_x27_6610_) == 0)
{
lean_object* v___x_6624_; 
v___x_6624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6624_, 0, v_b_6611_);
return v___x_6624_;
}
else
{
lean_object* v_head_6625_; lean_object* v_toCold_6626_; lean_object* v_options_6627_; lean_object* v_tail_6628_; lean_object* v_name_6629_; lean_object* v_run_x27_6630_; lean_object* v_inheritedTraceOptions_6631_; uint8_t v_hasTrace_6632_; lean_object* v___x_6633_; uint8_t v___y_6635_; lean_object* v___x_6640_; lean_object* v___y_6642_; 
lean_dec_ref(v_b_6611_);
v_head_6625_ = lean_ctor_get(v_as_x27_6610_, 0);
v_toCold_6626_ = lean_ctor_get(v___y_6621_, 0);
v_options_6627_ = lean_ctor_get(v_toCold_6626_, 2);
v_tail_6628_ = lean_ctor_get(v_as_x27_6610_, 1);
v_name_6629_ = lean_ctor_get(v_head_6625_, 0);
v_run_x27_6630_ = lean_ctor_get(v_head_6625_, 1);
v_inheritedTraceOptions_6631_ = lean_ctor_get(v_toCold_6626_, 11);
v_hasTrace_6632_ = lean_ctor_get_uint8(v_options_6627_, sizeof(void*)*1);
v___x_6633_ = lean_box(0);
v___x_6640_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6632_ == 0)
{
lean_object* v___x_6670_; 
lean_inc_ref(v_run_x27_6630_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
lean_inc(v___y_6620_);
lean_inc_ref(v___y_6619_);
lean_inc(v___y_6618_);
lean_inc_ref(v___y_6617_);
lean_inc(v___y_6616_);
lean_inc_ref(v___y_6615_);
lean_inc(v___y_6614_);
lean_inc(v___y_6613_);
lean_inc_ref(v___y_6612_);
v___x_6670_ = lean_apply_12(v_run_x27_6630_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, lean_box(0));
v___y_6642_ = v___x_6670_;
goto v___jp_6641_;
}
else
{
lean_object* v___f_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; uint8_t v___x_6675_; lean_object* v___y_6677_; lean_object* v___y_6678_; lean_object* v_a_6679_; lean_object* v___y_6692_; lean_object* v___y_6693_; lean_object* v_a_6694_; 
lean_inc(v_name_6629_);
v___f_6671_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6671_, 0, v_name_6629_);
v___x_6672_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6673_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6674_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6631_, v_options_6627_, v___x_6674_);
if (v___x_6675_ == 0)
{
lean_object* v___x_6744_; uint8_t v___x_6745_; 
v___x_6744_ = l_Lean_trace_profiler;
v___x_6745_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6627_, v___x_6744_);
if (v___x_6745_ == 0)
{
lean_object* v___x_6746_; 
lean_dec_ref(v___f_6671_);
lean_inc_ref(v_run_x27_6630_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
lean_inc(v___y_6620_);
lean_inc_ref(v___y_6619_);
lean_inc(v___y_6618_);
lean_inc_ref(v___y_6617_);
lean_inc(v___y_6616_);
lean_inc_ref(v___y_6615_);
lean_inc(v___y_6614_);
lean_inc(v___y_6613_);
lean_inc_ref(v___y_6612_);
v___x_6746_ = lean_apply_12(v_run_x27_6630_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, lean_box(0));
v___y_6642_ = v___x_6746_;
goto v___jp_6641_;
}
else
{
goto v___jp_6703_;
}
}
else
{
goto v___jp_6703_;
}
v___jp_6676_:
{
lean_object* v___x_6680_; double v___x_6681_; double v___x_6682_; double v___x_6683_; double v___x_6684_; double v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v___x_6680_ = lean_io_mono_nanos_now();
v___x_6681_ = lean_float_of_nat(v___y_6677_);
v___x_6682_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6683_ = lean_float_div(v___x_6681_, v___x_6682_);
v___x_6684_ = lean_float_of_nat(v___x_6680_);
v___x_6685_ = lean_float_div(v___x_6684_, v___x_6682_);
v___x_6686_ = lean_box_float(v___x_6683_);
v___x_6687_ = lean_box_float(v___x_6685_);
v___x_6688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6688_, 0, v___x_6686_);
lean_ctor_set(v___x_6688_, 1, v___x_6687_);
v___x_6689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6689_, 0, v_a_6679_);
lean_ctor_set(v___x_6689_, 1, v___x_6688_);
v___x_6690_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6672_, v_hasTrace_6632_, v___x_6673_, v_options_6627_, v___x_6675_, v___y_6678_, v___f_6671_, v___x_6689_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_);
v___y_6642_ = v___x_6690_;
goto v___jp_6641_;
}
v___jp_6691_:
{
lean_object* v___x_6695_; double v___x_6696_; double v___x_6697_; lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; lean_object* v___x_6701_; lean_object* v___x_6702_; 
v___x_6695_ = lean_io_get_num_heartbeats();
v___x_6696_ = lean_float_of_nat(v___y_6692_);
v___x_6697_ = lean_float_of_nat(v___x_6695_);
v___x_6698_ = lean_box_float(v___x_6696_);
v___x_6699_ = lean_box_float(v___x_6697_);
v___x_6700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6700_, 0, v___x_6698_);
lean_ctor_set(v___x_6700_, 1, v___x_6699_);
v___x_6701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6701_, 0, v_a_6694_);
lean_ctor_set(v___x_6701_, 1, v___x_6700_);
v___x_6702_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6672_, v_hasTrace_6632_, v___x_6673_, v_options_6627_, v___x_6675_, v___y_6693_, v___f_6671_, v___x_6701_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_);
v___y_6642_ = v___x_6702_;
goto v___jp_6641_;
}
v___jp_6703_:
{
lean_object* v___x_6704_; lean_object* v_a_6705_; lean_object* v___x_6706_; uint8_t v___x_6707_; 
v___x_6704_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6622_);
v_a_6705_ = lean_ctor_get(v___x_6704_, 0);
lean_inc(v_a_6705_);
lean_dec_ref(v___x_6704_);
v___x_6706_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6707_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6627_, v___x_6706_);
if (v___x_6707_ == 0)
{
lean_object* v___x_6708_; lean_object* v___x_6709_; 
v___x_6708_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_6630_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
lean_inc(v___y_6620_);
lean_inc_ref(v___y_6619_);
lean_inc(v___y_6618_);
lean_inc_ref(v___y_6617_);
lean_inc(v___y_6616_);
lean_inc_ref(v___y_6615_);
lean_inc(v___y_6614_);
lean_inc(v___y_6613_);
lean_inc_ref(v___y_6612_);
v___x_6709_ = lean_apply_12(v_run_x27_6630_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, lean_box(0));
if (lean_obj_tag(v___x_6709_) == 0)
{
lean_object* v_a_6710_; lean_object* v___x_6712_; uint8_t v_isShared_6713_; uint8_t v_isSharedCheck_6717_; 
v_a_6710_ = lean_ctor_get(v___x_6709_, 0);
v_isSharedCheck_6717_ = !lean_is_exclusive(v___x_6709_);
if (v_isSharedCheck_6717_ == 0)
{
v___x_6712_ = v___x_6709_;
v_isShared_6713_ = v_isSharedCheck_6717_;
goto v_resetjp_6711_;
}
else
{
lean_inc(v_a_6710_);
lean_dec(v___x_6709_);
v___x_6712_ = lean_box(0);
v_isShared_6713_ = v_isSharedCheck_6717_;
goto v_resetjp_6711_;
}
v_resetjp_6711_:
{
lean_object* v___x_6715_; 
if (v_isShared_6713_ == 0)
{
lean_ctor_set_tag(v___x_6712_, 1);
v___x_6715_ = v___x_6712_;
goto v_reusejp_6714_;
}
else
{
lean_object* v_reuseFailAlloc_6716_; 
v_reuseFailAlloc_6716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6716_, 0, v_a_6710_);
v___x_6715_ = v_reuseFailAlloc_6716_;
goto v_reusejp_6714_;
}
v_reusejp_6714_:
{
v___y_6677_ = v___x_6708_;
v___y_6678_ = v_a_6705_;
v_a_6679_ = v___x_6715_;
goto v___jp_6676_;
}
}
}
else
{
lean_object* v_a_6718_; lean_object* v___x_6720_; uint8_t v_isShared_6721_; uint8_t v_isSharedCheck_6725_; 
v_a_6718_ = lean_ctor_get(v___x_6709_, 0);
v_isSharedCheck_6725_ = !lean_is_exclusive(v___x_6709_);
if (v_isSharedCheck_6725_ == 0)
{
v___x_6720_ = v___x_6709_;
v_isShared_6721_ = v_isSharedCheck_6725_;
goto v_resetjp_6719_;
}
else
{
lean_inc(v_a_6718_);
lean_dec(v___x_6709_);
v___x_6720_ = lean_box(0);
v_isShared_6721_ = v_isSharedCheck_6725_;
goto v_resetjp_6719_;
}
v_resetjp_6719_:
{
lean_object* v___x_6723_; 
if (v_isShared_6721_ == 0)
{
lean_ctor_set_tag(v___x_6720_, 0);
v___x_6723_ = v___x_6720_;
goto v_reusejp_6722_;
}
else
{
lean_object* v_reuseFailAlloc_6724_; 
v_reuseFailAlloc_6724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_a_6718_);
v___x_6723_ = v_reuseFailAlloc_6724_;
goto v_reusejp_6722_;
}
v_reusejp_6722_:
{
v___y_6677_ = v___x_6708_;
v___y_6678_ = v_a_6705_;
v_a_6679_ = v___x_6723_;
goto v___jp_6676_;
}
}
}
}
else
{
lean_object* v___x_6726_; lean_object* v___x_6727_; 
v___x_6726_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_6630_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
lean_inc(v___y_6620_);
lean_inc_ref(v___y_6619_);
lean_inc(v___y_6618_);
lean_inc_ref(v___y_6617_);
lean_inc(v___y_6616_);
lean_inc_ref(v___y_6615_);
lean_inc(v___y_6614_);
lean_inc(v___y_6613_);
lean_inc_ref(v___y_6612_);
v___x_6727_ = lean_apply_12(v_run_x27_6630_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, lean_box(0));
if (lean_obj_tag(v___x_6727_) == 0)
{
lean_object* v_a_6728_; lean_object* v___x_6730_; uint8_t v_isShared_6731_; uint8_t v_isSharedCheck_6735_; 
v_a_6728_ = lean_ctor_get(v___x_6727_, 0);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6727_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6730_ = v___x_6727_;
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_a_6728_);
lean_dec(v___x_6727_);
v___x_6730_ = lean_box(0);
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
v_resetjp_6729_:
{
lean_object* v___x_6733_; 
if (v_isShared_6731_ == 0)
{
lean_ctor_set_tag(v___x_6730_, 1);
v___x_6733_ = v___x_6730_;
goto v_reusejp_6732_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_a_6728_);
v___x_6733_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6732_;
}
v_reusejp_6732_:
{
v___y_6692_ = v___x_6726_;
v___y_6693_ = v_a_6705_;
v_a_6694_ = v___x_6733_;
goto v___jp_6691_;
}
}
}
else
{
lean_object* v_a_6736_; lean_object* v___x_6738_; uint8_t v_isShared_6739_; uint8_t v_isSharedCheck_6743_; 
v_a_6736_ = lean_ctor_get(v___x_6727_, 0);
v_isSharedCheck_6743_ = !lean_is_exclusive(v___x_6727_);
if (v_isSharedCheck_6743_ == 0)
{
v___x_6738_ = v___x_6727_;
v_isShared_6739_ = v_isSharedCheck_6743_;
goto v_resetjp_6737_;
}
else
{
lean_inc(v_a_6736_);
lean_dec(v___x_6727_);
v___x_6738_ = lean_box(0);
v_isShared_6739_ = v_isSharedCheck_6743_;
goto v_resetjp_6737_;
}
v_resetjp_6737_:
{
lean_object* v___x_6741_; 
if (v_isShared_6739_ == 0)
{
lean_ctor_set_tag(v___x_6738_, 0);
v___x_6741_ = v___x_6738_;
goto v_reusejp_6740_;
}
else
{
lean_object* v_reuseFailAlloc_6742_; 
v_reuseFailAlloc_6742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6742_, 0, v_a_6736_);
v___x_6741_ = v_reuseFailAlloc_6742_;
goto v_reusejp_6740_;
}
v_reusejp_6740_:
{
v___y_6692_ = v___x_6726_;
v___y_6693_ = v_a_6705_;
v_a_6694_ = v___x_6741_;
goto v___jp_6691_;
}
}
}
}
}
}
v___jp_6634_:
{
lean_object* v___x_6636_; lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; 
v___x_6636_ = lean_box(v___y_6635_);
v___x_6637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6637_, 0, v___x_6636_);
v___x_6638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6638_, 0, v___x_6637_);
lean_ctor_set(v___x_6638_, 1, v___x_6633_);
v___x_6639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6639_, 0, v___x_6638_);
return v___x_6639_;
}
v___jp_6641_:
{
if (lean_obj_tag(v___y_6642_) == 0)
{
lean_object* v_a_6643_; uint8_t v___x_6644_; 
v_a_6643_ = lean_ctor_get(v___y_6642_, 0);
lean_inc(v_a_6643_);
lean_dec_ref_known(v___y_6642_, 1);
v___x_6644_ = lean_unbox(v_a_6643_);
if (v___x_6644_ == 0)
{
lean_dec(v_a_6643_);
v_as_x27_6610_ = v_tail_6628_;
v_b_6611_ = v___x_6640_;
goto _start;
}
else
{
if (v_hasTrace_6632_ == 0)
{
uint8_t v___x_6646_; 
v___x_6646_ = lean_unbox(v_a_6643_);
lean_dec(v_a_6643_);
v___y_6635_ = v___x_6646_;
goto v___jp_6634_;
}
else
{
lean_object* v___x_6647_; lean_object* v___x_6648_; uint8_t v___x_6649_; 
v___x_6647_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6648_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6649_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6631_, v_options_6627_, v___x_6648_);
if (v___x_6649_ == 0)
{
uint8_t v___x_6650_; 
v___x_6650_ = lean_unbox(v_a_6643_);
lean_dec(v_a_6643_);
v___y_6635_ = v___x_6650_;
goto v___jp_6634_;
}
else
{
lean_object* v___x_6651_; lean_object* v___x_6652_; 
v___x_6651_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_6652_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6647_, v___x_6651_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_);
if (lean_obj_tag(v___x_6652_) == 0)
{
uint8_t v___x_6653_; 
lean_dec_ref_known(v___x_6652_, 1);
v___x_6653_ = lean_unbox(v_a_6643_);
lean_dec(v_a_6643_);
v___y_6635_ = v___x_6653_;
goto v___jp_6634_;
}
else
{
lean_object* v_a_6654_; lean_object* v___x_6656_; uint8_t v_isShared_6657_; uint8_t v_isSharedCheck_6661_; 
lean_dec(v_a_6643_);
v_a_6654_ = lean_ctor_get(v___x_6652_, 0);
v_isSharedCheck_6661_ = !lean_is_exclusive(v___x_6652_);
if (v_isSharedCheck_6661_ == 0)
{
v___x_6656_ = v___x_6652_;
v_isShared_6657_ = v_isSharedCheck_6661_;
goto v_resetjp_6655_;
}
else
{
lean_inc(v_a_6654_);
lean_dec(v___x_6652_);
v___x_6656_ = lean_box(0);
v_isShared_6657_ = v_isSharedCheck_6661_;
goto v_resetjp_6655_;
}
v_resetjp_6655_:
{
lean_object* v___x_6659_; 
if (v_isShared_6657_ == 0)
{
v___x_6659_ = v___x_6656_;
goto v_reusejp_6658_;
}
else
{
lean_object* v_reuseFailAlloc_6660_; 
v_reuseFailAlloc_6660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6660_, 0, v_a_6654_);
v___x_6659_ = v_reuseFailAlloc_6660_;
goto v_reusejp_6658_;
}
v_reusejp_6658_:
{
return v___x_6659_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6662_; lean_object* v___x_6664_; uint8_t v_isShared_6665_; uint8_t v_isSharedCheck_6669_; 
v_a_6662_ = lean_ctor_get(v___y_6642_, 0);
v_isSharedCheck_6669_ = !lean_is_exclusive(v___y_6642_);
if (v_isSharedCheck_6669_ == 0)
{
v___x_6664_ = v___y_6642_;
v_isShared_6665_ = v_isSharedCheck_6669_;
goto v_resetjp_6663_;
}
else
{
lean_inc(v_a_6662_);
lean_dec(v___y_6642_);
v___x_6664_ = lean_box(0);
v_isShared_6665_ = v_isSharedCheck_6669_;
goto v_resetjp_6663_;
}
v_resetjp_6663_:
{
lean_object* v___x_6667_; 
if (v_isShared_6665_ == 0)
{
v___x_6667_ = v___x_6664_;
goto v_reusejp_6666_;
}
else
{
lean_object* v_reuseFailAlloc_6668_; 
v_reuseFailAlloc_6668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6668_, 0, v_a_6662_);
v___x_6667_ = v_reuseFailAlloc_6668_;
goto v_reusejp_6666_;
}
v_reusejp_6666_:
{
return v___x_6667_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_6610_ = stack[0].m_obj;
lean_object* v_b_6611_ = stack[1].m_obj;
lean_object* v___y_6612_ = stack[2].m_obj;
lean_object* v___y_6613_ = stack[3].m_obj;
lean_object* v___y_6614_ = stack[4].m_obj;
lean_object* v___y_6615_ = stack[5].m_obj;
lean_object* v___y_6616_ = stack[6].m_obj;
lean_object* v___y_6617_ = stack[7].m_obj;
lean_object* v___y_6618_ = stack[8].m_obj;
lean_object* v___y_6619_ = stack[9].m_obj;
lean_object* v___y_6620_ = stack[10].m_obj;
lean_object* v___y_6621_ = stack[11].m_obj;
lean_object* v___y_6622_ = stack[12].m_obj;
lean_object* v_res_6747_;
v_res_6747_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6610_, v_b_6611_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_);
stack->m_obj
 = v_res_6747_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_6748_, lean_object* v_b_6749_, lean_object* v___y_6750_, lean_object* v___y_6751_, lean_object* v___y_6752_, lean_object* v___y_6753_, lean_object* v___y_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_, lean_object* v___y_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_, lean_object* v___y_6761_){
_start:
{
lean_object* v_res_6762_; 
v_res_6762_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6748_, v_b_6749_, v___y_6750_, v___y_6751_, v___y_6752_, v___y_6753_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_, v___y_6760_);
lean_dec(v___y_6760_);
lean_dec_ref(v___y_6759_);
lean_dec(v___y_6758_);
lean_dec_ref(v___y_6757_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6755_);
lean_dec(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec(v___y_6752_);
lean_dec(v___y_6751_);
lean_dec_ref(v___y_6750_);
lean_dec(v_as_x27_6748_);
return v_res_6762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_6765_; lean_object* v___x_6766_; 
v___x_6765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_6766_ = l_Lean_stringToMessageData(v___x_6765_);
return v___x_6766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_6768_; lean_object* v___x_6769_; 
v___x_6768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_6769_ = l_Lean_stringToMessageData(v___x_6768_);
return v___x_6769_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_, lean_object* v_a_6773_, lean_object* v_a_6774_, lean_object* v_a_6775_, lean_object* v_a_6776_, lean_object* v_a_6777_, lean_object* v_a_6778_, lean_object* v_a_6779_, lean_object* v_a_6780_, lean_object* v_a_6781_){
_start:
{
lean_object* v___x_6783_; lean_object* v___x_6784_; 
v___x_6783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_6784_ = l_Lean_Core_checkSystem(v___x_6783_, v_a_6780_, v_a_6781_);
if (lean_obj_tag(v___x_6784_) == 0)
{
lean_object* v___x_6785_; lean_object* v_caches_6786_; lean_object* v_typeAnalysis_6787_; lean_object* v_target_6788_; lean_object* v_hypotheses_6789_; lean_object* v___x_6791_; uint8_t v_isShared_6792_; uint8_t v_isSharedCheck_6874_; 
lean_dec_ref_known(v___x_6784_, 1);
v___x_6785_ = lean_st_ref_take(v_a_6772_);
v_caches_6786_ = lean_ctor_get(v___x_6785_, 0);
v_typeAnalysis_6787_ = lean_ctor_get(v___x_6785_, 1);
v_target_6788_ = lean_ctor_get(v___x_6785_, 2);
v_hypotheses_6789_ = lean_ctor_get(v___x_6785_, 3);
v_isSharedCheck_6874_ = !lean_is_exclusive(v___x_6785_);
if (v_isSharedCheck_6874_ == 0)
{
v___x_6791_ = v___x_6785_;
v_isShared_6792_ = v_isSharedCheck_6874_;
goto v_resetjp_6790_;
}
else
{
lean_inc(v_hypotheses_6789_);
lean_inc(v_target_6788_);
lean_inc(v_typeAnalysis_6787_);
lean_inc(v_caches_6786_);
lean_dec(v___x_6785_);
v___x_6791_ = lean_box(0);
v_isShared_6792_ = v_isSharedCheck_6874_;
goto v_resetjp_6790_;
}
v_resetjp_6790_:
{
uint8_t v___x_6793_; lean_object* v___x_6795_; 
v___x_6793_ = 0;
if (v_isShared_6792_ == 0)
{
v___x_6795_ = v___x_6791_;
goto v_reusejp_6794_;
}
else
{
lean_object* v_reuseFailAlloc_6873_; 
v_reuseFailAlloc_6873_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6873_, 0, v_caches_6786_);
lean_ctor_set(v_reuseFailAlloc_6873_, 1, v_typeAnalysis_6787_);
lean_ctor_set(v_reuseFailAlloc_6873_, 2, v_target_6788_);
lean_ctor_set(v_reuseFailAlloc_6873_, 3, v_hypotheses_6789_);
v___x_6795_ = v_reuseFailAlloc_6873_;
goto v_reusejp_6794_;
}
v_reusejp_6794_:
{
lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___x_6798_; 
lean_ctor_set_uint8(v___x_6795_, sizeof(void*)*4, v___x_6793_);
v___x_6796_ = lean_st_ref_put(v_a_6772_, v___x_6795_);
v___x_6797_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_6798_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_6770_, v___x_6797_, v_a_6771_, v_a_6772_, v_a_6773_, v_a_6774_, v_a_6775_, v_a_6776_, v_a_6777_, v_a_6778_, v_a_6779_, v_a_6780_, v_a_6781_);
if (lean_obj_tag(v___x_6798_) == 0)
{
lean_object* v_a_6799_; lean_object* v___x_6801_; uint8_t v_isShared_6802_; uint8_t v_isSharedCheck_6864_; 
v_a_6799_ = lean_ctor_get(v___x_6798_, 0);
v_isSharedCheck_6864_ = !lean_is_exclusive(v___x_6798_);
if (v_isSharedCheck_6864_ == 0)
{
v___x_6801_ = v___x_6798_;
v_isShared_6802_ = v_isSharedCheck_6864_;
goto v_resetjp_6800_;
}
else
{
lean_inc(v_a_6799_);
lean_dec(v___x_6798_);
v___x_6801_ = lean_box(0);
v_isShared_6802_ = v_isSharedCheck_6864_;
goto v_resetjp_6800_;
}
v_resetjp_6800_:
{
lean_object* v_fst_6803_; 
v_fst_6803_ = lean_ctor_get(v_a_6799_, 0);
lean_inc(v_fst_6803_);
lean_dec(v_a_6799_);
if (lean_obj_tag(v_fst_6803_) == 0)
{
lean_object* v___x_6804_; uint8_t v_didChange_6805_; 
v___x_6804_ = lean_st_ref_get(v_a_6772_);
v_didChange_6805_ = lean_ctor_get_uint8(v___x_6804_, sizeof(void*)*4);
lean_dec(v___x_6804_);
if (v_didChange_6805_ == 0)
{
lean_object* v_toCold_6806_; lean_object* v_options_6807_; uint8_t v_hasTrace_6808_; 
v_toCold_6806_ = lean_ctor_get(v_a_6780_, 0);
v_options_6807_ = lean_ctor_get(v_toCold_6806_, 2);
v_hasTrace_6808_ = lean_ctor_get_uint8(v_options_6807_, sizeof(void*)*1);
if (v_hasTrace_6808_ == 0)
{
lean_object* v___x_6809_; lean_object* v___x_6811_; 
v___x_6809_ = lean_box(v_didChange_6805_);
if (v_isShared_6802_ == 0)
{
lean_ctor_set(v___x_6801_, 0, v___x_6809_);
v___x_6811_ = v___x_6801_;
goto v_reusejp_6810_;
}
else
{
lean_object* v_reuseFailAlloc_6812_; 
v_reuseFailAlloc_6812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6812_, 0, v___x_6809_);
v___x_6811_ = v_reuseFailAlloc_6812_;
goto v_reusejp_6810_;
}
v_reusejp_6810_:
{
return v___x_6811_;
}
}
else
{
lean_object* v_inheritedTraceOptions_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; uint8_t v___x_6816_; 
v_inheritedTraceOptions_6813_ = lean_ctor_get(v_toCold_6806_, 11);
v___x_6814_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6815_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6816_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6813_, v_options_6807_, v___x_6815_);
if (v___x_6816_ == 0)
{
lean_object* v___x_6817_; lean_object* v___x_6819_; 
v___x_6817_ = lean_box(v_didChange_6805_);
if (v_isShared_6802_ == 0)
{
lean_ctor_set(v___x_6801_, 0, v___x_6817_);
v___x_6819_ = v___x_6801_;
goto v_reusejp_6818_;
}
else
{
lean_object* v_reuseFailAlloc_6820_; 
v_reuseFailAlloc_6820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6820_, 0, v___x_6817_);
v___x_6819_ = v_reuseFailAlloc_6820_;
goto v_reusejp_6818_;
}
v_reusejp_6818_:
{
return v___x_6819_;
}
}
else
{
lean_object* v___x_6821_; lean_object* v___x_6822_; 
lean_del_object(v___x_6801_);
v___x_6821_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6822_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6814_, v___x_6821_, v_a_6778_, v_a_6779_, v_a_6780_, v_a_6781_);
if (lean_obj_tag(v___x_6822_) == 0)
{
lean_object* v___x_6824_; uint8_t v_isShared_6825_; uint8_t v_isSharedCheck_6830_; 
v_isSharedCheck_6830_ = !lean_is_exclusive(v___x_6822_);
if (v_isSharedCheck_6830_ == 0)
{
lean_object* v_unused_6831_; 
v_unused_6831_ = lean_ctor_get(v___x_6822_, 0);
lean_dec(v_unused_6831_);
v___x_6824_ = v___x_6822_;
v_isShared_6825_ = v_isSharedCheck_6830_;
goto v_resetjp_6823_;
}
else
{
lean_dec(v___x_6822_);
v___x_6824_ = lean_box(0);
v_isShared_6825_ = v_isSharedCheck_6830_;
goto v_resetjp_6823_;
}
v_resetjp_6823_:
{
lean_object* v___x_6826_; lean_object* v___x_6828_; 
v___x_6826_ = lean_box(v_didChange_6805_);
if (v_isShared_6825_ == 0)
{
lean_ctor_set(v___x_6824_, 0, v___x_6826_);
v___x_6828_ = v___x_6824_;
goto v_reusejp_6827_;
}
else
{
lean_object* v_reuseFailAlloc_6829_; 
v_reuseFailAlloc_6829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6829_, 0, v___x_6826_);
v___x_6828_ = v_reuseFailAlloc_6829_;
goto v_reusejp_6827_;
}
v_reusejp_6827_:
{
return v___x_6828_;
}
}
}
else
{
lean_object* v_a_6832_; lean_object* v___x_6834_; uint8_t v_isShared_6835_; uint8_t v_isSharedCheck_6839_; 
v_a_6832_ = lean_ctor_get(v___x_6822_, 0);
v_isSharedCheck_6839_ = !lean_is_exclusive(v___x_6822_);
if (v_isSharedCheck_6839_ == 0)
{
v___x_6834_ = v___x_6822_;
v_isShared_6835_ = v_isSharedCheck_6839_;
goto v_resetjp_6833_;
}
else
{
lean_inc(v_a_6832_);
lean_dec(v___x_6822_);
v___x_6834_ = lean_box(0);
v_isShared_6835_ = v_isSharedCheck_6839_;
goto v_resetjp_6833_;
}
v_resetjp_6833_:
{
lean_object* v___x_6837_; 
if (v_isShared_6835_ == 0)
{
v___x_6837_ = v___x_6834_;
goto v_reusejp_6836_;
}
else
{
lean_object* v_reuseFailAlloc_6838_; 
v_reuseFailAlloc_6838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6838_, 0, v_a_6832_);
v___x_6837_ = v_reuseFailAlloc_6838_;
goto v_reusejp_6836_;
}
v_reusejp_6836_:
{
return v___x_6837_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_6840_; lean_object* v_options_6841_; uint8_t v_hasTrace_6842_; 
lean_del_object(v___x_6801_);
v_toCold_6840_ = lean_ctor_get(v_a_6780_, 0);
v_options_6841_ = lean_ctor_get(v_toCold_6840_, 2);
v_hasTrace_6842_ = lean_ctor_get_uint8(v_options_6841_, sizeof(void*)*1);
if (v_hasTrace_6842_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_6844_; lean_object* v___x_6845_; lean_object* v___x_6846_; uint8_t v___x_6847_; 
v_inheritedTraceOptions_6844_ = lean_ctor_get(v_toCold_6840_, 11);
v___x_6845_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6846_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6847_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6844_, v_options_6841_, v___x_6846_);
if (v___x_6847_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6849_; lean_object* v___x_6850_; 
v___x_6849_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6850_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6845_, v___x_6849_, v_a_6778_, v_a_6779_, v_a_6780_, v_a_6781_);
if (lean_obj_tag(v___x_6850_) == 0)
{
lean_dec_ref_known(v___x_6850_, 1);
goto _start;
}
else
{
lean_object* v_a_6852_; lean_object* v___x_6854_; uint8_t v_isShared_6855_; uint8_t v_isSharedCheck_6859_; 
v_a_6852_ = lean_ctor_get(v___x_6850_, 0);
v_isSharedCheck_6859_ = !lean_is_exclusive(v___x_6850_);
if (v_isSharedCheck_6859_ == 0)
{
v___x_6854_ = v___x_6850_;
v_isShared_6855_ = v_isSharedCheck_6859_;
goto v_resetjp_6853_;
}
else
{
lean_inc(v_a_6852_);
lean_dec(v___x_6850_);
v___x_6854_ = lean_box(0);
v_isShared_6855_ = v_isSharedCheck_6859_;
goto v_resetjp_6853_;
}
v_resetjp_6853_:
{
lean_object* v___x_6857_; 
if (v_isShared_6855_ == 0)
{
v___x_6857_ = v___x_6854_;
goto v_reusejp_6856_;
}
else
{
lean_object* v_reuseFailAlloc_6858_; 
v_reuseFailAlloc_6858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6858_, 0, v_a_6852_);
v___x_6857_ = v_reuseFailAlloc_6858_;
goto v_reusejp_6856_;
}
v_reusejp_6856_:
{
return v___x_6857_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_6860_; lean_object* v___x_6862_; 
v_val_6860_ = lean_ctor_get(v_fst_6803_, 0);
lean_inc(v_val_6860_);
lean_dec_ref_known(v_fst_6803_, 1);
if (v_isShared_6802_ == 0)
{
lean_ctor_set(v___x_6801_, 0, v_val_6860_);
v___x_6862_ = v___x_6801_;
goto v_reusejp_6861_;
}
else
{
lean_object* v_reuseFailAlloc_6863_; 
v_reuseFailAlloc_6863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6863_, 0, v_val_6860_);
v___x_6862_ = v_reuseFailAlloc_6863_;
goto v_reusejp_6861_;
}
v_reusejp_6861_:
{
return v___x_6862_;
}
}
}
}
else
{
lean_object* v_a_6865_; lean_object* v___x_6867_; uint8_t v_isShared_6868_; uint8_t v_isSharedCheck_6872_; 
v_a_6865_ = lean_ctor_get(v___x_6798_, 0);
v_isSharedCheck_6872_ = !lean_is_exclusive(v___x_6798_);
if (v_isSharedCheck_6872_ == 0)
{
v___x_6867_ = v___x_6798_;
v_isShared_6868_ = v_isSharedCheck_6872_;
goto v_resetjp_6866_;
}
else
{
lean_inc(v_a_6865_);
lean_dec(v___x_6798_);
v___x_6867_ = lean_box(0);
v_isShared_6868_ = v_isSharedCheck_6872_;
goto v_resetjp_6866_;
}
v_resetjp_6866_:
{
lean_object* v___x_6870_; 
if (v_isShared_6868_ == 0)
{
v___x_6870_ = v___x_6867_;
goto v_reusejp_6869_;
}
else
{
lean_object* v_reuseFailAlloc_6871_; 
v_reuseFailAlloc_6871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6871_, 0, v_a_6865_);
v___x_6870_ = v_reuseFailAlloc_6871_;
goto v_reusejp_6869_;
}
v_reusejp_6869_:
{
return v___x_6870_;
}
}
}
}
}
}
else
{
lean_object* v_a_6875_; lean_object* v___x_6877_; uint8_t v_isShared_6878_; uint8_t v_isSharedCheck_6882_; 
v_a_6875_ = lean_ctor_get(v___x_6784_, 0);
v_isSharedCheck_6882_ = !lean_is_exclusive(v___x_6784_);
if (v_isSharedCheck_6882_ == 0)
{
v___x_6877_ = v___x_6784_;
v_isShared_6878_ = v_isSharedCheck_6882_;
goto v_resetjp_6876_;
}
else
{
lean_inc(v_a_6875_);
lean_dec(v___x_6784_);
v___x_6877_ = lean_box(0);
v_isShared_6878_ = v_isSharedCheck_6882_;
goto v_resetjp_6876_;
}
v_resetjp_6876_:
{
lean_object* v___x_6880_; 
if (v_isShared_6878_ == 0)
{
v___x_6880_ = v___x_6877_;
goto v_reusejp_6879_;
}
else
{
lean_object* v_reuseFailAlloc_6881_; 
v_reuseFailAlloc_6881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6881_, 0, v_a_6875_);
v___x_6880_ = v_reuseFailAlloc_6881_;
goto v_reusejp_6879_;
}
v_reusejp_6879_:
{
return v___x_6880_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_passes_6770_ = stack[0].m_obj;
lean_object* v_a_6771_ = stack[1].m_obj;
lean_object* v_a_6772_ = stack[2].m_obj;
lean_object* v_a_6773_ = stack[3].m_obj;
lean_object* v_a_6774_ = stack[4].m_obj;
lean_object* v_a_6775_ = stack[5].m_obj;
lean_object* v_a_6776_ = stack[6].m_obj;
lean_object* v_a_6777_ = stack[7].m_obj;
lean_object* v_a_6778_ = stack[8].m_obj;
lean_object* v_a_6779_ = stack[9].m_obj;
lean_object* v_a_6780_ = stack[10].m_obj;
lean_object* v_a_6781_ = stack[11].m_obj;
lean_object* v_res_6883_;
v_res_6883_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6770_, v_a_6771_, v_a_6772_, v_a_6773_, v_a_6774_, v_a_6775_, v_a_6776_, v_a_6777_, v_a_6778_, v_a_6779_, v_a_6780_, v_a_6781_);
stack->m_obj
 = v_res_6883_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6884_, lean_object* v_a_6885_, lean_object* v_a_6886_, lean_object* v_a_6887_, lean_object* v_a_6888_, lean_object* v_a_6889_, lean_object* v_a_6890_, lean_object* v_a_6891_, lean_object* v_a_6892_, lean_object* v_a_6893_, lean_object* v_a_6894_, lean_object* v_a_6895_, lean_object* v_a_6896_){
_start:
{
lean_object* v_res_6897_; 
v_res_6897_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_, v_a_6891_, v_a_6892_, v_a_6893_, v_a_6894_, v_a_6895_);
lean_dec(v_a_6895_);
lean_dec_ref(v_a_6894_);
lean_dec(v_a_6893_);
lean_dec_ref(v_a_6892_);
lean_dec(v_a_6891_);
lean_dec_ref(v_a_6890_);
lean_dec(v_a_6889_);
lean_dec_ref(v_a_6888_);
lean_dec(v_a_6887_);
lean_dec(v_a_6886_);
lean_dec_ref(v_a_6885_);
lean_dec(v_passes_6884_);
return v_res_6897_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6898_, lean_object* v_msg_6899_, lean_object* v___y_6900_, lean_object* v___y_6901_, lean_object* v___y_6902_, lean_object* v___y_6903_, lean_object* v___y_6904_, lean_object* v___y_6905_, lean_object* v___y_6906_, lean_object* v___y_6907_, lean_object* v___y_6908_, lean_object* v___y_6909_, lean_object* v___y_6910_){
_start:
{
lean_object* v___x_6912_; 
v___x_6912_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6898_, v_msg_6899_, v___y_6907_, v___y_6908_, v___y_6909_, v___y_6910_);
return v___x_6912_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_6898_ = stack[0].m_obj;
lean_object* v_msg_6899_ = stack[1].m_obj;
lean_object* v___y_6900_ = stack[2].m_obj;
lean_object* v___y_6901_ = stack[3].m_obj;
lean_object* v___y_6902_ = stack[4].m_obj;
lean_object* v___y_6903_ = stack[5].m_obj;
lean_object* v___y_6904_ = stack[6].m_obj;
lean_object* v___y_6905_ = stack[7].m_obj;
lean_object* v___y_6906_ = stack[8].m_obj;
lean_object* v___y_6907_ = stack[9].m_obj;
lean_object* v___y_6908_ = stack[10].m_obj;
lean_object* v___y_6909_ = stack[11].m_obj;
lean_object* v___y_6910_ = stack[12].m_obj;
lean_object* v_res_6913_;
v_res_6913_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6898_, v_msg_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_, v___y_6910_);
stack->m_obj
 = v_res_6913_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6914_, lean_object* v_msg_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_, lean_object* v___y_6922_, lean_object* v___y_6923_, lean_object* v___y_6924_, lean_object* v___y_6925_, lean_object* v___y_6926_, lean_object* v___y_6927_){
_start:
{
lean_object* v_res_6928_; 
v_res_6928_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6914_, v_msg_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_, v___y_6922_, v___y_6923_, v___y_6924_, v___y_6925_, v___y_6926_);
lean_dec(v___y_6926_);
lean_dec_ref(v___y_6925_);
lean_dec(v___y_6924_);
lean_dec_ref(v___y_6923_);
lean_dec(v___y_6922_);
lean_dec_ref(v___y_6921_);
lean_dec(v___y_6920_);
lean_dec_ref(v___y_6919_);
lean_dec(v___y_6918_);
lean_dec(v___y_6917_);
lean_dec_ref(v___y_6916_);
return v_res_6928_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6929_, lean_object* v_x_6930_, lean_object* v___y_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_, lean_object* v___y_6936_, lean_object* v___y_6937_, lean_object* v___y_6938_, lean_object* v___y_6939_, lean_object* v___y_6940_, lean_object* v___y_6941_){
_start:
{
lean_object* v___x_6943_; 
v___x_6943_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6930_);
return v___x_6943_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_6930_ = stack[1].m_obj;
lean_object* v___y_6931_ = stack[2].m_obj;
lean_object* v___y_6932_ = stack[3].m_obj;
lean_object* v___y_6933_ = stack[4].m_obj;
lean_object* v___y_6934_ = stack[5].m_obj;
lean_object* v___y_6935_ = stack[6].m_obj;
lean_object* v___y_6936_ = stack[7].m_obj;
lean_object* v___y_6937_ = stack[8].m_obj;
lean_object* v___y_6938_ = stack[9].m_obj;
lean_object* v___y_6939_ = stack[10].m_obj;
lean_object* v___y_6940_ = stack[11].m_obj;
lean_object* v___y_6941_ = stack[12].m_obj;
lean_object* v_res_6944_;
v_res_6944_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_box(0), v_x_6930_, v___y_6931_, v___y_6932_, v___y_6933_, v___y_6934_, v___y_6935_, v___y_6936_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_);
stack->m_obj
 = v_res_6944_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6945_, lean_object* v_x_6946_, lean_object* v___y_6947_, lean_object* v___y_6948_, lean_object* v___y_6949_, lean_object* v___y_6950_, lean_object* v___y_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_, lean_object* v___y_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_){
_start:
{
lean_object* v_res_6959_; 
v_res_6959_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6945_, v_x_6946_, v___y_6947_, v___y_6948_, v___y_6949_, v___y_6950_, v___y_6951_, v___y_6952_, v___y_6953_, v___y_6954_, v___y_6955_, v___y_6956_, v___y_6957_);
lean_dec(v___y_6957_);
lean_dec_ref(v___y_6956_);
lean_dec(v___y_6955_);
lean_dec_ref(v___y_6954_);
lean_dec(v___y_6953_);
lean_dec_ref(v___y_6952_);
lean_dec(v___y_6951_);
lean_dec_ref(v___y_6950_);
lean_dec(v___y_6949_);
lean_dec(v___y_6948_);
lean_dec_ref(v___y_6947_);
return v_res_6959_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6960_, lean_object* v_as_x27_6961_, lean_object* v_b_6962_, lean_object* v_a_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_, lean_object* v___y_6970_, lean_object* v___y_6971_, lean_object* v___y_6972_, lean_object* v___y_6973_, lean_object* v___y_6974_){
_start:
{
lean_object* v___x_6976_; 
v___x_6976_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6961_, v_b_6962_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_, v___y_6971_, v___y_6972_, v___y_6973_, v___y_6974_);
return v___x_6976_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_6960_ = stack[0].m_obj;
lean_object* v_as_x27_6961_ = stack[1].m_obj;
lean_object* v_b_6962_ = stack[2].m_obj;
lean_object* v___y_6964_ = stack[4].m_obj;
lean_object* v___y_6965_ = stack[5].m_obj;
lean_object* v___y_6966_ = stack[6].m_obj;
lean_object* v___y_6967_ = stack[7].m_obj;
lean_object* v___y_6968_ = stack[8].m_obj;
lean_object* v___y_6969_ = stack[9].m_obj;
lean_object* v___y_6970_ = stack[10].m_obj;
lean_object* v___y_6971_ = stack[11].m_obj;
lean_object* v___y_6972_ = stack[12].m_obj;
lean_object* v___y_6973_ = stack[13].m_obj;
lean_object* v___y_6974_ = stack[14].m_obj;
lean_object* v_res_6977_;
v_res_6977_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6960_, v_as_x27_6961_, v_b_6962_, lean_box(0), v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_, v___y_6971_, v___y_6972_, v___y_6973_, v___y_6974_);
stack->m_obj
 = v_res_6977_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6978_, lean_object* v_as_x27_6979_, lean_object* v_b_6980_, lean_object* v_a_6981_, lean_object* v___y_6982_, lean_object* v___y_6983_, lean_object* v___y_6984_, lean_object* v___y_6985_, lean_object* v___y_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_){
_start:
{
lean_object* v_res_6994_; 
v_res_6994_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6978_, v_as_x27_6979_, v_b_6980_, v_a_6981_, v___y_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_, v___y_6988_, v___y_6989_, v___y_6990_, v___y_6991_, v___y_6992_);
lean_dec(v___y_6992_);
lean_dec_ref(v___y_6991_);
lean_dec(v___y_6990_);
lean_dec_ref(v___y_6989_);
lean_dec(v___y_6988_);
lean_dec_ref(v___y_6987_);
lean_dec(v___y_6986_);
lean_dec_ref(v___y_6985_);
lean_dec(v___y_6984_);
lean_dec(v___y_6983_);
lean_dec_ref(v___y_6982_);
lean_dec(v_as_x27_6979_);
lean_dec(v_as_6978_);
return v_res_6994_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6995_, lean_object* v_data_6996_, lean_object* v_ref_6997_, lean_object* v_msg_6998_, lean_object* v___y_6999_, lean_object* v___y_7000_, lean_object* v___y_7001_, lean_object* v___y_7002_, lean_object* v___y_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_, lean_object* v___y_7008_, lean_object* v___y_7009_){
_start:
{
lean_object* v___x_7011_; 
v___x_7011_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6995_, v_data_6996_, v_ref_6997_, v_msg_6998_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_);
return v___x_7011_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_6995_ = stack[0].m_obj;
lean_object* v_data_6996_ = stack[1].m_obj;
lean_object* v_ref_6997_ = stack[2].m_obj;
lean_object* v_msg_6998_ = stack[3].m_obj;
lean_object* v___y_6999_ = stack[4].m_obj;
lean_object* v___y_7000_ = stack[5].m_obj;
lean_object* v___y_7001_ = stack[6].m_obj;
lean_object* v___y_7002_ = stack[7].m_obj;
lean_object* v___y_7003_ = stack[8].m_obj;
lean_object* v___y_7004_ = stack[9].m_obj;
lean_object* v___y_7005_ = stack[10].m_obj;
lean_object* v___y_7006_ = stack[11].m_obj;
lean_object* v___y_7007_ = stack[12].m_obj;
lean_object* v___y_7008_ = stack[13].m_obj;
lean_object* v___y_7009_ = stack[14].m_obj;
lean_object* v_res_7012_;
v_res_7012_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6995_, v_data_6996_, v_ref_6997_, v_msg_6998_, v___y_6999_, v___y_7000_, v___y_7001_, v___y_7002_, v___y_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_);
stack->m_obj
 = v_res_7012_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_7013_, lean_object* v_data_7014_, lean_object* v_ref_7015_, lean_object* v_msg_7016_, lean_object* v___y_7017_, lean_object* v___y_7018_, lean_object* v___y_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_, lean_object* v___y_7025_, lean_object* v___y_7026_, lean_object* v___y_7027_, lean_object* v___y_7028_){
_start:
{
lean_object* v_res_7029_; 
v_res_7029_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_7013_, v_data_7014_, v_ref_7015_, v_msg_7016_, v___y_7017_, v___y_7018_, v___y_7019_, v___y_7020_, v___y_7021_, v___y_7022_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_);
lean_dec(v___y_7027_);
lean_dec_ref(v___y_7026_);
lean_dec(v___y_7025_);
lean_dec_ref(v___y_7024_);
lean_dec(v___y_7023_);
lean_dec_ref(v___y_7022_);
lean_dec(v___y_7021_);
lean_dec_ref(v___y_7020_);
lean_dec(v___y_7019_);
lean_dec(v___y_7018_);
lean_dec_ref(v___y_7017_);
return v_res_7029_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_7030_, lean_object* v_a_7031_, lean_object* v_a_7032_, lean_object* v_a_7033_, lean_object* v_a_7034_, lean_object* v_a_7035_, lean_object* v_a_7036_, lean_object* v_a_7037_, lean_object* v_a_7038_, lean_object* v_a_7039_, lean_object* v_a_7040_, lean_object* v_a_7041_){
_start:
{
lean_object* v___x_7043_; 
v___x_7043_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_7030_, v_a_7031_, v_a_7032_, v_a_7033_, v_a_7034_, v_a_7035_, v_a_7036_, v_a_7037_, v_a_7038_, v_a_7039_, v_a_7040_, v_a_7041_);
if (lean_obj_tag(v___x_7043_) == 0)
{
lean_object* v_a_7044_; lean_object* v___x_7045_; lean_object* v___x_7047_; uint8_t v_isShared_7048_; uint8_t v_isSharedCheck_7052_; 
v_a_7044_ = lean_ctor_get(v___x_7043_, 0);
lean_inc(v_a_7044_);
lean_dec_ref_known(v___x_7043_, 1);
v___x_7045_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_7031_, v_a_7032_);
v_isSharedCheck_7052_ = !lean_is_exclusive(v___x_7045_);
if (v_isSharedCheck_7052_ == 0)
{
lean_object* v_unused_7053_; 
v_unused_7053_ = lean_ctor_get(v___x_7045_, 0);
lean_dec(v_unused_7053_);
v___x_7047_ = v___x_7045_;
v_isShared_7048_ = v_isSharedCheck_7052_;
goto v_resetjp_7046_;
}
else
{
lean_dec(v___x_7045_);
v___x_7047_ = lean_box(0);
v_isShared_7048_ = v_isSharedCheck_7052_;
goto v_resetjp_7046_;
}
v_resetjp_7046_:
{
lean_object* v___x_7050_; 
if (v_isShared_7048_ == 0)
{
lean_ctor_set(v___x_7047_, 0, v_a_7044_);
v___x_7050_ = v___x_7047_;
goto v_reusejp_7049_;
}
else
{
lean_object* v_reuseFailAlloc_7051_; 
v_reuseFailAlloc_7051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7051_, 0, v_a_7044_);
v___x_7050_ = v_reuseFailAlloc_7051_;
goto v_reusejp_7049_;
}
v_reusejp_7049_:
{
return v___x_7050_;
}
}
}
else
{
return v___x_7043_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_0interp(lean_interpreter_value* stack)
{
lean_object* v_passes_7030_ = stack[0].m_obj;
lean_object* v_a_7031_ = stack[1].m_obj;
lean_object* v_a_7032_ = stack[2].m_obj;
lean_object* v_a_7033_ = stack[3].m_obj;
lean_object* v_a_7034_ = stack[4].m_obj;
lean_object* v_a_7035_ = stack[5].m_obj;
lean_object* v_a_7036_ = stack[6].m_obj;
lean_object* v_a_7037_ = stack[7].m_obj;
lean_object* v_a_7038_ = stack[8].m_obj;
lean_object* v_a_7039_ = stack[9].m_obj;
lean_object* v_a_7040_ = stack[10].m_obj;
lean_object* v_a_7041_ = stack[11].m_obj;
lean_object* v_res_7054_;
v_res_7054_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_7030_, v_a_7031_, v_a_7032_, v_a_7033_, v_a_7034_, v_a_7035_, v_a_7036_, v_a_7037_, v_a_7038_, v_a_7039_, v_a_7040_, v_a_7041_);
stack->m_obj
 = v_res_7054_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_7055_, lean_object* v_a_7056_, lean_object* v_a_7057_, lean_object* v_a_7058_, lean_object* v_a_7059_, lean_object* v_a_7060_, lean_object* v_a_7061_, lean_object* v_a_7062_, lean_object* v_a_7063_, lean_object* v_a_7064_, lean_object* v_a_7065_, lean_object* v_a_7066_, lean_object* v_a_7067_){
_start:
{
lean_object* v_res_7068_; 
v_res_7068_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_7055_, v_a_7056_, v_a_7057_, v_a_7058_, v_a_7059_, v_a_7060_, v_a_7061_, v_a_7062_, v_a_7063_, v_a_7064_, v_a_7065_, v_a_7066_);
lean_dec(v_a_7066_);
lean_dec_ref(v_a_7065_);
lean_dec(v_a_7064_);
lean_dec_ref(v_a_7063_);
lean_dec(v_a_7062_);
lean_dec_ref(v_a_7061_);
lean_dec(v_a_7060_);
lean_dec_ref(v_a_7059_);
lean_dec(v_a_7058_);
lean_dec(v_a_7057_);
lean_dec_ref(v_a_7056_);
lean_dec(v_passes_7055_);
return v_res_7068_;
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
