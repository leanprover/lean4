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
lean_object* v_type_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_6389__overap_2883_; lean_object* v___x_2884_; 
v_type_2879_ = lean_ctor_get(v___y_2856_, 1);
lean_inc_ref(v_type_2879_);
lean_dec_ref(v___y_2856_);
v___x_2880_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2881_ = l_Lean_MessageData_ofExpr(v_type_2879_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_6389__overap_2883_ = l_Lean_addTrace___redArg(v___x_2851_, v___x_2852_, v_toMonadRef_2853_, v___f_2854_, v_cls_2876_, v___x_2882_);
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
v___x_2884_ = lean_apply_12(v___x_6389__overap_2883_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, lean_box(0));
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
lean_object* v___y_2936_; lean_object* v___x_2937_; lean_object* v_toApplicative_2938_; lean_object* v_toFunctor_2939_; lean_object* v_toSeq_2940_; lean_object* v_toSeqLeft_2941_; lean_object* v_toSeqRight_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___f_2945_; lean_object* v___f_2946_; lean_object* v___x_2947_; lean_object* v___f_2948_; lean_object* v___f_2949_; lean_object* v___f_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_toApplicative_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3006_; 
v___x_2937_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2938_ = lean_ctor_get(v___x_2937_, 0);
v_toFunctor_2939_ = lean_ctor_get(v_toApplicative_2938_, 0);
v_toSeq_2940_ = lean_ctor_get(v_toApplicative_2938_, 2);
v_toSeqLeft_2941_ = lean_ctor_get(v_toApplicative_2938_, 3);
v_toSeqRight_2942_ = lean_ctor_get(v_toApplicative_2938_, 4);
v___f_2943_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2944_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2939_, 2);
v___f_2945_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2945_, 0, v_toFunctor_2939_);
v___f_2946_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2946_, 0, v_toFunctor_2939_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___f_2945_);
lean_ctor_set(v___x_2947_, 1, v___f_2946_);
lean_inc(v_toSeqRight_2942_);
v___f_2948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2948_, 0, v_toSeqRight_2942_);
lean_inc(v_toSeqLeft_2941_);
v___f_2949_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2949_, 0, v_toSeqLeft_2941_);
lean_inc(v_toSeq_2940_);
v___f_2950_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2950_, 0, v_toSeq_2940_);
v___x_2951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2947_);
lean_ctor_set(v___x_2951_, 1, v___f_2943_);
lean_ctor_set(v___x_2951_, 2, v___f_2950_);
lean_ctor_set(v___x_2951_, 3, v___f_2949_);
lean_ctor_set(v___x_2951_, 4, v___f_2948_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___f_2944_);
v___x_2953_ = l_StateRefT_x27_instMonad___redArg(v___x_2952_);
v_toApplicative_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2953_, 1);
lean_dec(v_unused_3007_);
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_3006_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_toApplicative_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3006_;
goto v_resetjp_2955_;
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
v___jp_2935_:
{
if (lean_obj_tag(v___y_2936_) == 0)
{
lean_dec_ref_known(v___y_2936_, 1);
goto v___jp_2917_;
}
else
{
lean_dec_ref(v_hyps_2904_);
return v___y_2936_;
}
}
v_resetjp_2955_:
{
lean_object* v_toFunctor_2958_; lean_object* v_toSeq_2959_; lean_object* v_toSeqLeft_2960_; lean_object* v_toSeqRight_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3004_; 
v_toFunctor_2958_ = lean_ctor_get(v_toApplicative_2954_, 0);
v_toSeq_2959_ = lean_ctor_get(v_toApplicative_2954_, 2);
v_toSeqLeft_2960_ = lean_ctor_get(v_toApplicative_2954_, 3);
v_toSeqRight_2961_ = lean_ctor_get(v_toApplicative_2954_, 4);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_toApplicative_2954_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v_toApplicative_2954_, 1);
lean_dec(v_unused_3005_);
v___x_2963_ = v_toApplicative_2954_;
v_isShared_2964_ = v_isSharedCheck_3004_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_toSeqRight_2961_);
lean_inc(v_toSeqLeft_2960_);
lean_inc(v_toSeq_2959_);
lean_inc(v_toFunctor_2958_);
lean_dec(v_toApplicative_2954_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3004_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___f_2965_; lean_object* v___f_2966_; lean_object* v___f_2967_; lean_object* v___f_2968_; lean_object* v___x_2969_; lean_object* v___f_2970_; lean_object* v___f_2971_; lean_object* v___f_2972_; lean_object* v___x_2974_; 
v___f_2965_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2966_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2958_);
v___f_2967_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2967_, 0, v_toFunctor_2958_);
v___f_2968_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2968_, 0, v_toFunctor_2958_);
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___f_2967_);
lean_ctor_set(v___x_2969_, 1, v___f_2968_);
v___f_2970_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2970_, 0, v_toSeqRight_2961_);
v___f_2971_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2971_, 0, v_toSeqLeft_2960_);
v___f_2972_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2972_, 0, v_toSeq_2959_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 4, v___f_2970_);
lean_ctor_set(v___x_2963_, 3, v___f_2971_);
lean_ctor_set(v___x_2963_, 2, v___f_2972_);
lean_ctor_set(v___x_2963_, 1, v___f_2965_);
lean_ctor_set(v___x_2963_, 0, v___x_2969_);
v___x_2974_ = v___x_2963_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___f_2965_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v___f_2972_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v___f_2971_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v___f_2970_);
v___x_2974_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___f_2966_);
lean_ctor_set(v___x_2956_, 0, v___x_2974_);
v___x_2976_ = v___x_2956_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___f_2966_);
v___x_2976_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_toMonadRef_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2977_ = l_StateRefT_x27_instMonad___redArg(v___x_2976_);
v___x_2978_ = l_ReaderT_instMonad___redArg(v___x_2977_);
v___x_2979_ = l_StateRefT_x27_instMonad___redArg(v___x_2978_);
v___x_2980_ = l_ReaderT_instMonad___redArg(v___x_2979_);
v___x_2981_ = l_ReaderT_instMonad___redArg(v___x_2980_);
v___x_2982_ = l_StateRefT_x27_instMonad___redArg(v___x_2981_);
v___x_2983_ = l_ReaderT_instMonad___redArg(v___x_2982_);
v___x_2984_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2985_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_2986_ = lean_ctor_get(v___x_2985_, 0);
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = lean_array_get_size(v_hyps_2904_);
v___x_2989_ = lean_nat_dec_lt(v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_dec_ref(v___x_2983_);
goto v___jp_2917_;
}
else
{
lean_object* v___f_2990_; lean_object* v___f_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___f_2990_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
lean_inc_ref(v_toMonadRef_2986_);
lean_inc_ref(v___x_2983_);
v___f_2991_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 18, 4);
lean_closure_set(v___f_2991_, 0, v___x_2983_);
lean_closure_set(v___f_2991_, 1, v___x_2984_);
lean_closure_set(v___f_2991_, 2, v_toMonadRef_2986_);
lean_closure_set(v___f_2991_, 3, v___f_2990_);
v___x_2992_ = lean_box(0);
v___x_2993_ = lean_nat_dec_le(v___x_2988_, v___x_2988_);
if (v___x_2993_ == 0)
{
if (v___x_2989_ == 0)
{
lean_dec_ref(v___f_2991_);
lean_dec_ref(v___x_2983_);
goto v___jp_2917_;
}
else
{
size_t v___x_2994_; size_t v___x_2995_; lean_object* v___x_6041__overap_2996_; lean_object* v___x_2997_; 
v___x_2994_ = ((size_t)0ULL);
v___x_2995_ = lean_usize_of_nat(v___x_2988_);
lean_inc_ref(v_hyps_2904_);
v___x_6041__overap_2996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2983_, v___f_2991_, v_hyps_2904_, v___x_2994_, v___x_2995_, v___x_2992_);
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
v___x_2997_ = lean_apply_12(v___x_6041__overap_2996_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, lean_box(0));
v___y_2936_ = v___x_2997_;
goto v___jp_2935_;
}
}
else
{
size_t v___x_2998_; size_t v___x_2999_; lean_object* v___x_6044__overap_3000_; lean_object* v___x_3001_; 
v___x_2998_ = ((size_t)0ULL);
v___x_2999_ = lean_usize_of_nat(v___x_2988_);
lean_inc_ref(v_hyps_2904_);
v___x_6044__overap_3000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2983_, v___f_2991_, v_hyps_2904_, v___x_2998_, v___x_2999_, v___x_2992_);
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
v___x_3001_ = lean_apply_12(v___x_6044__overap_3000_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, lean_box(0));
v___y_2936_ = v___x_3001_;
goto v___jp_2935_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_3022_){
_start:
{
lean_object* v___x_3024_; lean_object* v_hypotheses_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_st_ref_get(v_a_3022_);
v_hypotheses_3025_ = lean_ctor_get(v___x_3024_, 3);
lean_inc_ref(v_hypotheses_3025_);
lean_dec(v___x_3024_);
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_hypotheses_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_3027_);
lean_dec(v_a_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v_hypotheses_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_st_ref_get(v_a_3031_);
v_hypotheses_3043_ = lean_ctor_get(v___x_3042_, 3);
lean_inc_ref(v_hypotheses_3043_);
lean_dec(v___x_3042_);
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v_hypotheses_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v___x_3071_; lean_object* v_caches_3072_; lean_object* v_typeAnalysis_3073_; lean_object* v_target_3074_; uint8_t v_didChange_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3085_; 
v___x_3071_ = lean_st_ref_take(v___y_3060_);
v_caches_3072_ = lean_ctor_get(v___x_3071_, 0);
v_typeAnalysis_3073_ = lean_ctor_get(v___x_3071_, 1);
v_target_3074_ = lean_ctor_get(v___x_3071_, 2);
v_didChange_3075_ = lean_ctor_get_uint8(v___x_3071_, sizeof(void*)*4);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v___x_3071_, 3);
lean_dec(v_unused_3086_);
v___x_3077_ = v___x_3071_;
v_isShared_3078_ = v_isSharedCheck_3085_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_target_3074_);
lean_inc(v_typeAnalysis_3073_);
lean_inc(v_caches_3072_);
lean_dec(v___x_3071_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3085_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3079_ = lean_box(0);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 3, v_hyps_3058_);
v___x_3081_ = v___x_3077_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_caches_3072_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_typeAnalysis_3073_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_target_3074_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_hyps_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*4, v_didChange_3075_);
v___x_3081_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_st_ref_put(v___y_3060_, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3079_);
return v___x_3083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3101_, lean_object* v_hyps_3102_){
_start:
{
lean_object* v___f_3103_; lean_object* v___x_3104_; 
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3103_, 0, v_hyps_3102_);
v___x_3104_ = lean_apply_2(v_inst_3101_, lean_box(0), v___f_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; lean_object* v_caches_3118_; lean_object* v_typeAnalysis_3119_; lean_object* v_target_3120_; uint8_t v_didChange_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3132_; 
v___x_3117_ = lean_st_ref_take(v___y_3106_);
v_caches_3118_ = lean_ctor_get(v___x_3117_, 0);
v_typeAnalysis_3119_ = lean_ctor_get(v___x_3117_, 1);
v_target_3120_ = lean_ctor_get(v___x_3117_, 2);
v_didChange_3121_ = lean_ctor_get_uint8(v___x_3117_, sizeof(void*)*4);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v___x_3117_, 3);
lean_dec(v_unused_3133_);
v___x_3123_ = v___x_3117_;
v_isShared_3124_ = v_isSharedCheck_3132_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_target_3120_);
lean_inc(v_typeAnalysis_3119_);
lean_inc(v_caches_3118_);
lean_dec(v___x_3117_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3132_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3125_ = lean_box(0);
v___x_3126_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 3, v___x_3126_);
v___x_3128_ = v___x_3123_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_caches_3118_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_typeAnalysis_3119_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_target_3120_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v___x_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3131_, sizeof(void*)*4, v_didChange_3121_);
v___x_3128_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_st_ref_put(v___y_3106_, v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3125_);
return v___x_3130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3147_, lean_object* v_cls_3148_, lean_object* v_____do__lift_3149_, lean_object* v_____do__lift_3150_){
_start:
{
uint8_t v_hasTrace_3151_; 
v_hasTrace_3151_ = lean_ctor_get_uint8(v_____do__lift_3150_, sizeof(void*)*1);
if (v_hasTrace_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec(v_cls_3148_);
v___x_3152_ = lean_box(v_hasTrace_3151_);
v___x_3153_ = lean_apply_2(v_toPure_3147_, lean_box(0), v___x_3152_);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3154_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3155_ = l_Lean_Name_append(v___x_3154_, v_cls_3148_);
v___x_3156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3149_, v_____do__lift_3150_, v___x_3155_);
lean_dec(v___x_3155_);
v___x_3157_ = lean_box(v___x_3156_);
v___x_3158_ = lean_apply_2(v_toPure_3147_, lean_box(0), v___x_3157_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3159_, lean_object* v_cls_3160_, lean_object* v_____do__lift_3161_, lean_object* v_____do__lift_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3159_, v_cls_3160_, v_____do__lift_3161_, v_____do__lift_3162_);
lean_dec_ref(v_____do__lift_3162_);
lean_dec_ref(v_____do__lift_3161_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_inst_3164_, lean_object* v_toPure_3165_, lean_object* v_cls_3166_, lean_object* v_toBind_3167_, lean_object* v_____do__lift_3168_){
_start:
{
lean_object* v_getOptionsUnrestricted_3169_; lean_object* v___f_3170_; lean_object* v___x_3171_; 
v_getOptionsUnrestricted_3169_ = lean_ctor_get(v_inst_3164_, 1);
lean_inc(v_getOptionsUnrestricted_3169_);
lean_dec_ref(v_inst_3164_);
v___f_3170_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3170_, 0, v_toPure_3165_);
lean_closure_set(v___f_3170_, 1, v_cls_3166_);
lean_closure_set(v___f_3170_, 2, v_____do__lift_3168_);
v___x_3171_ = lean_apply_4(v_toBind_3167_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3169_, v___f_3170_);
return v___x_3171_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3174_ = l_Lean_stringToMessageData(v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3175_, lean_object* v_a_3176_, lean_object* v___y_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_cls_3182_, uint8_t v_____do__lift_3183_){
_start:
{
if (v_____do__lift_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_dec(v_cls_3182_);
lean_dec(v_inst_3181_);
lean_dec_ref(v_inst_3180_);
lean_dec_ref(v_inst_3179_);
lean_dec_ref(v_inst_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v_a_3176_);
v___x_3184_ = lean_box(0);
v___x_3185_ = lean_apply_2(v_toPure_3175_, lean_box(0), v___x_3184_);
return v___x_3185_;
}
else
{
lean_object* v_type_3186_; lean_object* v_type_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_dec(v_toPure_3175_);
v_type_3186_ = lean_ctor_get(v_a_3176_, 1);
lean_inc_ref(v_type_3186_);
lean_dec_ref(v_a_3176_);
v_type_3187_ = lean_ctor_get(v___y_3177_, 1);
lean_inc_ref(v_type_3187_);
lean_dec_ref(v___y_3177_);
v___x_3188_ = l_Lean_MessageData_ofExpr(v_type_3186_);
v___x_3189_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3188_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = l_Lean_MessageData_ofExpr(v_type_3187_);
v___x_3192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = l_Lean_addTrace___redArg(v_inst_3178_, v_inst_3179_, v_inst_3180_, v_inst_3181_, v_cls_3182_, v___x_3192_);
return v___x_3193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3194_, lean_object* v_a_3195_, lean_object* v___y_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_cls_3201_, lean_object* v_____do__lift_3202_){
_start:
{
uint8_t v_____do__lift_3040__boxed_3203_; lean_object* v_res_3204_; 
v_____do__lift_3040__boxed_3203_ = lean_unbox(v_____do__lift_3202_);
v_res_3204_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3194_, v_a_3195_, v___y_3196_, v_inst_3197_, v_inst_3198_, v_inst_3199_, v_inst_3200_, v_cls_3201_, v_____do__lift_3040__boxed_3203_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3205_, lean_object* v_inst_3206_, lean_object* v_toPure_3207_, lean_object* v_toBind_3208_, lean_object* v_a_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_x_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_getInheritedTraceOptions_3215_; lean_object* v_cls_3216_; lean_object* v___f_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v_getInheritedTraceOptions_3215_ = lean_ctor_get(v_inst_3205_, 2);
lean_inc(v_getInheritedTraceOptions_3215_);
v_cls_3216_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3208_, 2);
lean_inc(v_toPure_3207_);
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3217_, 0, v_inst_3206_);
lean_closure_set(v___f_3217_, 1, v_toPure_3207_);
lean_closure_set(v___f_3217_, 2, v_cls_3216_);
lean_closure_set(v___f_3217_, 3, v_toBind_3208_);
v___f_3218_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3218_, 0, v_toPure_3207_);
lean_closure_set(v___f_3218_, 1, v_a_3209_);
lean_closure_set(v___f_3218_, 2, v___y_3214_);
lean_closure_set(v___f_3218_, 3, v_inst_3210_);
lean_closure_set(v___f_3218_, 4, v_inst_3205_);
lean_closure_set(v___f_3218_, 5, v_inst_3211_);
lean_closure_set(v___f_3218_, 6, v_inst_3212_);
lean_closure_set(v___f_3218_, 7, v_cls_3216_);
v___x_3219_ = lean_apply_4(v_toBind_3208_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3215_, v___f_3217_);
v___x_3220_ = lean_apply_4(v_toBind_3208_, lean_box(0), lean_box(0), v___x_3219_, v___f_3218_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3221_, lean_object* v_res_3222_, lean_object* v_____r_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_apply_2(v_toPure_3221_, lean_box(0), v_res_3222_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3225_, lean_object* v_toBind_3226_, lean_object* v___f_3227_, lean_object* v_____r_3228_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3230_ = lean_apply_2(v_inst_3225_, lean_box(0), v___x_3229_);
v___x_3231_ = lean_apply_4(v_toBind_3226_, lean_box(0), lean_box(0), v___x_3230_, v___f_3227_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3232_, lean_object* v_____r_3233_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_apply_1(v___f_3232_, v_____r_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3235_, lean_object* v_type_3236_, lean_object* v_type_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_inst_3241_, lean_object* v_cls_3242_, lean_object* v_toBind_3243_, lean_object* v___f_3244_, uint8_t v_____do__lift_3245_){
_start:
{
if (v_____do__lift_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_dec(v___f_3244_);
lean_dec(v_toBind_3243_);
lean_dec(v_cls_3242_);
lean_dec(v_inst_3241_);
lean_dec_ref(v_inst_3240_);
lean_dec_ref(v_inst_3239_);
lean_dec_ref(v_inst_3238_);
lean_dec_ref(v_type_3237_);
lean_dec_ref(v_type_3236_);
v___x_3246_ = lean_box(0);
v___x_3247_ = lean_apply_1(v___f_3235_, v___x_3246_);
return v___x_3247_;
}
else
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
lean_dec(v___f_3235_);
v___x_3248_ = l_Lean_MessageData_ofExpr(v_type_3236_);
v___x_3249_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = l_Lean_MessageData_ofExpr(v_type_3237_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_addTrace___redArg(v_inst_3238_, v_inst_3239_, v_inst_3240_, v_inst_3241_, v_cls_3242_, v___x_3252_);
v___x_3254_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3253_, v___f_3244_);
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3255_, lean_object* v_type_3256_, lean_object* v_type_3257_, lean_object* v_inst_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_cls_3262_, lean_object* v_toBind_3263_, lean_object* v___f_3264_, lean_object* v_____do__lift_3265_){
_start:
{
uint8_t v_____do__lift_3140__boxed_3266_; lean_object* v_res_3267_; 
v_____do__lift_3140__boxed_3266_ = lean_unbox(v_____do__lift_3265_);
v_res_3267_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3255_, v_type_3256_, v_type_3257_, v_inst_3258_, v_inst_3259_, v_inst_3260_, v_inst_3261_, v_cls_3262_, v_toBind_3263_, v___f_3264_, v_____do__lift_3140__boxed_3266_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3268_, lean_object* v_inst_3269_, lean_object* v_toBind_3270_, lean_object* v_inst_3271_, lean_object* v___f_3272_, lean_object* v_a_3273_, lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v___f_3278_, lean_object* v_res_3279_){
_start:
{
lean_object* v___x_3280_; lean_object* v_zero_3281_; uint8_t v_isZero_3282_; 
v___x_3280_ = lean_array_get_size(v_res_3279_);
v_zero_3281_ = lean_unsigned_to_nat(0u);
v_isZero_3282_ = lean_nat_dec_eq(v___x_3280_, v_zero_3281_);
if (v_isZero_3282_ == 1)
{
lean_object* v___f_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
lean_dec(v___f_3278_);
lean_dec(v_inst_3277_);
lean_dec_ref(v_inst_3276_);
lean_dec_ref(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec_ref(v_a_3273_);
lean_inc_ref(v_res_3279_);
lean_inc(v_toPure_3268_);
v___f_3283_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3283_, 0, v_toPure_3268_);
lean_closure_set(v___f_3283_, 1, v_res_3279_);
lean_inc(v_toBind_3270_);
v___f_3284_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3284_, 0, v_inst_3269_);
lean_closure_set(v___f_3284_, 1, v_toBind_3270_);
lean_closure_set(v___f_3284_, 2, v___f_3283_);
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_nat_dec_lt(v_zero_3281_, v___x_3280_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_dec_ref(v_res_3279_);
lean_dec(v___f_3272_);
lean_dec_ref(v_inst_3271_);
v___x_3287_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3285_);
v___x_3288_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3287_, v___f_3284_);
return v___x_3288_;
}
else
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_nat_dec_le(v___x_3280_, v___x_3280_);
if (v___x_3289_ == 0)
{
if (v___x_3286_ == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_dec_ref(v_res_3279_);
lean_dec(v___f_3272_);
lean_dec_ref(v_inst_3271_);
v___x_3290_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3285_);
v___x_3291_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3290_, v___f_3284_);
return v___x_3291_;
}
else
{
size_t v___x_3292_; size_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec(v_toPure_3268_);
v___x_3292_ = ((size_t)0ULL);
v___x_3293_ = lean_usize_of_nat(v___x_3280_);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3271_, v___f_3272_, v_res_3279_, v___x_3292_, v___x_3293_, v___x_3285_);
v___x_3295_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3294_, v___f_3284_);
return v___x_3295_;
}
}
else
{
size_t v___x_3296_; size_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v_toPure_3268_);
v___x_3296_ = ((size_t)0ULL);
v___x_3297_ = lean_usize_of_nat(v___x_3280_);
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3271_, v___f_3272_, v_res_3279_, v___x_3296_, v___x_3297_, v___x_3285_);
v___x_3299_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3298_, v___f_3284_);
return v___x_3299_;
}
}
}
else
{
lean_object* v_one_3300_; lean_object* v_n_3301_; uint8_t v_isZero_3302_; 
lean_dec(v___f_3272_);
v_one_3300_ = lean_unsigned_to_nat(1u);
v_n_3301_ = lean_nat_sub(v___x_3280_, v_one_3300_);
v_isZero_3302_ = lean_nat_dec_eq(v_n_3301_, v_zero_3281_);
lean_dec(v_n_3301_);
if (v_isZero_3302_ == 1)
{
lean_object* v_newHyp_3303_; lean_object* v_type_3304_; lean_object* v_type_3305_; uint8_t v___x_3306_; 
lean_dec(v___f_3278_);
v_newHyp_3303_ = lean_array_fget_borrowed(v_res_3279_, v_zero_3281_);
v_type_3304_ = lean_ctor_get(v_newHyp_3303_, 1);
v_type_3305_ = lean_ctor_get(v_a_3273_, 1);
lean_inc_ref(v_type_3305_);
lean_dec_ref(v_a_3273_);
v___x_3306_ = lean_expr_eqv(v_type_3304_, v_type_3305_);
if (v___x_3306_ == 0)
{
lean_object* v_getInheritedTraceOptions_3307_; lean_object* v___f_3308_; lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v_cls_3311_; lean_object* v___f_3312_; lean_object* v___f_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_inc_ref(v_type_3304_);
v_getInheritedTraceOptions_3307_ = lean_ctor_get(v_inst_3274_, 2);
lean_inc(v_getInheritedTraceOptions_3307_);
lean_inc(v_toPure_3268_);
v___f_3308_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3308_, 0, v_toPure_3268_);
lean_closure_set(v___f_3308_, 1, v_res_3279_);
lean_inc_n(v_toBind_3270_, 4);
v___f_3309_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3309_, 0, v_inst_3269_);
lean_closure_set(v___f_3309_, 1, v_toBind_3270_);
lean_closure_set(v___f_3309_, 2, v___f_3308_);
lean_inc_ref(v___f_3309_);
v___f_3310_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3310_, 0, v___f_3309_);
v_cls_3311_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3312_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3312_, 0, v_inst_3275_);
lean_closure_set(v___f_3312_, 1, v_toPure_3268_);
lean_closure_set(v___f_3312_, 2, v_cls_3311_);
lean_closure_set(v___f_3312_, 3, v_toBind_3270_);
v___f_3313_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3313_, 0, v___f_3309_);
lean_closure_set(v___f_3313_, 1, v_type_3305_);
lean_closure_set(v___f_3313_, 2, v_type_3304_);
lean_closure_set(v___f_3313_, 3, v_inst_3271_);
lean_closure_set(v___f_3313_, 4, v_inst_3274_);
lean_closure_set(v___f_3313_, 5, v_inst_3276_);
lean_closure_set(v___f_3313_, 6, v_inst_3277_);
lean_closure_set(v___f_3313_, 7, v_cls_3311_);
lean_closure_set(v___f_3313_, 8, v_toBind_3270_);
lean_closure_set(v___f_3313_, 9, v___f_3310_);
v___x_3314_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3307_, v___f_3312_);
v___x_3315_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3314_, v___f_3313_);
return v___x_3315_;
}
else
{
lean_object* v___x_3316_; 
lean_dec_ref(v_type_3305_);
lean_dec(v_inst_3277_);
lean_dec_ref(v_inst_3276_);
lean_dec_ref(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec_ref(v_inst_3271_);
lean_dec(v_toBind_3270_);
lean_dec(v_inst_3269_);
v___x_3316_ = lean_apply_2(v_toPure_3268_, lean_box(0), v_res_3279_);
return v___x_3316_;
}
}
else
{
lean_object* v___f_3317_; lean_object* v___f_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
lean_dec(v_inst_3277_);
lean_dec_ref(v_inst_3276_);
lean_dec_ref(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec_ref(v_a_3273_);
lean_inc_ref(v_res_3279_);
lean_inc(v_toPure_3268_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3317_, 0, v_toPure_3268_);
lean_closure_set(v___f_3317_, 1, v_res_3279_);
lean_inc(v_toBind_3270_);
v___f_3318_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3318_, 0, v_inst_3269_);
lean_closure_set(v___f_3318_, 1, v_toBind_3270_);
lean_closure_set(v___f_3318_, 2, v___f_3317_);
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_nat_dec_lt(v_zero_3281_, v___x_3280_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
lean_dec_ref(v_res_3279_);
lean_dec(v___f_3278_);
lean_dec_ref(v_inst_3271_);
v___x_3321_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3319_);
v___x_3322_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3321_, v___f_3318_);
return v___x_3322_;
}
else
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_nat_dec_le(v___x_3280_, v___x_3280_);
if (v___x_3323_ == 0)
{
if (v___x_3320_ == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec_ref(v_res_3279_);
lean_dec(v___f_3278_);
lean_dec_ref(v_inst_3271_);
v___x_3324_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3319_);
v___x_3325_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3324_, v___f_3318_);
return v___x_3325_;
}
else
{
size_t v___x_3326_; size_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec(v_toPure_3268_);
v___x_3326_ = ((size_t)0ULL);
v___x_3327_ = lean_usize_of_nat(v___x_3280_);
v___x_3328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3271_, v___f_3278_, v_res_3279_, v___x_3326_, v___x_3327_, v___x_3319_);
v___x_3329_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3328_, v___f_3318_);
return v___x_3329_;
}
}
else
{
size_t v___x_3330_; size_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec(v_toPure_3268_);
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = lean_usize_of_nat(v___x_3280_);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3271_, v___f_3278_, v_res_3279_, v___x_3330_, v___x_3331_, v___x_3319_);
v___x_3333_ = lean_apply_4(v_toBind_3270_, lean_box(0), lean_box(0), v___x_3332_, v___f_3318_);
return v___x_3333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3334_, lean_object* v_toPure_3335_, lean_object* v_____do__lift_3336_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = l_Array_append___redArg(v_bs_3334_, v_____do__lift_3336_);
v___x_3338_ = lean_apply_2(v_toPure_3335_, lean_box(0), v___x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3339_, lean_object* v_toPure_3340_, lean_object* v_____do__lift_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3339_, v_toPure_3340_, v_____do__lift_3341_);
lean_dec_ref(v_____do__lift_3341_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_toPure_3345_, lean_object* v_toBind_3346_, lean_object* v_inst_3347_, lean_object* v_inst_3348_, lean_object* v_inst_3349_, lean_object* v_inst_3350_, lean_object* v_f_3351_, lean_object* v_bs_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v___f_3354_; lean_object* v___f_3355_; lean_object* v___f_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
lean_inc(v_inst_3349_);
lean_inc_ref(v_inst_3348_);
lean_inc_ref(v_inst_3347_);
lean_inc_ref_n(v_a_3353_, 2);
lean_inc_n(v_toBind_3346_, 3);
lean_inc_n(v_toPure_3345_, 2);
lean_inc_ref(v_inst_3344_);
lean_inc_ref(v_inst_3343_);
v___f_3354_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3354_, 0, v_inst_3343_);
lean_closure_set(v___f_3354_, 1, v_inst_3344_);
lean_closure_set(v___f_3354_, 2, v_toPure_3345_);
lean_closure_set(v___f_3354_, 3, v_toBind_3346_);
lean_closure_set(v___f_3354_, 4, v_a_3353_);
lean_closure_set(v___f_3354_, 5, v_inst_3347_);
lean_closure_set(v___f_3354_, 6, v_inst_3348_);
lean_closure_set(v___f_3354_, 7, v_inst_3349_);
lean_inc_ref(v___f_3354_);
v___f_3355_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3355_, 0, v_toPure_3345_);
lean_closure_set(v___f_3355_, 1, v_inst_3350_);
lean_closure_set(v___f_3355_, 2, v_toBind_3346_);
lean_closure_set(v___f_3355_, 3, v_inst_3347_);
lean_closure_set(v___f_3355_, 4, v___f_3354_);
lean_closure_set(v___f_3355_, 5, v_a_3353_);
lean_closure_set(v___f_3355_, 6, v_inst_3343_);
lean_closure_set(v___f_3355_, 7, v_inst_3344_);
lean_closure_set(v___f_3355_, 8, v_inst_3348_);
lean_closure_set(v___f_3355_, 9, v_inst_3349_);
lean_closure_set(v___f_3355_, 10, v___f_3354_);
v___f_3356_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3356_, 0, v_bs_3352_);
lean_closure_set(v___f_3356_, 1, v_toPure_3345_);
v___x_3357_ = lean_apply_1(v_f_3351_, v_a_3353_);
v___x_3358_ = lean_apply_4(v_toBind_3346_, lean_box(0), lean_box(0), v___x_3357_, v___f_3355_);
v___x_3359_ = lean_apply_4(v_toBind_3346_, lean_box(0), lean_box(0), v___x_3358_, v___f_3356_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3362_, lean_object* v_toPure_3363_, lean_object* v_toBind_3364_, lean_object* v___f_3365_, lean_object* v_inst_3366_, lean_object* v___f_3367_, lean_object* v_____r_3368_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3369_ = lean_unsigned_to_nat(0u);
v___x_3370_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3371_ = lean_array_get_size(v_hyps_3362_);
v___x_3372_ = lean_nat_dec_lt(v___x_3369_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec(v___f_3367_);
lean_dec_ref(v_inst_3366_);
lean_dec_ref(v_hyps_3362_);
v___x_3373_ = lean_apply_2(v_toPure_3363_, lean_box(0), v___x_3370_);
v___x_3374_ = lean_apply_4(v_toBind_3364_, lean_box(0), lean_box(0), v___x_3373_, v___f_3365_);
return v___x_3374_;
}
else
{
size_t v___x_3375_; size_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec(v_toPure_3363_);
v___x_3375_ = ((size_t)0ULL);
v___x_3376_ = lean_usize_of_nat(v___x_3371_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3366_, v___f_3367_, v_hyps_3362_, v___x_3375_, v___x_3376_, v___x_3370_);
v___x_3378_ = lean_apply_4(v_toBind_3364_, lean_box(0), lean_box(0), v___x_3377_, v___f_3365_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3379_, lean_object* v_toBind_3380_, lean_object* v___f_3381_, lean_object* v_inst_3382_, lean_object* v___f_3383_, lean_object* v_inst_3384_, lean_object* v___f_3385_, lean_object* v_hyps_3386_){
_start:
{
lean_object* v___f_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_inc(v_toBind_3380_);
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3387_, 0, v_hyps_3386_);
lean_closure_set(v___f_3387_, 1, v_toPure_3379_);
lean_closure_set(v___f_3387_, 2, v_toBind_3380_);
lean_closure_set(v___f_3387_, 3, v___f_3381_);
lean_closure_set(v___f_3387_, 4, v_inst_3382_);
lean_closure_set(v___f_3387_, 5, v___f_3383_);
v___x_3388_ = lean_apply_2(v_inst_3384_, lean_box(0), v___f_3385_);
v___x_3389_ = lean_apply_4(v_toBind_3380_, lean_box(0), lean_box(0), v___x_3388_, v___f_3387_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_inst_3394_, lean_object* v_inst_3395_, lean_object* v_inst_3396_, lean_object* v_f_3397_){
_start:
{
lean_object* v_toApplicative_3398_; lean_object* v_toBind_3399_; lean_object* v_toPure_3400_; lean_object* v___f_3401_; lean_object* v___f_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___f_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; 
v_toApplicative_3398_ = lean_ctor_get(v_inst_3391_, 0);
v_toBind_3399_ = lean_ctor_get(v_inst_3391_, 1);
lean_inc_n(v_toBind_3399_, 3);
v_toPure_3400_ = lean_ctor_get(v_toApplicative_3398_, 1);
lean_inc_n(v_toPure_3400_, 2);
lean_inc_n(v_inst_3396_, 3);
v___f_3401_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3401_, 0, v_inst_3396_);
v___f_3402_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3403_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3404_ = lean_apply_2(v_inst_3396_, lean_box(0), v___x_3403_);
lean_inc_ref(v_inst_3391_);
v___f_3405_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3405_, 0, v_inst_3392_);
lean_closure_set(v___f_3405_, 1, v_inst_3393_);
lean_closure_set(v___f_3405_, 2, v_toPure_3400_);
lean_closure_set(v___f_3405_, 3, v_toBind_3399_);
lean_closure_set(v___f_3405_, 4, v_inst_3391_);
lean_closure_set(v___f_3405_, 5, v_inst_3395_);
lean_closure_set(v___f_3405_, 6, v_inst_3394_);
lean_closure_set(v___f_3405_, 7, v_inst_3396_);
lean_closure_set(v___f_3405_, 8, v_f_3397_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3406_, 0, v_toPure_3400_);
lean_closure_set(v___f_3406_, 1, v_toBind_3399_);
lean_closure_set(v___f_3406_, 2, v___f_3401_);
lean_closure_set(v___f_3406_, 3, v_inst_3391_);
lean_closure_set(v___f_3406_, 4, v___f_3405_);
lean_closure_set(v___f_3406_, 5, v_inst_3396_);
lean_closure_set(v___f_3406_, 6, v___f_3402_);
v___x_3407_ = lean_apply_4(v_toBind_3399_, lean_box(0), lean_box(0), v___x_3404_, v___f_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3408_, lean_object* v_inst_3409_, lean_object* v_inst_3410_, lean_object* v_inst_3411_, lean_object* v_inst_3412_, lean_object* v_inst_3413_, lean_object* v_inst_3414_, lean_object* v_f_3415_){
_start:
{
lean_object* v_toApplicative_3416_; lean_object* v_toBind_3417_; lean_object* v_toPure_3418_; lean_object* v___f_3419_; lean_object* v___f_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___f_3423_; lean_object* v___f_3424_; lean_object* v___x_3425_; 
v_toApplicative_3416_ = lean_ctor_get(v_inst_3409_, 0);
v_toBind_3417_ = lean_ctor_get(v_inst_3409_, 1);
lean_inc_n(v_toBind_3417_, 3);
v_toPure_3418_ = lean_ctor_get(v_toApplicative_3416_, 1);
lean_inc_n(v_toPure_3418_, 2);
lean_inc_n(v_inst_3414_, 3);
v___f_3419_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3419_, 0, v_inst_3414_);
v___f_3420_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3421_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3422_ = lean_apply_2(v_inst_3414_, lean_box(0), v___x_3421_);
lean_inc_ref(v_inst_3409_);
v___f_3423_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3423_, 0, v_inst_3410_);
lean_closure_set(v___f_3423_, 1, v_inst_3411_);
lean_closure_set(v___f_3423_, 2, v_toPure_3418_);
lean_closure_set(v___f_3423_, 3, v_toBind_3417_);
lean_closure_set(v___f_3423_, 4, v_inst_3409_);
lean_closure_set(v___f_3423_, 5, v_inst_3413_);
lean_closure_set(v___f_3423_, 6, v_inst_3412_);
lean_closure_set(v___f_3423_, 7, v_inst_3414_);
lean_closure_set(v___f_3423_, 8, v_f_3415_);
v___f_3424_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3424_, 0, v_toPure_3418_);
lean_closure_set(v___f_3424_, 1, v_toBind_3417_);
lean_closure_set(v___f_3424_, 2, v___f_3419_);
lean_closure_set(v___f_3424_, 3, v_inst_3409_);
lean_closure_set(v___f_3424_, 4, v___f_3423_);
lean_closure_set(v___f_3424_, 5, v_inst_3414_);
lean_closure_set(v___f_3424_, 6, v___f_3420_);
v___x_3425_ = lean_apply_4(v_toBind_3417_, lean_box(0), lean_box(0), v___x_3422_, v___f_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3426_, lean_object* v_____r_3427_){
_start:
{
uint8_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = 0;
v___x_3429_ = lean_box(v___x_3428_);
v___x_3430_ = lean_apply_2(v_toPure_3426_, lean_box(0), v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_snd_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; lean_object* v_caches_3445_; lean_object* v_typeAnalysis_3446_; lean_object* v_target_3447_; uint8_t v_didChange_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3458_; 
v___x_3444_ = lean_st_ref_take(v___y_3433_);
v_caches_3445_ = lean_ctor_get(v___x_3444_, 0);
v_typeAnalysis_3446_ = lean_ctor_get(v___x_3444_, 1);
v_target_3447_ = lean_ctor_get(v___x_3444_, 2);
v_didChange_3448_ = lean_ctor_get_uint8(v___x_3444_, sizeof(void*)*4);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v___x_3444_, 3);
lean_dec(v_unused_3459_);
v___x_3450_ = v___x_3444_;
v_isShared_3451_ = v_isSharedCheck_3458_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_target_3447_);
lean_inc(v_typeAnalysis_3446_);
lean_inc(v_caches_3445_);
lean_dec(v___x_3444_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3458_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3452_ = lean_box(0);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 3, v_snd_3431_);
v___x_3454_ = v___x_3450_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_caches_3445_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_typeAnalysis_3446_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_target_3447_);
lean_ctor_set(v_reuseFailAlloc_3457_, 3, v_snd_3431_);
lean_ctor_set_uint8(v_reuseFailAlloc_3457_, sizeof(void*)*4, v_didChange_3448_);
v___x_3454_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_st_ref_put(v___y_3433_, v___x_3454_);
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3452_);
return v___x_3456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed(lean_object* v_snd_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(v_snd_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_inst_3474_, lean_object* v_toBind_3475_, lean_object* v___f_3476_, lean_object* v_toPure_3477_, lean_object* v_____s_3478_){
_start:
{
lean_object* v_fst_3479_; 
v_fst_3479_ = lean_ctor_get(v_____s_3478_, 0);
if (lean_obj_tag(v_fst_3479_) == 0)
{
lean_object* v_snd_3480_; lean_object* v___f_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec(v_toPure_3477_);
v_snd_3480_ = lean_ctor_get(v_____s_3478_, 1);
lean_inc(v_snd_3480_);
lean_dec_ref(v_____s_3478_);
v___f_3481_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_3481_, 0, v_snd_3480_);
v___x_3482_ = lean_apply_2(v_inst_3474_, lean_box(0), v___f_3481_);
v___x_3483_ = lean_apply_4(v_toBind_3475_, lean_box(0), lean_box(0), v___x_3482_, v___f_3476_);
return v___x_3483_;
}
else
{
lean_object* v_val_3484_; lean_object* v___x_3485_; 
lean_inc_ref(v_fst_3479_);
lean_dec_ref(v_____s_3478_);
lean_dec(v___f_3476_);
lean_dec(v_toBind_3475_);
lean_dec(v_inst_3474_);
v_val_3484_ = lean_ctor_get(v_fst_3479_, 0);
lean_inc(v_val_3484_);
lean_dec_ref_known(v_fst_3479_, 1);
v___x_3485_ = lean_apply_2(v_toPure_3477_, lean_box(0), v_val_3484_);
return v___x_3485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_toPure_3486_, lean_object* v_____do__lift_3487_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_apply_2(v_toPure_3486_, lean_box(0), v_____do__lift_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3489_, lean_object* v_next_3490_, lean_object* v_G_3491_, lean_object* v_____do__lift_3492_){
_start:
{
if (lean_obj_tag(v_____do__lift_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; 
lean_dec(v_G_3491_);
v_a_3493_ = lean_ctor_get(v_____do__lift_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v_____do__lift_3492_, 1);
v___x_3494_ = lean_apply_2(v_toPure_3489_, lean_box(0), v_a_3493_);
return v___x_3494_;
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
lean_dec(v_toPure_3489_);
v_a_3495_ = lean_ctor_get(v_____do__lift_3492_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v_____do__lift_3492_, 1);
v___x_3496_ = lean_unsigned_to_nat(1u);
v___x_3497_ = lean_nat_add(v_next_3490_, v___x_3496_);
v___x_3498_ = lean_apply_4(v_G_3491_, v___x_3497_, v_a_3495_, lean_box(0), lean_box(0));
return v___x_3498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3499_, lean_object* v_next_3500_, lean_object* v_G_3501_, lean_object* v_____do__lift_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3499_, v_next_3500_, v_G_3501_, v_____do__lift_3502_);
lean_dec(v_next_3500_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(uint8_t v___x_3504_, lean_object* v_snd_3505_, lean_object* v_toPure_3506_, lean_object* v_____r_3507_){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3508_ = lean_box(v___x_3504_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
lean_ctor_set(v___x_3510_, 1, v_snd_3505_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
v___x_3512_ = lean_apply_2(v_toPure_3506_, lean_box(0), v___x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed(lean_object* v___x_3513_, lean_object* v_snd_3514_, lean_object* v_toPure_3515_, lean_object* v_____r_3516_){
_start:
{
uint8_t v___x_1675__boxed_3517_; lean_object* v_res_3518_; 
v___x_1675__boxed_3517_ = lean_unbox(v___x_3513_);
v_res_3518_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_1675__boxed_3517_, v_snd_3514_, v_toPure_3515_, v_____r_3516_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_snd_3519_, lean_object* v_newHyp_3520_, lean_object* v___x_3521_, lean_object* v_toPure_3522_, lean_object* v_____r_3523_){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3524_ = lean_array_push(v_snd_3519_, v_newHyp_3520_);
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3521_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
v___x_3527_ = lean_apply_2(v_toPure_3522_, lean_box(0), v___x_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_toPure_3528_, lean_object* v___x_3529_, lean_object* v_____do__lift_3530_, lean_object* v_____do__lift_3531_){
_start:
{
uint8_t v_hasTrace_3532_; 
v_hasTrace_3532_ = lean_ctor_get_uint8(v_____do__lift_3531_, sizeof(void*)*1);
if (v_hasTrace_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec(v___x_3529_);
v___x_3533_ = lean_box(v_hasTrace_3532_);
v___x_3534_ = lean_apply_2(v_toPure_3528_, lean_box(0), v___x_3533_);
return v___x_3534_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3535_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3536_ = l_Lean_Name_append(v___x_3535_, v___x_3529_);
v___x_3537_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3530_, v_____do__lift_3531_, v___x_3536_);
lean_dec(v___x_3536_);
v___x_3538_ = lean_box(v___x_3537_);
v___x_3539_ = lean_apply_2(v_toPure_3528_, lean_box(0), v___x_3538_);
return v___x_3539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed(lean_object* v_toPure_3540_, lean_object* v___x_3541_, lean_object* v_____do__lift_3542_, lean_object* v_____do__lift_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(v_toPure_3540_, v___x_3541_, v_____do__lift_3542_, v_____do__lift_3543_);
lean_dec_ref(v_____do__lift_3543_);
lean_dec_ref(v_____do__lift_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v_inst_3545_, lean_object* v_toPure_3546_, lean_object* v___x_3547_, lean_object* v_toBind_3548_, lean_object* v_____do__lift_3549_){
_start:
{
lean_object* v_getOptionsUnrestricted_3550_; lean_object* v___f_3551_; lean_object* v___x_3552_; 
v_getOptionsUnrestricted_3550_ = lean_ctor_get(v_inst_3545_, 1);
lean_inc(v_getOptionsUnrestricted_3550_);
lean_dec_ref(v_inst_3545_);
v___f_3551_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_3551_, 0, v_toPure_3546_);
lean_closure_set(v___f_3551_, 1, v___x_3547_);
lean_closure_set(v___f_3551_, 2, v_____do__lift_3549_);
v___x_3552_ = lean_apply_4(v_toBind_3548_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3550_, v___f_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object* v___f_3553_, lean_object* v___x_3554_, lean_object* v_type_3555_, lean_object* v_inst_3556_, lean_object* v_inst_3557_, lean_object* v_toMonadRef_3558_, lean_object* v_inst_3559_, lean_object* v___x_3560_, lean_object* v_toBind_3561_, lean_object* v___f_3562_, uint8_t v_____do__lift_3563_){
_start:
{
if (v_____do__lift_3563_ == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec(v___f_3562_);
lean_dec(v_toBind_3561_);
lean_dec(v___x_3560_);
lean_dec(v_inst_3559_);
lean_dec_ref(v_toMonadRef_3558_);
lean_dec_ref(v_inst_3557_);
lean_dec_ref(v_inst_3556_);
lean_dec_ref(v_type_3555_);
lean_dec_ref(v___x_3554_);
v___x_3564_ = lean_box(0);
v___x_3565_ = lean_apply_1(v___f_3553_, v___x_3564_);
return v___x_3565_;
}
else
{
lean_object* v_type_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v___f_3553_);
v_type_3566_ = lean_ctor_get(v___x_3554_, 1);
lean_inc_ref(v_type_3566_);
lean_dec_ref(v___x_3554_);
v___x_3567_ = l_Lean_MessageData_ofExpr(v_type_3566_);
v___x_3568_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = l_Lean_MessageData_ofExpr(v_type_3555_);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3569_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = l_Lean_addTrace___redArg(v_inst_3556_, v_inst_3557_, v_toMonadRef_3558_, v_inst_3559_, v___x_3560_, v___x_3571_);
v___x_3573_ = lean_apply_4(v_toBind_3561_, lean_box(0), lean_box(0), v___x_3572_, v___f_3562_);
return v___x_3573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___f_3574_, lean_object* v___x_3575_, lean_object* v_type_3576_, lean_object* v_inst_3577_, lean_object* v_inst_3578_, lean_object* v_toMonadRef_3579_, lean_object* v_inst_3580_, lean_object* v___x_3581_, lean_object* v_toBind_3582_, lean_object* v___f_3583_, lean_object* v_____do__lift_3584_){
_start:
{
uint8_t v_____do__lift_1750__boxed_3585_; lean_object* v_res_3586_; 
v_____do__lift_1750__boxed_3585_ = lean_unbox(v_____do__lift_3584_);
v_res_3586_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3574_, v___x_3575_, v_type_3576_, v_inst_3577_, v_inst_3578_, v_toMonadRef_3579_, v_inst_3580_, v___x_3581_, v_toBind_3582_, v___f_3583_, v_____do__lift_1750__boxed_3585_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v___x_3587_, lean_object* v_snd_3588_, lean_object* v___x_3589_, lean_object* v_toPure_3590_, lean_object* v_inst_3591_, lean_object* v_toBind_3592_, lean_object* v_inst_3593_, lean_object* v_inst_3594_, lean_object* v_inst_3595_, lean_object* v_toMonadRef_3596_, lean_object* v_inst_3597_, lean_object* v___f_3598_, lean_object* v_newHyp_3599_){
_start:
{
lean_object* v_type_3600_; lean_object* v_value_3601_; uint8_t v___x_3602_; 
v_type_3600_ = lean_ctor_get(v_newHyp_3599_, 1);
v_value_3601_ = lean_ctor_get(v_newHyp_3599_, 2);
lean_inc_ref(v_type_3600_);
v___x_3602_ = l_Lean_Expr_isFalse(v_type_3600_);
if (v___x_3602_ == 0)
{
lean_object* v_type_3603_; lean_object* v___f_3604_; lean_object* v___f_3605_; lean_object* v___f_3606_; lean_object* v___f_3607_; uint8_t v___x_3615_; 
lean_dec(v___f_3598_);
v_type_3603_ = lean_ctor_get(v___x_3587_, 1);
lean_inc(v_toPure_3590_);
lean_inc(v___x_3589_);
lean_inc_ref(v_newHyp_3599_);
lean_inc(v_snd_3588_);
v___f_3604_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3604_, 0, v_snd_3588_);
lean_closure_set(v___f_3604_, 1, v_newHyp_3599_);
lean_closure_set(v___f_3604_, 2, v___x_3589_);
lean_closure_set(v___f_3604_, 3, v_toPure_3590_);
v___f_3605_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3605_, 0, v___f_3604_);
lean_inc(v_toBind_3592_);
v___f_3606_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3606_, 0, v_inst_3591_);
lean_closure_set(v___f_3606_, 1, v_toBind_3592_);
lean_closure_set(v___f_3606_, 2, v___f_3605_);
lean_inc_ref(v___f_3606_);
v___f_3607_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3607_, 0, v___f_3606_);
v___x_3615_ = lean_expr_eqv(v_type_3603_, v_type_3600_);
if (v___x_3615_ == 0)
{
lean_inc_ref(v_type_3600_);
lean_dec_ref(v_newHyp_3599_);
lean_dec(v___x_3589_);
lean_dec(v_snd_3588_);
goto v___jp_3608_;
}
else
{
if (v___x_3602_ == 0)
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
lean_dec_ref(v___f_3607_);
lean_dec_ref(v___f_3606_);
lean_dec(v_inst_3597_);
lean_dec_ref(v_toMonadRef_3596_);
lean_dec_ref(v_inst_3595_);
lean_dec_ref(v_inst_3594_);
lean_dec_ref(v_inst_3593_);
lean_dec(v_toBind_3592_);
lean_dec_ref(v___x_3587_);
v___x_3616_ = lean_box(0);
v___x_3617_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3588_, v_newHyp_3599_, v___x_3589_, v_toPure_3590_, v___x_3616_);
return v___x_3617_;
}
else
{
lean_inc_ref(v_type_3600_);
lean_dec_ref(v_newHyp_3599_);
lean_dec(v___x_3589_);
lean_dec(v_snd_3588_);
goto v___jp_3608_;
}
}
v___jp_3608_:
{
lean_object* v_getInheritedTraceOptions_3609_; lean_object* v___x_3610_; lean_object* v___f_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_getInheritedTraceOptions_3609_ = lean_ctor_get(v_inst_3593_, 2);
lean_inc(v_getInheritedTraceOptions_3609_);
v___x_3610_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3592_, 3);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3611_, 0, v_inst_3594_);
lean_closure_set(v___f_3611_, 1, v_toPure_3590_);
lean_closure_set(v___f_3611_, 2, v___x_3610_);
lean_closure_set(v___f_3611_, 3, v_toBind_3592_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3612_, 0, v___f_3606_);
lean_closure_set(v___f_3612_, 1, v___x_3587_);
lean_closure_set(v___f_3612_, 2, v_type_3600_);
lean_closure_set(v___f_3612_, 3, v_inst_3595_);
lean_closure_set(v___f_3612_, 4, v_inst_3593_);
lean_closure_set(v___f_3612_, 5, v_toMonadRef_3596_);
lean_closure_set(v___f_3612_, 6, v_inst_3597_);
lean_closure_set(v___f_3612_, 7, v___x_3610_);
lean_closure_set(v___f_3612_, 8, v_toBind_3592_);
lean_closure_set(v___f_3612_, 9, v___f_3607_);
v___x_3613_ = lean_apply_4(v_toBind_3592_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3609_, v___f_3611_);
v___x_3614_ = lean_apply_4(v_toBind_3592_, lean_box(0), lean_box(0), v___x_3613_, v___f_3612_);
return v___x_3614_;
}
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
lean_inc_ref(v_value_3601_);
lean_dec_ref(v_newHyp_3599_);
lean_dec(v_inst_3597_);
lean_dec_ref(v_toMonadRef_3596_);
lean_dec_ref(v_inst_3595_);
lean_dec_ref(v_inst_3594_);
lean_dec_ref(v_inst_3593_);
lean_dec(v_toPure_3590_);
lean_dec(v___x_3589_);
lean_dec(v_snd_3588_);
lean_dec_ref(v___x_3587_);
v___x_3618_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3618_, 0, v_value_3601_);
v___x_3619_ = lean_apply_2(v_inst_3591_, lean_box(0), v___x_3618_);
v___x_3620_ = lean_apply_4(v_toBind_3592_, lean_box(0), lean_box(0), v___x_3619_, v___f_3598_);
return v___x_3620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3621_, lean_object* v_toPure_3622_, lean_object* v_hyps_3623_, lean_object* v___x_3624_, lean_object* v_inst_3625_, lean_object* v_toBind_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_toMonadRef_3630_, lean_object* v_inst_3631_, lean_object* v_f_3632_, lean_object* v___f_3633_, lean_object* v_next_3634_, lean_object* v_acc_3635_, lean_object* v_h_3636_, lean_object* v_G_3637_){
_start:
{
uint8_t v___x_3638_; 
v___x_3638_ = lean_nat_dec_lt(v_next_3634_, v___x_3621_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; 
lean_dec(v_G_3637_);
lean_dec(v_next_3634_);
lean_dec(v___f_3633_);
lean_dec(v_f_3632_);
lean_dec(v_inst_3631_);
lean_dec_ref(v_toMonadRef_3630_);
lean_dec_ref(v_inst_3629_);
lean_dec_ref(v_inst_3628_);
lean_dec_ref(v_inst_3627_);
lean_dec(v_toBind_3626_);
lean_dec(v_inst_3625_);
lean_dec(v___x_3624_);
v___x_3639_ = lean_apply_2(v_toPure_3622_, lean_box(0), v_acc_3635_);
return v___x_3639_;
}
else
{
lean_object* v_snd_3640_; lean_object* v___f_3641_; lean_object* v___x_3642_; lean_object* v___f_3643_; lean_object* v___x_3644_; lean_object* v___f_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v_snd_3640_ = lean_ctor_get(v_acc_3635_, 1);
lean_inc_n(v_snd_3640_, 2);
lean_dec_ref(v_acc_3635_);
lean_inc(v_next_3634_);
lean_inc_n(v_toPure_3622_, 2);
v___f_3641_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3641_, 0, v_toPure_3622_);
lean_closure_set(v___f_3641_, 1, v_next_3634_);
lean_closure_set(v___f_3641_, 2, v_G_3637_);
v___x_3642_ = lean_box(v___x_3638_);
v___f_3643_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3643_, 0, v___x_3642_);
lean_closure_set(v___f_3643_, 1, v_snd_3640_);
lean_closure_set(v___f_3643_, 2, v_toPure_3622_);
v___x_3644_ = lean_array_fget_borrowed(v_hyps_3623_, v_next_3634_);
lean_inc_n(v_toBind_3626_, 3);
lean_inc_n(v___x_3644_, 2);
v___f_3645_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9), 13, 12);
lean_closure_set(v___f_3645_, 0, v___x_3644_);
lean_closure_set(v___f_3645_, 1, v_snd_3640_);
lean_closure_set(v___f_3645_, 2, v___x_3624_);
lean_closure_set(v___f_3645_, 3, v_toPure_3622_);
lean_closure_set(v___f_3645_, 4, v_inst_3625_);
lean_closure_set(v___f_3645_, 5, v_toBind_3626_);
lean_closure_set(v___f_3645_, 6, v_inst_3627_);
lean_closure_set(v___f_3645_, 7, v_inst_3628_);
lean_closure_set(v___f_3645_, 8, v_inst_3629_);
lean_closure_set(v___f_3645_, 9, v_toMonadRef_3630_);
lean_closure_set(v___f_3645_, 10, v_inst_3631_);
lean_closure_set(v___f_3645_, 11, v___f_3643_);
v___x_3646_ = lean_apply_2(v_f_3632_, v_next_3634_, v___x_3644_);
v___x_3647_ = lean_apply_4(v_toBind_3626_, lean_box(0), lean_box(0), v___x_3646_, v___f_3645_);
v___x_3648_ = lean_apply_4(v_toBind_3626_, lean_box(0), lean_box(0), v___x_3647_, v___f_3633_);
v___x_3649_ = lean_apply_4(v_toBind_3626_, lean_box(0), lean_box(0), v___x_3648_, v___f_3641_);
return v___x_3649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3650_ = _args[0];
lean_object* v_toPure_3651_ = _args[1];
lean_object* v_hyps_3652_ = _args[2];
lean_object* v___x_3653_ = _args[3];
lean_object* v_inst_3654_ = _args[4];
lean_object* v_toBind_3655_ = _args[5];
lean_object* v_inst_3656_ = _args[6];
lean_object* v_inst_3657_ = _args[7];
lean_object* v_inst_3658_ = _args[8];
lean_object* v_toMonadRef_3659_ = _args[9];
lean_object* v_inst_3660_ = _args[10];
lean_object* v_f_3661_ = _args[11];
lean_object* v___f_3662_ = _args[12];
lean_object* v_next_3663_ = _args[13];
lean_object* v_acc_3664_ = _args[14];
lean_object* v_h_3665_ = _args[15];
lean_object* v_G_3666_ = _args[16];
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3650_, v_toPure_3651_, v_hyps_3652_, v___x_3653_, v_inst_3654_, v_toBind_3655_, v_inst_3656_, v_inst_3657_, v_inst_3658_, v_toMonadRef_3659_, v_inst_3660_, v_f_3661_, v___f_3662_, v_next_3663_, v_acc_3664_, v_h_3665_, v_G_3666_);
lean_dec_ref(v_hyps_3652_);
lean_dec(v___x_3650_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3668_, lean_object* v_inst_3669_, lean_object* v_toBind_3670_, lean_object* v_inst_3671_, lean_object* v_inst_3672_, lean_object* v_inst_3673_, lean_object* v_toMonadRef_3674_, lean_object* v_inst_3675_, lean_object* v_f_3676_, lean_object* v___f_3677_, lean_object* v___f_3678_, lean_object* v_hyps_3679_){
_start:
{
lean_object* v___x_3680_; lean_object* v_newHyps_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___f_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3680_ = lean_array_get_size(v_hyps_3679_);
v_newHyps_3681_ = lean_mk_empty_array_with_capacity(v___x_3680_);
v___x_3682_ = lean_unsigned_to_nat(0u);
v___x_3683_ = lean_box(0);
lean_inc(v_toBind_3670_);
v___f_3684_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3684_, 0, v___x_3680_);
lean_closure_set(v___f_3684_, 1, v_toPure_3668_);
lean_closure_set(v___f_3684_, 2, v_hyps_3679_);
lean_closure_set(v___f_3684_, 3, v___x_3683_);
lean_closure_set(v___f_3684_, 4, v_inst_3669_);
lean_closure_set(v___f_3684_, 5, v_toBind_3670_);
lean_closure_set(v___f_3684_, 6, v_inst_3671_);
lean_closure_set(v___f_3684_, 7, v_inst_3672_);
lean_closure_set(v___f_3684_, 8, v_inst_3673_);
lean_closure_set(v___f_3684_, 9, v_toMonadRef_3674_);
lean_closure_set(v___f_3684_, 10, v_inst_3675_);
lean_closure_set(v___f_3684_, 11, v_f_3676_);
lean_closure_set(v___f_3684_, 12, v___f_3677_);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v_newHyps_3681_);
v___x_3686_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3684_, v___x_3682_, v___x_3685_, lean_box(0));
v___x_3687_ = lean_apply_4(v_toBind_3670_, lean_box(0), lean_box(0), v___x_3686_, v___f_3678_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3688_, lean_object* v_inst_3689_, lean_object* v_inst_3690_, lean_object* v_inst_3691_, lean_object* v_inst_3692_, lean_object* v_inst_3693_, lean_object* v_f_3694_){
_start:
{
lean_object* v_toApplicative_3695_; lean_object* v_toBind_3696_; lean_object* v_toPure_3697_; lean_object* v_toMonadRef_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___f_3703_; lean_object* v___f_3704_; lean_object* v___x_3705_; 
v_toApplicative_3695_ = lean_ctor_get(v_inst_3688_, 0);
v_toBind_3696_ = lean_ctor_get(v_inst_3688_, 1);
lean_inc_n(v_toBind_3696_, 3);
v_toPure_3697_ = lean_ctor_get(v_toApplicative_3695_, 1);
lean_inc_n(v_toPure_3697_, 4);
v_toMonadRef_3698_ = lean_ctor_get(v_inst_3690_, 1);
lean_inc_ref(v_toMonadRef_3698_);
lean_dec_ref(v_inst_3690_);
v___x_3699_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3689_, 2);
v___x_3700_ = lean_apply_2(v_inst_3689_, lean_box(0), v___x_3699_);
v___f_3701_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3701_, 0, v_toPure_3697_);
v___f_3702_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3702_, 0, v_inst_3689_);
lean_closure_set(v___f_3702_, 1, v_toBind_3696_);
lean_closure_set(v___f_3702_, 2, v___f_3701_);
lean_closure_set(v___f_3702_, 3, v_toPure_3697_);
v___f_3703_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3703_, 0, v_toPure_3697_);
v___f_3704_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3704_, 0, v_toPure_3697_);
lean_closure_set(v___f_3704_, 1, v_inst_3689_);
lean_closure_set(v___f_3704_, 2, v_toBind_3696_);
lean_closure_set(v___f_3704_, 3, v_inst_3691_);
lean_closure_set(v___f_3704_, 4, v_inst_3692_);
lean_closure_set(v___f_3704_, 5, v_inst_3688_);
lean_closure_set(v___f_3704_, 6, v_toMonadRef_3698_);
lean_closure_set(v___f_3704_, 7, v_inst_3693_);
lean_closure_set(v___f_3704_, 8, v_f_3694_);
lean_closure_set(v___f_3704_, 9, v___f_3703_);
lean_closure_set(v___f_3704_, 10, v___f_3702_);
v___x_3705_ = lean_apply_4(v_toBind_3696_, lean_box(0), lean_box(0), v___x_3700_, v___f_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3706_, lean_object* v_inst_3707_, lean_object* v_inst_3708_, lean_object* v_inst_3709_, lean_object* v_inst_3710_, lean_object* v_inst_3711_, lean_object* v_inst_3712_, lean_object* v_inst_3713_, lean_object* v_inst_3714_, lean_object* v_f_3715_){
_start:
{
lean_object* v_toApplicative_3716_; lean_object* v_toBind_3717_; lean_object* v_toPure_3718_; lean_object* v_toMonadRef_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___f_3722_; lean_object* v___f_3723_; lean_object* v___f_3724_; lean_object* v___f_3725_; lean_object* v___x_3726_; 
v_toApplicative_3716_ = lean_ctor_get(v_inst_3707_, 0);
v_toBind_3717_ = lean_ctor_get(v_inst_3707_, 1);
lean_inc_n(v_toBind_3717_, 3);
v_toPure_3718_ = lean_ctor_get(v_toApplicative_3716_, 1);
lean_inc_n(v_toPure_3718_, 4);
v_toMonadRef_3719_ = lean_ctor_get(v_inst_3709_, 1);
lean_inc_ref(v_toMonadRef_3719_);
lean_dec_ref(v_inst_3709_);
v___x_3720_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3708_, 2);
v___x_3721_ = lean_apply_2(v_inst_3708_, lean_box(0), v___x_3720_);
v___f_3722_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3722_, 0, v_toPure_3718_);
v___f_3723_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3723_, 0, v_inst_3708_);
lean_closure_set(v___f_3723_, 1, v_toBind_3717_);
lean_closure_set(v___f_3723_, 2, v___f_3722_);
lean_closure_set(v___f_3723_, 3, v_toPure_3718_);
v___f_3724_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3724_, 0, v_toPure_3718_);
v___f_3725_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3725_, 0, v_toPure_3718_);
lean_closure_set(v___f_3725_, 1, v_inst_3708_);
lean_closure_set(v___f_3725_, 2, v_toBind_3717_);
lean_closure_set(v___f_3725_, 3, v_inst_3711_);
lean_closure_set(v___f_3725_, 4, v_inst_3712_);
lean_closure_set(v___f_3725_, 5, v_inst_3707_);
lean_closure_set(v___f_3725_, 6, v_toMonadRef_3719_);
lean_closure_set(v___f_3725_, 7, v_inst_3713_);
lean_closure_set(v___f_3725_, 8, v_f_3715_);
lean_closure_set(v___f_3725_, 9, v___f_3724_);
lean_closure_set(v___f_3725_, 10, v___f_3723_);
v___x_3726_ = lean_apply_4(v_toBind_3717_, lean_box(0), lean_box(0), v___x_3721_, v___f_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3727_, lean_object* v_inst_3728_, lean_object* v_inst_3729_, lean_object* v_inst_3730_, lean_object* v_inst_3731_, lean_object* v_inst_3732_, lean_object* v_inst_3733_, lean_object* v_inst_3734_, lean_object* v_inst_3735_, lean_object* v_f_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3727_, v_inst_3728_, v_inst_3729_, v_inst_3730_, v_inst_3731_, v_inst_3732_, v_inst_3733_, v_inst_3734_, v_inst_3735_, v_f_3736_);
lean_dec_ref(v_inst_3735_);
lean_dec_ref(v_inst_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3738_, lean_object* v_snd_3739_, lean_object* v___x_3740_, lean_object* v_toPure_3741_, lean_object* v_inst_3742_, lean_object* v_toBind_3743_, lean_object* v_inst_3744_, lean_object* v_inst_3745_, lean_object* v_toMonadRef_3746_, lean_object* v_inst_3747_, lean_object* v_inst_3748_, lean_object* v___f_3749_, lean_object* v_newHyp_3750_){
_start:
{
lean_object* v_type_3751_; lean_object* v_value_3752_; uint8_t v___x_3753_; 
v_type_3751_ = lean_ctor_get(v_newHyp_3750_, 1);
v_value_3752_ = lean_ctor_get(v_newHyp_3750_, 2);
lean_inc_ref(v_type_3751_);
v___x_3753_ = l_Lean_Expr_isFalse(v_type_3751_);
if (v___x_3753_ == 0)
{
lean_object* v_type_3754_; lean_object* v___f_3755_; lean_object* v___f_3756_; lean_object* v___f_3757_; lean_object* v___f_3758_; uint8_t v___x_3766_; 
lean_dec(v___f_3749_);
v_type_3754_ = lean_ctor_get(v___x_3738_, 1);
lean_inc(v_toPure_3741_);
lean_inc(v___x_3740_);
lean_inc_ref(v_newHyp_3750_);
lean_inc(v_snd_3739_);
v___f_3755_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3755_, 0, v_snd_3739_);
lean_closure_set(v___f_3755_, 1, v_newHyp_3750_);
lean_closure_set(v___f_3755_, 2, v___x_3740_);
lean_closure_set(v___f_3755_, 3, v_toPure_3741_);
v___f_3756_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3756_, 0, v___f_3755_);
lean_inc(v_toBind_3743_);
v___f_3757_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3757_, 0, v_inst_3742_);
lean_closure_set(v___f_3757_, 1, v_toBind_3743_);
lean_closure_set(v___f_3757_, 2, v___f_3756_);
lean_inc_ref(v___f_3757_);
v___f_3758_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3758_, 0, v___f_3757_);
v___x_3766_ = lean_expr_eqv(v_type_3754_, v_type_3751_);
if (v___x_3766_ == 0)
{
lean_inc_ref(v_type_3751_);
lean_dec_ref(v_newHyp_3750_);
lean_dec(v___x_3740_);
lean_dec(v_snd_3739_);
goto v___jp_3759_;
}
else
{
if (v___x_3753_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_dec_ref(v___f_3758_);
lean_dec_ref(v___f_3757_);
lean_dec_ref(v_inst_3748_);
lean_dec(v_inst_3747_);
lean_dec_ref(v_toMonadRef_3746_);
lean_dec_ref(v_inst_3745_);
lean_dec_ref(v_inst_3744_);
lean_dec(v_toBind_3743_);
lean_dec_ref(v___x_3738_);
v___x_3767_ = lean_box(0);
v___x_3768_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3739_, v_newHyp_3750_, v___x_3740_, v_toPure_3741_, v___x_3767_);
return v___x_3768_;
}
else
{
lean_inc_ref(v_type_3751_);
lean_dec_ref(v_newHyp_3750_);
lean_dec(v___x_3740_);
lean_dec(v_snd_3739_);
goto v___jp_3759_;
}
}
v___jp_3759_:
{
lean_object* v_getInheritedTraceOptions_3760_; lean_object* v___x_3761_; lean_object* v___f_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v_getInheritedTraceOptions_3760_ = lean_ctor_get(v_inst_3744_, 2);
lean_inc(v_getInheritedTraceOptions_3760_);
v___x_3761_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3743_, 3);
v___f_3762_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3762_, 0, v___f_3757_);
lean_closure_set(v___f_3762_, 1, v___x_3738_);
lean_closure_set(v___f_3762_, 2, v_type_3751_);
lean_closure_set(v___f_3762_, 3, v_inst_3745_);
lean_closure_set(v___f_3762_, 4, v_inst_3744_);
lean_closure_set(v___f_3762_, 5, v_toMonadRef_3746_);
lean_closure_set(v___f_3762_, 6, v_inst_3747_);
lean_closure_set(v___f_3762_, 7, v___x_3761_);
lean_closure_set(v___f_3762_, 8, v_toBind_3743_);
lean_closure_set(v___f_3762_, 9, v___f_3758_);
v___f_3763_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3763_, 0, v_inst_3748_);
lean_closure_set(v___f_3763_, 1, v_toPure_3741_);
lean_closure_set(v___f_3763_, 2, v___x_3761_);
lean_closure_set(v___f_3763_, 3, v_toBind_3743_);
v___x_3764_ = lean_apply_4(v_toBind_3743_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3760_, v___f_3763_);
v___x_3765_ = lean_apply_4(v_toBind_3743_, lean_box(0), lean_box(0), v___x_3764_, v___f_3762_);
return v___x_3765_;
}
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
lean_inc_ref(v_value_3752_);
lean_dec_ref(v_newHyp_3750_);
lean_dec_ref(v_inst_3748_);
lean_dec(v_inst_3747_);
lean_dec_ref(v_toMonadRef_3746_);
lean_dec_ref(v_inst_3745_);
lean_dec_ref(v_inst_3744_);
lean_dec(v_toPure_3741_);
lean_dec(v___x_3740_);
lean_dec(v_snd_3739_);
lean_dec_ref(v___x_3738_);
v___x_3769_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3769_, 0, v_value_3752_);
v___x_3770_ = lean_apply_2(v_inst_3742_, lean_box(0), v___x_3769_);
v___x_3771_ = lean_apply_4(v_toBind_3743_, lean_box(0), lean_box(0), v___x_3770_, v___f_3749_);
return v___x_3771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3772_, lean_object* v_toPure_3773_, lean_object* v_hyps_3774_, lean_object* v___x_3775_, lean_object* v_inst_3776_, lean_object* v_toBind_3777_, lean_object* v_inst_3778_, lean_object* v_inst_3779_, lean_object* v_toMonadRef_3780_, lean_object* v_inst_3781_, lean_object* v_inst_3782_, lean_object* v_f_3783_, lean_object* v___f_3784_, lean_object* v_next_3785_, lean_object* v_acc_3786_, lean_object* v_h_3787_, lean_object* v_G_3788_){
_start:
{
uint8_t v___x_3789_; 
v___x_3789_ = lean_nat_dec_lt(v_next_3785_, v___x_3772_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; 
lean_dec(v_G_3788_);
lean_dec(v_next_3785_);
lean_dec(v___f_3784_);
lean_dec(v_f_3783_);
lean_dec_ref(v_inst_3782_);
lean_dec(v_inst_3781_);
lean_dec_ref(v_toMonadRef_3780_);
lean_dec_ref(v_inst_3779_);
lean_dec_ref(v_inst_3778_);
lean_dec(v_toBind_3777_);
lean_dec(v_inst_3776_);
lean_dec(v___x_3775_);
v___x_3790_ = lean_apply_2(v_toPure_3773_, lean_box(0), v_acc_3786_);
return v___x_3790_;
}
else
{
lean_object* v_snd_3791_; lean_object* v___f_3792_; lean_object* v___x_3793_; lean_object* v___f_3794_; lean_object* v___x_3795_; lean_object* v___f_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_snd_3791_ = lean_ctor_get(v_acc_3786_, 1);
lean_inc_n(v_snd_3791_, 2);
lean_dec_ref(v_acc_3786_);
lean_inc(v_next_3785_);
lean_inc_n(v_toPure_3773_, 2);
v___f_3792_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3792_, 0, v_toPure_3773_);
lean_closure_set(v___f_3792_, 1, v_next_3785_);
lean_closure_set(v___f_3792_, 2, v_G_3788_);
v___x_3793_ = lean_box(v___x_3789_);
v___f_3794_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3794_, 0, v___x_3793_);
lean_closure_set(v___f_3794_, 1, v_snd_3791_);
lean_closure_set(v___f_3794_, 2, v_toPure_3773_);
v___x_3795_ = lean_array_fget_borrowed(v_hyps_3774_, v_next_3785_);
lean_dec(v_next_3785_);
lean_inc_n(v_toBind_3777_, 3);
lean_inc_n(v___x_3795_, 2);
v___f_3796_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3796_, 0, v___x_3795_);
lean_closure_set(v___f_3796_, 1, v_snd_3791_);
lean_closure_set(v___f_3796_, 2, v___x_3775_);
lean_closure_set(v___f_3796_, 3, v_toPure_3773_);
lean_closure_set(v___f_3796_, 4, v_inst_3776_);
lean_closure_set(v___f_3796_, 5, v_toBind_3777_);
lean_closure_set(v___f_3796_, 6, v_inst_3778_);
lean_closure_set(v___f_3796_, 7, v_inst_3779_);
lean_closure_set(v___f_3796_, 8, v_toMonadRef_3780_);
lean_closure_set(v___f_3796_, 9, v_inst_3781_);
lean_closure_set(v___f_3796_, 10, v_inst_3782_);
lean_closure_set(v___f_3796_, 11, v___f_3794_);
v___x_3797_ = lean_apply_1(v_f_3783_, v___x_3795_);
v___x_3798_ = lean_apply_4(v_toBind_3777_, lean_box(0), lean_box(0), v___x_3797_, v___f_3796_);
v___x_3799_ = lean_apply_4(v_toBind_3777_, lean_box(0), lean_box(0), v___x_3798_, v___f_3784_);
v___x_3800_ = lean_apply_4(v_toBind_3777_, lean_box(0), lean_box(0), v___x_3799_, v___f_3792_);
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3801_ = _args[0];
lean_object* v_toPure_3802_ = _args[1];
lean_object* v_hyps_3803_ = _args[2];
lean_object* v___x_3804_ = _args[3];
lean_object* v_inst_3805_ = _args[4];
lean_object* v_toBind_3806_ = _args[5];
lean_object* v_inst_3807_ = _args[6];
lean_object* v_inst_3808_ = _args[7];
lean_object* v_toMonadRef_3809_ = _args[8];
lean_object* v_inst_3810_ = _args[9];
lean_object* v_inst_3811_ = _args[10];
lean_object* v_f_3812_ = _args[11];
lean_object* v___f_3813_ = _args[12];
lean_object* v_next_3814_ = _args[13];
lean_object* v_acc_3815_ = _args[14];
lean_object* v_h_3816_ = _args[15];
lean_object* v_G_3817_ = _args[16];
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3801_, v_toPure_3802_, v_hyps_3803_, v___x_3804_, v_inst_3805_, v_toBind_3806_, v_inst_3807_, v_inst_3808_, v_toMonadRef_3809_, v_inst_3810_, v_inst_3811_, v_f_3812_, v___f_3813_, v_next_3814_, v_acc_3815_, v_h_3816_, v_G_3817_);
lean_dec_ref(v_hyps_3803_);
lean_dec(v___x_3801_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3819_, lean_object* v_inst_3820_, lean_object* v_toBind_3821_, lean_object* v_inst_3822_, lean_object* v_inst_3823_, lean_object* v_toMonadRef_3824_, lean_object* v_inst_3825_, lean_object* v_inst_3826_, lean_object* v_f_3827_, lean_object* v___f_3828_, lean_object* v___f_3829_, lean_object* v_hyps_3830_){
_start:
{
lean_object* v___x_3831_; lean_object* v_newHyps_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___f_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3831_ = lean_array_get_size(v_hyps_3830_);
v_newHyps_3832_ = lean_mk_empty_array_with_capacity(v___x_3831_);
v___x_3833_ = lean_unsigned_to_nat(0u);
v___x_3834_ = lean_box(0);
lean_inc(v_toBind_3821_);
v___f_3835_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3835_, 0, v___x_3831_);
lean_closure_set(v___f_3835_, 1, v_toPure_3819_);
lean_closure_set(v___f_3835_, 2, v_hyps_3830_);
lean_closure_set(v___f_3835_, 3, v___x_3834_);
lean_closure_set(v___f_3835_, 4, v_inst_3820_);
lean_closure_set(v___f_3835_, 5, v_toBind_3821_);
lean_closure_set(v___f_3835_, 6, v_inst_3822_);
lean_closure_set(v___f_3835_, 7, v_inst_3823_);
lean_closure_set(v___f_3835_, 8, v_toMonadRef_3824_);
lean_closure_set(v___f_3835_, 9, v_inst_3825_);
lean_closure_set(v___f_3835_, 10, v_inst_3826_);
lean_closure_set(v___f_3835_, 11, v_f_3827_);
lean_closure_set(v___f_3835_, 12, v___f_3828_);
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3834_);
lean_ctor_set(v___x_3836_, 1, v_newHyps_3832_);
v___x_3837_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3835_, v___x_3833_, v___x_3836_, lean_box(0));
v___x_3838_ = lean_apply_4(v_toBind_3821_, lean_box(0), lean_box(0), v___x_3837_, v___f_3829_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3839_, lean_object* v_inst_3840_, lean_object* v_inst_3841_, lean_object* v_inst_3842_, lean_object* v_inst_3843_, lean_object* v_inst_3844_, lean_object* v_f_3845_){
_start:
{
lean_object* v_toApplicative_3846_; lean_object* v_toBind_3847_; lean_object* v_toPure_3848_; lean_object* v_toMonadRef_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___f_3852_; lean_object* v___f_3853_; lean_object* v___f_3854_; lean_object* v___f_3855_; lean_object* v___x_3856_; 
v_toApplicative_3846_ = lean_ctor_get(v_inst_3839_, 0);
v_toBind_3847_ = lean_ctor_get(v_inst_3839_, 1);
lean_inc_n(v_toBind_3847_, 3);
v_toPure_3848_ = lean_ctor_get(v_toApplicative_3846_, 1);
lean_inc_n(v_toPure_3848_, 4);
v_toMonadRef_3849_ = lean_ctor_get(v_inst_3841_, 1);
lean_inc_ref(v_toMonadRef_3849_);
lean_dec_ref(v_inst_3841_);
v___x_3850_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3840_, 2);
v___x_3851_ = lean_apply_2(v_inst_3840_, lean_box(0), v___x_3850_);
v___f_3852_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3852_, 0, v_toPure_3848_);
v___f_3853_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3853_, 0, v_inst_3840_);
lean_closure_set(v___f_3853_, 1, v_toBind_3847_);
lean_closure_set(v___f_3853_, 2, v___f_3852_);
lean_closure_set(v___f_3853_, 3, v_toPure_3848_);
v___f_3854_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3854_, 0, v_toPure_3848_);
v___f_3855_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3855_, 0, v_toPure_3848_);
lean_closure_set(v___f_3855_, 1, v_inst_3840_);
lean_closure_set(v___f_3855_, 2, v_toBind_3847_);
lean_closure_set(v___f_3855_, 3, v_inst_3842_);
lean_closure_set(v___f_3855_, 4, v_inst_3839_);
lean_closure_set(v___f_3855_, 5, v_toMonadRef_3849_);
lean_closure_set(v___f_3855_, 6, v_inst_3844_);
lean_closure_set(v___f_3855_, 7, v_inst_3843_);
lean_closure_set(v___f_3855_, 8, v_f_3845_);
lean_closure_set(v___f_3855_, 9, v___f_3854_);
lean_closure_set(v___f_3855_, 10, v___f_3853_);
v___x_3856_ = lean_apply_4(v_toBind_3847_, lean_box(0), lean_box(0), v___x_3851_, v___f_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3857_, lean_object* v_inst_3858_, lean_object* v_inst_3859_, lean_object* v_inst_3860_, lean_object* v_inst_3861_, lean_object* v_inst_3862_, lean_object* v_inst_3863_, lean_object* v_inst_3864_, lean_object* v_inst_3865_, lean_object* v_f_3866_){
_start:
{
lean_object* v_toApplicative_3867_; lean_object* v_toBind_3868_; lean_object* v_toPure_3869_; lean_object* v_toMonadRef_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___f_3873_; lean_object* v___f_3874_; lean_object* v___f_3875_; lean_object* v___f_3876_; lean_object* v___x_3877_; 
v_toApplicative_3867_ = lean_ctor_get(v_inst_3858_, 0);
v_toBind_3868_ = lean_ctor_get(v_inst_3858_, 1);
lean_inc_n(v_toBind_3868_, 3);
v_toPure_3869_ = lean_ctor_get(v_toApplicative_3867_, 1);
lean_inc_n(v_toPure_3869_, 4);
v_toMonadRef_3870_ = lean_ctor_get(v_inst_3860_, 1);
lean_inc_ref(v_toMonadRef_3870_);
lean_dec_ref(v_inst_3860_);
v___x_3871_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3859_, 2);
v___x_3872_ = lean_apply_2(v_inst_3859_, lean_box(0), v___x_3871_);
v___f_3873_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3873_, 0, v_toPure_3869_);
v___f_3874_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3874_, 0, v_inst_3859_);
lean_closure_set(v___f_3874_, 1, v_toBind_3868_);
lean_closure_set(v___f_3874_, 2, v___f_3873_);
lean_closure_set(v___f_3874_, 3, v_toPure_3869_);
v___f_3875_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3875_, 0, v_toPure_3869_);
v___f_3876_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3876_, 0, v_toPure_3869_);
lean_closure_set(v___f_3876_, 1, v_inst_3859_);
lean_closure_set(v___f_3876_, 2, v_toBind_3868_);
lean_closure_set(v___f_3876_, 3, v_inst_3862_);
lean_closure_set(v___f_3876_, 4, v_inst_3858_);
lean_closure_set(v___f_3876_, 5, v_toMonadRef_3870_);
lean_closure_set(v___f_3876_, 6, v_inst_3864_);
lean_closure_set(v___f_3876_, 7, v_inst_3863_);
lean_closure_set(v___f_3876_, 8, v_f_3866_);
lean_closure_set(v___f_3876_, 9, v___f_3875_);
lean_closure_set(v___f_3876_, 10, v___f_3874_);
v___x_3877_ = lean_apply_4(v_toBind_3868_, lean_box(0), lean_box(0), v___x_3872_, v___f_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3878_, lean_object* v_inst_3879_, lean_object* v_inst_3880_, lean_object* v_inst_3881_, lean_object* v_inst_3882_, lean_object* v_inst_3883_, lean_object* v_inst_3884_, lean_object* v_inst_3885_, lean_object* v_inst_3886_, lean_object* v_f_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3878_, v_inst_3879_, v_inst_3880_, v_inst_3881_, v_inst_3882_, v_inst_3883_, v_inst_3884_, v_inst_3885_, v_inst_3886_, v_f_3887_);
lean_dec_ref(v_inst_3886_);
lean_dec_ref(v_inst_3882_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3889_, lean_object* v_x_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_apply_1(v_f_3889_, v___y_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3893_, lean_object* v_inst_3894_, lean_object* v___f_3895_, lean_object* v_hyps_3896_){
_start:
{
lean_object* v_toPure_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v_toPure_3897_ = lean_ctor_get(v_toApplicative_3893_, 1);
lean_inc(v_toPure_3897_);
lean_dec_ref(v_toApplicative_3893_);
v___x_3898_ = lean_unsigned_to_nat(0u);
v___x_3899_ = lean_array_get_size(v_hyps_3896_);
v___x_3900_ = lean_box(0);
v___x_3901_ = lean_nat_dec_lt(v___x_3898_, v___x_3899_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; 
lean_dec_ref(v_hyps_3896_);
lean_dec(v___f_3895_);
lean_dec_ref(v_inst_3894_);
v___x_3902_ = lean_apply_2(v_toPure_3897_, lean_box(0), v___x_3900_);
return v___x_3902_;
}
else
{
uint8_t v___x_3903_; 
v___x_3903_ = lean_nat_dec_le(v___x_3899_, v___x_3899_);
if (v___x_3903_ == 0)
{
if (v___x_3901_ == 0)
{
lean_object* v___x_3904_; 
lean_dec_ref(v_hyps_3896_);
lean_dec(v___f_3895_);
lean_dec_ref(v_inst_3894_);
v___x_3904_ = lean_apply_2(v_toPure_3897_, lean_box(0), v___x_3900_);
return v___x_3904_;
}
else
{
size_t v___x_3905_; size_t v___x_3906_; lean_object* v___x_3907_; 
lean_dec(v_toPure_3897_);
v___x_3905_ = ((size_t)0ULL);
v___x_3906_ = lean_usize_of_nat(v___x_3899_);
v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3894_, v___f_3895_, v_hyps_3896_, v___x_3905_, v___x_3906_, v___x_3900_);
return v___x_3907_;
}
}
else
{
size_t v___x_3908_; size_t v___x_3909_; lean_object* v___x_3910_; 
lean_dec(v_toPure_3897_);
v___x_3908_ = ((size_t)0ULL);
v___x_3909_ = lean_usize_of_nat(v___x_3899_);
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3894_, v___f_3895_, v_hyps_3896_, v___x_3908_, v___x_3909_, v___x_3900_);
return v___x_3910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3911_, lean_object* v_inst_3912_, lean_object* v_f_3913_){
_start:
{
lean_object* v_toApplicative_3914_; lean_object* v_toBind_3915_; lean_object* v___f_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v_toApplicative_3914_ = lean_ctor_get(v_inst_3911_, 0);
lean_inc_ref(v_toApplicative_3914_);
v_toBind_3915_ = lean_ctor_get(v_inst_3911_, 1);
lean_inc(v_toBind_3915_);
v___f_3916_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3916_, 0, v_f_3913_);
v___f_3917_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3917_, 0, v_toApplicative_3914_);
lean_closure_set(v___f_3917_, 1, v_inst_3911_);
lean_closure_set(v___f_3917_, 2, v___f_3916_);
v___x_3918_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3919_ = lean_apply_2(v_inst_3912_, lean_box(0), v___x_3918_);
v___x_3920_ = lean_apply_4(v_toBind_3915_, lean_box(0), lean_box(0), v___x_3919_, v___f_3917_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3921_, lean_object* v_inst_3922_, lean_object* v_inst_3923_, lean_object* v_inst_3924_, lean_object* v_f_3925_){
_start:
{
lean_object* v_toApplicative_3926_; lean_object* v_toBind_3927_; lean_object* v___f_3928_; lean_object* v___f_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v_toApplicative_3926_ = lean_ctor_get(v_inst_3922_, 0);
lean_inc_ref(v_toApplicative_3926_);
v_toBind_3927_ = lean_ctor_get(v_inst_3922_, 1);
lean_inc(v_toBind_3927_);
v___f_3928_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3928_, 0, v_f_3925_);
v___f_3929_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3929_, 0, v_toApplicative_3926_);
lean_closure_set(v___f_3929_, 1, v_inst_3922_);
lean_closure_set(v___f_3929_, 2, v___f_3928_);
v___x_3930_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3931_ = lean_apply_2(v_inst_3923_, lean_box(0), v___x_3930_);
v___x_3932_ = lean_apply_4(v_toBind_3927_, lean_box(0), lean_box(0), v___x_3931_, v___f_3929_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3933_, lean_object* v_inst_3934_, lean_object* v_inst_3935_, lean_object* v_inst_3936_, lean_object* v_f_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3933_, v_inst_3934_, v_inst_3935_, v_inst_3936_, v_f_3937_);
lean_dec_ref(v_inst_3936_);
return v_res_3938_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_3941_, lean_object* v_methods_3942_, lean_object* v_config_3943_, lean_object* v_hyp_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___x_3953_; lean_object* v_caches_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v_typeAnalysis_3961_; lean_object* v_target_3962_; lean_object* v_hypotheses_3963_; uint8_t v_didChange_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4005_; 
v___x_3953_ = lean_st_ref_get(v_a_3945_);
v_caches_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc_ref(v_caches_3954_);
lean_dec(v___x_3953_);
v___x_3955_ = lean_unsigned_to_nat(0u);
v___x_3956_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_3941_, v_caches_3954_);
v___x_3957_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_3958_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3955_);
lean_ctor_set(v___x_3958_, 1, v___x_3956_);
lean_ctor_set(v___x_3958_, 2, v___x_3957_);
lean_ctor_set(v___x_3958_, 3, v___x_3957_);
v___x_3959_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3941_, v___x_3957_, v_caches_3954_);
v___x_3960_ = lean_st_ref_take(v_a_3945_);
v_typeAnalysis_3961_ = lean_ctor_get(v___x_3960_, 1);
v_target_3962_ = lean_ctor_get(v___x_3960_, 2);
v_hypotheses_3963_ = lean_ctor_get(v___x_3960_, 3);
v_didChange_3964_ = lean_ctor_get_uint8(v___x_3960_, sizeof(void*)*4);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4005_ == 0)
{
lean_object* v_unused_4006_; 
v_unused_4006_ = lean_ctor_get(v___x_3960_, 0);
lean_dec(v_unused_4006_);
v___x_3966_ = v___x_3960_;
v_isShared_3967_ = v_isSharedCheck_4005_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_hypotheses_3963_);
lean_inc(v_target_3962_);
lean_inc(v_typeAnalysis_3961_);
lean_dec(v___x_3960_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4005_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3959_);
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_typeAnalysis_3961_);
lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_target_3962_);
lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_hypotheses_3963_);
lean_ctor_set_uint8(v_reuseFailAlloc_4004_, sizeof(void*)*4, v_didChange_3964_);
v___x_3969_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; lean_object* v_type_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3970_ = lean_st_ref_put(v_a_3945_, v___x_3969_);
v_type_3971_ = lean_ctor_get(v_hyp_3944_, 1);
lean_inc_ref(v_type_3971_);
v___x_3972_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3972_, 0, v_type_3971_);
v___x_3973_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3972_, v_methods_3942_, v_config_3943_, v___x_3958_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v_fst_3975_; lean_object* v_snd_3976_; lean_object* v___x_3977_; lean_object* v_caches_3978_; lean_object* v_persistentCache_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_typeAnalysis_3982_; lean_object* v_target_3983_; lean_object* v_hypotheses_3984_; uint8_t v_didChange_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3994_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v___x_3973_, 1);
v_fst_3975_ = lean_ctor_get(v_a_3974_, 0);
lean_inc(v_fst_3975_);
v_snd_3976_ = lean_ctor_get(v_a_3974_, 1);
lean_inc(v_snd_3976_);
lean_dec(v_a_3974_);
v___x_3977_ = lean_st_ref_get(v_a_3945_);
v_caches_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc_ref(v_caches_3978_);
lean_dec(v___x_3977_);
v_persistentCache_3979_ = lean_ctor_get(v_snd_3976_, 1);
lean_inc_ref(v_persistentCache_3979_);
lean_dec(v_snd_3976_);
v___x_3980_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3941_, v_persistentCache_3979_, v_caches_3978_);
v___x_3981_ = lean_st_ref_take(v_a_3945_);
v_typeAnalysis_3982_ = lean_ctor_get(v___x_3981_, 1);
v_target_3983_ = lean_ctor_get(v___x_3981_, 2);
v_hypotheses_3984_ = lean_ctor_get(v___x_3981_, 3);
v_didChange_3985_ = lean_ctor_get_uint8(v___x_3981_, sizeof(void*)*4);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; 
v_unused_3995_ = lean_ctor_get(v___x_3981_, 0);
lean_dec(v_unused_3995_);
v___x_3987_ = v___x_3981_;
v_isShared_3988_ = v_isSharedCheck_3994_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_hypotheses_3984_);
lean_inc(v_target_3983_);
lean_inc(v_typeAnalysis_3982_);
lean_dec(v___x_3981_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3994_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3980_);
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3980_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_typeAnalysis_3982_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_target_3983_);
lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_hypotheses_3984_);
lean_ctor_set_uint8(v_reuseFailAlloc_3993_, sizeof(void*)*4, v_didChange_3985_);
v___x_3990_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3991_ = lean_st_ref_put(v_a_3945_, v___x_3990_);
v___x_3992_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_3944_, v_fst_3975_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v___x_3992_;
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec_ref(v_hyp_3944_);
v_a_3996_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3973_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3973_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_4007_, lean_object* v_methods_4008_, lean_object* v_config_4009_, lean_object* v_hyp_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
uint8_t v_cacheId_boxed_4019_; lean_object* v_res_4020_; 
v_cacheId_boxed_4019_ = lean_unbox(v_cacheId_4007_);
v_res_4020_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_4019_, v_methods_4008_, v_config_4009_, v_hyp_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_4021_, lean_object* v_methods_4022_, lean_object* v_config_4023_, lean_object* v_hyp_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4021_, v_methods_4022_, v_config_4023_, v_hyp_4024_, v_a_4026_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4038_, lean_object* v_methods_4039_, lean_object* v_config_4040_, lean_object* v_hyp_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
uint8_t v_cacheId_boxed_4054_; lean_object* v_res_4055_; 
v_cacheId_boxed_4054_ = lean_unbox(v_cacheId_4038_);
v_res_4055_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4054_, v_methods_4039_, v_config_4040_, v_hyp_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
lean_dec(v_a_4046_);
lean_dec_ref(v_a_4045_);
lean_dec(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4056_, lean_object* v_methods_4057_, lean_object* v_config_4058_, lean_object* v_hyp_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v___x_4068_; lean_object* v_caches_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v_typeAnalysis_4076_; lean_object* v_target_4077_; lean_object* v_hypotheses_4078_; uint8_t v_didChange_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4120_; 
v___x_4068_ = lean_st_ref_get(v_a_4060_);
v_caches_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc_ref(v_caches_4069_);
lean_dec(v___x_4068_);
v___x_4070_ = lean_unsigned_to_nat(0u);
v___x_4071_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4056_, v_caches_4069_);
v___x_4072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4074_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4056_, v___x_4073_, v_caches_4069_);
v___x_4075_ = lean_st_ref_take(v_a_4060_);
v_typeAnalysis_4076_ = lean_ctor_get(v___x_4075_, 1);
v_target_4077_ = lean_ctor_get(v___x_4075_, 2);
v_hypotheses_4078_ = lean_ctor_get(v___x_4075_, 3);
v_didChange_4079_ = lean_ctor_get_uint8(v___x_4075_, sizeof(void*)*4);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4120_ == 0)
{
lean_object* v_unused_4121_; 
v_unused_4121_ = lean_ctor_get(v___x_4075_, 0);
lean_dec(v_unused_4121_);
v___x_4081_ = v___x_4075_;
v_isShared_4082_ = v_isSharedCheck_4120_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_hypotheses_4078_);
lean_inc(v_target_4077_);
lean_inc(v_typeAnalysis_4076_);
lean_dec(v___x_4075_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4120_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v___x_4074_);
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4074_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v_typeAnalysis_4076_);
lean_ctor_set(v_reuseFailAlloc_4119_, 2, v_target_4077_);
lean_ctor_set(v_reuseFailAlloc_4119_, 3, v_hypotheses_4078_);
lean_ctor_set_uint8(v_reuseFailAlloc_4119_, sizeof(void*)*4, v_didChange_4079_);
v___x_4084_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4085_; lean_object* v_type_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4085_ = lean_st_ref_put(v_a_4060_, v___x_4084_);
v_type_4086_ = lean_ctor_get(v_hyp_4059_, 1);
lean_inc_ref(v_type_4086_);
v___x_4087_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4087_, 0, v_type_4086_);
v___x_4088_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4087_, v_methods_4057_, v_config_4058_, v___x_4072_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v_fst_4090_; lean_object* v_snd_4091_; lean_object* v___x_4092_; lean_object* v_caches_4093_; lean_object* v_cache_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v_typeAnalysis_4097_; lean_object* v_target_4098_; lean_object* v_hypotheses_4099_; uint8_t v_didChange_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4109_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4088_, 1);
v_fst_4090_ = lean_ctor_get(v_a_4089_, 0);
lean_inc(v_fst_4090_);
v_snd_4091_ = lean_ctor_get(v_a_4089_, 1);
lean_inc(v_snd_4091_);
lean_dec(v_a_4089_);
v___x_4092_ = lean_st_ref_get(v_a_4060_);
v_caches_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc_ref(v_caches_4093_);
lean_dec(v___x_4092_);
v_cache_4094_ = lean_ctor_get(v_snd_4091_, 1);
lean_inc_ref(v_cache_4094_);
lean_dec(v_snd_4091_);
v___x_4095_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4056_, v_cache_4094_, v_caches_4093_);
v___x_4096_ = lean_st_ref_take(v_a_4060_);
v_typeAnalysis_4097_ = lean_ctor_get(v___x_4096_, 1);
v_target_4098_ = lean_ctor_get(v___x_4096_, 2);
v_hypotheses_4099_ = lean_ctor_get(v___x_4096_, 3);
v_didChange_4100_ = lean_ctor_get_uint8(v___x_4096_, sizeof(void*)*4);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; 
v_unused_4110_ = lean_ctor_get(v___x_4096_, 0);
lean_dec(v_unused_4110_);
v___x_4102_ = v___x_4096_;
v_isShared_4103_ = v_isSharedCheck_4109_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_hypotheses_4099_);
lean_inc(v_target_4098_);
lean_inc(v_typeAnalysis_4097_);
lean_dec(v___x_4096_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4109_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4095_);
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4095_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_typeAnalysis_4097_);
lean_ctor_set(v_reuseFailAlloc_4108_, 2, v_target_4098_);
lean_ctor_set(v_reuseFailAlloc_4108_, 3, v_hypotheses_4099_);
lean_ctor_set_uint8(v_reuseFailAlloc_4108_, sizeof(void*)*4, v_didChange_4100_);
v___x_4105_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = lean_st_ref_put(v_a_4060_, v___x_4105_);
v___x_4107_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4059_, v_fst_4090_);
lean_dec(v_fst_4090_);
return v___x_4107_;
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec_ref(v_hyp_4059_);
v_a_4111_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4088_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4088_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4122_, lean_object* v_methods_4123_, lean_object* v_config_4124_, lean_object* v_hyp_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
uint8_t v_cacheId_boxed_4134_; lean_object* v_res_4135_; 
v_cacheId_boxed_4134_ = lean_unbox(v_cacheId_4122_);
v_res_4135_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4134_, v_methods_4123_, v_config_4124_, v_hyp_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4136_, lean_object* v_methods_4137_, lean_object* v_config_4138_, lean_object* v_hyp_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4136_, v_methods_4137_, v_config_4138_, v_hyp_4139_, v_a_4141_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4153_, lean_object* v_methods_4154_, lean_object* v_config_4155_, lean_object* v_hyp_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
uint8_t v_cacheId_boxed_4169_; lean_object* v_res_4170_; 
v_cacheId_boxed_4169_ = lean_unbox(v_cacheId_4153_);
v_res_4170_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4169_, v_methods_4154_, v_config_4155_, v_hyp_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
lean_dec(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4171_, lean_object* v_a_4172_, lean_object* v___x_4173_, lean_object* v_____r_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4187_ = lean_array_push(v_snd_4171_, v_a_4172_);
v___x_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4173_);
lean_ctor_set(v___x_4188_, 1, v___x_4187_);
v___x_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4191_, lean_object* v_a_4192_, lean_object* v___x_4193_, lean_object* v_____r_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4191_, v_a_4192_, v___x_4193_, v_____r_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4208_, lean_object* v___f_4209_, lean_object* v_____r_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; lean_object* v_caches_4224_; lean_object* v_typeAnalysis_4225_; lean_object* v_target_4226_; lean_object* v_hypotheses_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4237_; 
v___x_4223_ = lean_st_ref_take(v___y_4212_);
v_caches_4224_ = lean_ctor_get(v___x_4223_, 0);
v_typeAnalysis_4225_ = lean_ctor_get(v___x_4223_, 1);
v_target_4226_ = lean_ctor_get(v___x_4223_, 2);
v_hypotheses_4227_ = lean_ctor_get(v___x_4223_, 3);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4229_ = v___x_4223_;
v_isShared_4230_ = v_isSharedCheck_4237_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_hypotheses_4227_);
lean_inc(v_target_4226_);
lean_inc(v_typeAnalysis_4225_);
lean_inc(v_caches_4224_);
lean_dec(v___x_4223_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4237_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4231_; lean_object* v___x_4233_; 
v___x_4231_ = lean_box(0);
if (v_isShared_4230_ == 0)
{
v___x_4233_ = v___x_4229_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_caches_4224_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v_typeAnalysis_4225_);
lean_ctor_set(v_reuseFailAlloc_4236_, 2, v_target_4226_);
lean_ctor_set(v_reuseFailAlloc_4236_, 3, v_hypotheses_4227_);
v___x_4233_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_ctor_set_uint8(v___x_4233_, sizeof(void*)*4, v___x_4208_);
v___x_4234_ = lean_st_ref_put(v___y_4212_, v___x_4233_);
lean_inc(v___y_4221_);
lean_inc_ref(v___y_4220_);
lean_inc(v___y_4219_);
lean_inc_ref(v___y_4218_);
lean_inc(v___y_4217_);
lean_inc_ref(v___y_4216_);
lean_inc(v___y_4215_);
lean_inc_ref(v___y_4214_);
lean_inc(v___y_4213_);
lean_inc(v___y_4212_);
lean_inc_ref(v___y_4211_);
v___x_4235_ = lean_apply_13(v___f_4209_, v___x_4231_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, lean_box(0));
return v___x_4235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4238_, lean_object* v___f_4239_, lean_object* v_____r_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
uint8_t v___x_22285__boxed_4253_; lean_object* v_res_4254_; 
v___x_22285__boxed_4253_ = lean_unbox(v___x_4238_);
v_res_4254_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22285__boxed_4253_, v___f_4239_, v_____r_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4255_, lean_object* v_hypotheses_4256_, uint8_t v_cacheId_4257_, lean_object* v_methods_4258_, lean_object* v_config_4259_, lean_object* v___x_4260_, lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v_toMonadRef_4263_, lean_object* v___f_4264_, lean_object* v_next_4265_, lean_object* v_acc_4266_, lean_object* v_h_4267_, lean_object* v_G_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v___y_4282_; uint8_t v___x_4304_; 
v___x_4304_ = lean_nat_dec_lt(v_next_4265_, v___x_4255_);
if (v___x_4304_ == 0)
{
lean_object* v___x_4305_; 
lean_dec_ref(v_G_4268_);
lean_dec(v___f_4264_);
lean_dec_ref(v_toMonadRef_4263_);
lean_dec_ref(v___x_4262_);
lean_dec_ref(v___x_4261_);
lean_dec(v___x_4260_);
lean_dec_ref(v_config_4259_);
lean_dec_ref(v_methods_4258_);
v___x_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4305_, 0, v_acc_4266_);
return v___x_4305_;
}
else
{
lean_object* v_snd_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4380_; 
v_snd_4306_ = lean_ctor_get(v_acc_4266_, 1);
v_isSharedCheck_4380_ = !lean_is_exclusive(v_acc_4266_);
if (v_isSharedCheck_4380_ == 0)
{
lean_object* v_unused_4381_; 
v_unused_4381_ = lean_ctor_get(v_acc_4266_, 0);
lean_dec(v_unused_4381_);
v___x_4308_ = v_acc_4266_;
v_isShared_4309_ = v_isSharedCheck_4380_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_snd_4306_);
lean_dec(v_acc_4266_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4380_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = lean_array_fget_borrowed(v_hypotheses_4256_, v_next_4265_);
lean_inc(v___x_4310_);
v___x_4311_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4257_, v_methods_4258_, v_config_4259_, v___x_4310_, v___y_4270_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v_type_4313_; lean_object* v_value_4314_; uint8_t v___x_4315_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
v_type_4313_ = lean_ctor_get(v_a_4312_, 1);
v_value_4314_ = lean_ctor_get(v_a_4312_, 2);
lean_inc_ref(v_type_4313_);
v___x_4315_ = l_Lean_Expr_isFalse(v_type_4313_);
if (v___x_4315_ == 0)
{
lean_object* v_type_4316_; lean_object* v___f_4317_; uint8_t v___x_4347_; 
lean_del_object(v___x_4308_);
v_type_4316_ = lean_ctor_get(v___x_4310_, 1);
lean_inc(v___x_4260_);
lean_inc(v_a_4312_);
lean_inc(v_snd_4306_);
v___f_4317_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4317_, 0, v_snd_4306_);
lean_closure_set(v___f_4317_, 1, v_a_4312_);
lean_closure_set(v___f_4317_, 2, v___x_4260_);
v___x_4347_ = lean_expr_eqv(v_type_4316_, v_type_4313_);
if (v___x_4347_ == 0)
{
lean_inc_ref(v_type_4313_);
lean_dec(v_a_4312_);
lean_dec(v_snd_4306_);
lean_dec(v___x_4260_);
goto v___jp_4321_;
}
else
{
if (v___x_4315_ == 0)
{
lean_object* v___x_4348_; lean_object* v___x_4349_; 
lean_dec_ref(v___f_4317_);
lean_dec(v___f_4264_);
lean_dec_ref(v_toMonadRef_4263_);
lean_dec_ref(v___x_4262_);
lean_dec_ref(v___x_4261_);
v___x_4348_ = lean_box(0);
v___x_4349_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4306_, v_a_4312_, v___x_4260_, v___x_4348_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
v___y_4282_ = v___x_4349_;
goto v___jp_4281_;
}
else
{
lean_inc_ref(v_type_4313_);
lean_dec(v_a_4312_);
lean_dec(v_snd_4306_);
lean_dec(v___x_4260_);
goto v___jp_4321_;
}
}
v___jp_4318_:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4319_ = lean_box(0);
v___x_4320_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4304_, v___f_4317_, v___x_4319_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
v___y_4282_ = v___x_4320_;
goto v___jp_4281_;
}
v___jp_4321_:
{
lean_object* v_toCold_4322_; lean_object* v_options_4323_; uint8_t v_hasTrace_4324_; 
v_toCold_4322_ = lean_ctor_get(v___y_4278_, 0);
v_options_4323_ = lean_ctor_get(v_toCold_4322_, 2);
v_hasTrace_4324_ = lean_ctor_get_uint8(v_options_4323_, sizeof(void*)*1);
if (v_hasTrace_4324_ == 0)
{
lean_dec_ref(v_type_4313_);
lean_dec(v___f_4264_);
lean_dec_ref(v_toMonadRef_4263_);
lean_dec_ref(v___x_4262_);
lean_dec_ref(v___x_4261_);
goto v___jp_4318_;
}
else
{
lean_object* v_inheritedTraceOptions_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; uint8_t v___x_4328_; 
v_inheritedTraceOptions_4325_ = lean_ctor_get(v_toCold_4322_, 11);
v___x_4326_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4327_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4328_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4325_, v_options_4323_, v___x_4327_);
if (v___x_4328_ == 0)
{
lean_dec_ref(v_type_4313_);
lean_dec(v___f_4264_);
lean_dec_ref(v_toMonadRef_4263_);
lean_dec_ref(v___x_4262_);
lean_dec_ref(v___x_4261_);
goto v___jp_4318_;
}
else
{
lean_object* v_type_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_22210__overap_4335_; lean_object* v___x_4336_; 
v_type_4329_ = lean_ctor_get(v___x_4310_, 1);
lean_inc_ref(v_type_4329_);
v___x_4330_ = l_Lean_MessageData_ofExpr(v_type_4329_);
v___x_4331_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4330_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
v___x_4333_ = l_Lean_MessageData_ofExpr(v_type_4313_);
v___x_4334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4332_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_22210__overap_4335_ = l_Lean_addTrace___redArg(v___x_4261_, v___x_4262_, v_toMonadRef_4263_, v___f_4264_, v___x_4326_, v___x_4334_);
lean_inc(v___y_4279_);
lean_inc_ref(v___y_4278_);
lean_inc(v___y_4277_);
lean_inc_ref(v___y_4276_);
lean_inc(v___y_4275_);
lean_inc_ref(v___y_4274_);
lean_inc(v___y_4273_);
lean_inc_ref(v___y_4272_);
lean_inc(v___y_4271_);
lean_inc(v___y_4270_);
lean_inc_ref(v___y_4269_);
v___x_4336_ = lean_apply_12(v___x_22210__overap_4335_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, lean_box(0));
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4338_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4338_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4304_, v___f_4317_, v_a_4337_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
v___y_4282_ = v___x_4338_;
goto v___jp_4281_;
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v___f_4317_);
lean_dec_ref(v_G_4268_);
v_a_4339_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4336_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4336_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4350_; 
lean_inc_ref(v_value_4314_);
lean_dec(v_a_4312_);
lean_dec_ref(v_G_4268_);
lean_dec(v___f_4264_);
lean_dec_ref(v_toMonadRef_4263_);
lean_dec_ref(v___x_4262_);
lean_dec_ref(v___x_4261_);
lean_dec(v___x_4260_);
v___x_4350_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4314_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4362_; 
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; 
v_unused_4363_ = lean_ctor_get(v___x_4350_, 0);
lean_dec(v_unused_4363_);
v___x_4352_ = v___x_4350_;
v_isShared_4353_ = v_isSharedCheck_4362_;
goto v_resetjp_4351_;
}
else
{
lean_dec(v___x_4350_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4362_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4354_ = lean_box(v___x_4304_);
v___x_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v___x_4355_);
v___x_4357_ = v___x_4308_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_snd_4306_);
v___x_4357_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4359_; 
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4357_);
v___x_4359_ = v___x_4352_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
lean_del_object(v___x_4308_);
lean_dec(v_snd_4306_);
v_a_4364_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4350_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4350_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_del_object(v___x_4308_);
lean_dec(v_snd_4306_);
lean_dec_ref(v_G_4268_);
lean_dec(v___f_4264_);
lean_dec_ref(v_toMonadRef_4263_);
lean_dec_ref(v___x_4262_);
lean_dec_ref(v___x_4261_);
lean_dec(v___x_4260_);
v_a_4372_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4311_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4311_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
v___jp_4281_:
{
if (lean_obj_tag(v___y_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4295_; 
v_a_4283_ = lean_ctor_get(v___y_4282_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___y_4282_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4285_ = v___y_4282_;
v_isShared_4286_ = v_isSharedCheck_4295_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___y_4282_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4295_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
if (lean_obj_tag(v_a_4283_) == 0)
{
lean_object* v_a_4287_; lean_object* v___x_4289_; 
lean_dec_ref(v_G_4268_);
v_a_4287_ = lean_ctor_get(v_a_4283_, 0);
lean_inc(v_a_4287_);
lean_dec_ref_known(v_a_4283_, 1);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v_a_4287_);
v___x_4289_ = v___x_4285_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4287_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
lean_del_object(v___x_4285_);
v_a_4291_ = lean_ctor_get(v_a_4283_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v_a_4283_, 1);
v___x_4292_ = lean_unsigned_to_nat(1u);
v___x_4293_ = lean_nat_add(v_next_4265_, v___x_4292_);
lean_inc(v___y_4279_);
lean_inc_ref(v___y_4278_);
lean_inc(v___y_4277_);
lean_inc_ref(v___y_4276_);
lean_inc(v___y_4275_);
lean_inc_ref(v___y_4274_);
lean_inc(v___y_4273_);
lean_inc_ref(v___y_4272_);
lean_inc(v___y_4271_);
lean_inc(v___y_4270_);
lean_inc_ref(v___y_4269_);
v___x_4294_ = lean_apply_16(v_G_4268_, v___x_4293_, v_a_4291_, lean_box(0), lean_box(0), v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, lean_box(0));
return v___x_4294_;
}
}
}
else
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4303_; 
lean_dec_ref(v_G_4268_);
v_a_4296_ = lean_ctor_get(v___y_4282_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___y_4282_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4298_ = v___y_4282_;
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___y_4282_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4382_ = _args[0];
lean_object* v_hypotheses_4383_ = _args[1];
lean_object* v_cacheId_4384_ = _args[2];
lean_object* v_methods_4385_ = _args[3];
lean_object* v_config_4386_ = _args[4];
lean_object* v___x_4387_ = _args[5];
lean_object* v___x_4388_ = _args[6];
lean_object* v___x_4389_ = _args[7];
lean_object* v_toMonadRef_4390_ = _args[8];
lean_object* v___f_4391_ = _args[9];
lean_object* v_next_4392_ = _args[10];
lean_object* v_acc_4393_ = _args[11];
lean_object* v_h_4394_ = _args[12];
lean_object* v_G_4395_ = _args[13];
lean_object* v___y_4396_ = _args[14];
lean_object* v___y_4397_ = _args[15];
lean_object* v___y_4398_ = _args[16];
lean_object* v___y_4399_ = _args[17];
lean_object* v___y_4400_ = _args[18];
lean_object* v___y_4401_ = _args[19];
lean_object* v___y_4402_ = _args[20];
lean_object* v___y_4403_ = _args[21];
lean_object* v___y_4404_ = _args[22];
lean_object* v___y_4405_ = _args[23];
lean_object* v___y_4406_ = _args[24];
lean_object* v___y_4407_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4408_; lean_object* v_res_4409_; 
v_cacheId_boxed_4408_ = lean_unbox(v_cacheId_4384_);
v_res_4409_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4382_, v_hypotheses_4383_, v_cacheId_boxed_4408_, v_methods_4385_, v_config_4386_, v___x_4387_, v___x_4388_, v___x_4389_, v_toMonadRef_4390_, v___f_4391_, v_next_4392_, v_acc_4393_, v_h_4394_, v_G_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v_next_4392_);
lean_dec_ref(v_hypotheses_4383_);
lean_dec(v___x_4382_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4410_, lean_object* v_methods_4411_, lean_object* v_config_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v___x_4425_; lean_object* v_toApplicative_4426_; lean_object* v_toFunctor_4427_; lean_object* v_toSeq_4428_; lean_object* v_toSeqLeft_4429_; lean_object* v_toSeqRight_4430_; lean_object* v___f_4431_; lean_object* v___f_4432_; lean_object* v___f_4433_; lean_object* v___f_4434_; lean_object* v___x_4435_; lean_object* v___f_4436_; lean_object* v___f_4437_; lean_object* v___f_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v_toApplicative_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4529_; 
v___x_4425_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4426_ = lean_ctor_get(v___x_4425_, 0);
v_toFunctor_4427_ = lean_ctor_get(v_toApplicative_4426_, 0);
v_toSeq_4428_ = lean_ctor_get(v_toApplicative_4426_, 2);
v_toSeqLeft_4429_ = lean_ctor_get(v_toApplicative_4426_, 3);
v_toSeqRight_4430_ = lean_ctor_get(v_toApplicative_4426_, 4);
v___f_4431_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4432_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4427_, 2);
v___f_4433_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4433_, 0, v_toFunctor_4427_);
v___f_4434_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4434_, 0, v_toFunctor_4427_);
v___x_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___f_4433_);
lean_ctor_set(v___x_4435_, 1, v___f_4434_);
lean_inc(v_toSeqRight_4430_);
v___f_4436_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4436_, 0, v_toSeqRight_4430_);
lean_inc(v_toSeqLeft_4429_);
v___f_4437_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4437_, 0, v_toSeqLeft_4429_);
lean_inc(v_toSeq_4428_);
v___f_4438_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4438_, 0, v_toSeq_4428_);
v___x_4439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4435_);
lean_ctor_set(v___x_4439_, 1, v___f_4431_);
lean_ctor_set(v___x_4439_, 2, v___f_4438_);
lean_ctor_set(v___x_4439_, 3, v___f_4437_);
lean_ctor_set(v___x_4439_, 4, v___f_4436_);
v___x_4440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
lean_ctor_set(v___x_4440_, 1, v___f_4432_);
v___x_4441_ = l_StateRefT_x27_instMonad___redArg(v___x_4440_);
v_toApplicative_4442_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4529_ == 0)
{
lean_object* v_unused_4530_; 
v_unused_4530_ = lean_ctor_get(v___x_4441_, 1);
lean_dec(v_unused_4530_);
v___x_4444_ = v___x_4441_;
v_isShared_4445_ = v_isSharedCheck_4529_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_toApplicative_4442_);
lean_dec(v___x_4441_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4529_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v_toFunctor_4446_; lean_object* v_toSeq_4447_; lean_object* v_toSeqLeft_4448_; lean_object* v_toSeqRight_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4527_; 
v_toFunctor_4446_ = lean_ctor_get(v_toApplicative_4442_, 0);
v_toSeq_4447_ = lean_ctor_get(v_toApplicative_4442_, 2);
v_toSeqLeft_4448_ = lean_ctor_get(v_toApplicative_4442_, 3);
v_toSeqRight_4449_ = lean_ctor_get(v_toApplicative_4442_, 4);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_toApplicative_4442_);
if (v_isSharedCheck_4527_ == 0)
{
lean_object* v_unused_4528_; 
v_unused_4528_ = lean_ctor_get(v_toApplicative_4442_, 1);
lean_dec(v_unused_4528_);
v___x_4451_ = v_toApplicative_4442_;
v_isShared_4452_ = v_isSharedCheck_4527_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_toSeqRight_4449_);
lean_inc(v_toSeqLeft_4448_);
lean_inc(v_toSeq_4447_);
lean_inc(v_toFunctor_4446_);
lean_dec(v_toApplicative_4442_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4527_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___f_4453_; lean_object* v___f_4454_; lean_object* v___f_4455_; lean_object* v___f_4456_; lean_object* v___x_4457_; lean_object* v___f_4458_; lean_object* v___f_4459_; lean_object* v___f_4460_; lean_object* v___x_4462_; 
v___f_4453_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4454_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4446_);
v___f_4455_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4455_, 0, v_toFunctor_4446_);
v___f_4456_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4456_, 0, v_toFunctor_4446_);
v___x_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___f_4455_);
lean_ctor_set(v___x_4457_, 1, v___f_4456_);
v___f_4458_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4458_, 0, v_toSeqRight_4449_);
v___f_4459_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4459_, 0, v_toSeqLeft_4448_);
v___f_4460_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4460_, 0, v_toSeq_4447_);
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 4, v___f_4458_);
lean_ctor_set(v___x_4451_, 3, v___f_4459_);
lean_ctor_set(v___x_4451_, 2, v___f_4460_);
lean_ctor_set(v___x_4451_, 1, v___f_4453_);
lean_ctor_set(v___x_4451_, 0, v___x_4457_);
v___x_4462_ = v___x_4451_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v___f_4453_);
lean_ctor_set(v_reuseFailAlloc_4526_, 2, v___f_4460_);
lean_ctor_set(v_reuseFailAlloc_4526_, 3, v___f_4459_);
lean_ctor_set(v_reuseFailAlloc_4526_, 4, v___f_4458_);
v___x_4462_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4464_; 
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 1, v___f_4454_);
lean_ctor_set(v___x_4444_, 0, v___x_4462_);
v___x_4464_ = v___x_4444_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4462_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v___f_4454_);
v___x_4464_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v_toMonadRef_4473_; lean_object* v___f_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v_hypotheses_4477_; lean_object* v___x_4478_; lean_object* v_newHyps_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___f_4483_; lean_object* v___x_4484_; lean_object* v___x_22108__overap_4485_; lean_object* v___x_4486_; 
v___x_4465_ = l_StateRefT_x27_instMonad___redArg(v___x_4464_);
v___x_4466_ = l_ReaderT_instMonad___redArg(v___x_4465_);
v___x_4467_ = l_StateRefT_x27_instMonad___redArg(v___x_4466_);
v___x_4468_ = l_ReaderT_instMonad___redArg(v___x_4467_);
v___x_4469_ = l_ReaderT_instMonad___redArg(v___x_4468_);
v___x_4470_ = l_StateRefT_x27_instMonad___redArg(v___x_4469_);
v___x_4471_ = l_ReaderT_instMonad___redArg(v___x_4470_);
v___x_4472_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4473_ = lean_ctor_get(v___x_4472_, 0);
v___f_4474_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4475_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4476_ = lean_st_ref_get(v_a_4414_);
v_hypotheses_4477_ = lean_ctor_get(v___x_4476_, 3);
lean_inc_ref(v_hypotheses_4477_);
lean_dec(v___x_4476_);
v___x_4478_ = lean_array_get_size(v_hypotheses_4477_);
v_newHyps_4479_ = lean_mk_empty_array_with_capacity(v___x_4478_);
v___x_4480_ = lean_unsigned_to_nat(0u);
v___x_4481_ = lean_box(0);
v___x_4482_ = lean_box(v_cacheId_4410_);
lean_inc_ref(v_toMonadRef_4473_);
v___f_4483_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4483_, 0, v___x_4478_);
lean_closure_set(v___f_4483_, 1, v_hypotheses_4477_);
lean_closure_set(v___f_4483_, 2, v___x_4482_);
lean_closure_set(v___f_4483_, 3, v_methods_4411_);
lean_closure_set(v___f_4483_, 4, v_config_4412_);
lean_closure_set(v___f_4483_, 5, v___x_4481_);
lean_closure_set(v___f_4483_, 6, v___x_4471_);
lean_closure_set(v___f_4483_, 7, v___x_4475_);
lean_closure_set(v___f_4483_, 8, v_toMonadRef_4473_);
lean_closure_set(v___f_4483_, 9, v___f_4474_);
v___x_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4481_);
lean_ctor_set(v___x_4484_, 1, v_newHyps_4479_);
v___x_22108__overap_4485_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4483_, v___x_4480_, v___x_4484_, lean_box(0));
lean_inc(v_a_4423_);
lean_inc_ref(v_a_4422_);
lean_inc(v_a_4421_);
lean_inc_ref(v_a_4420_);
lean_inc(v_a_4419_);
lean_inc_ref(v_a_4418_);
lean_inc(v_a_4417_);
lean_inc_ref(v_a_4416_);
lean_inc(v_a_4415_);
lean_inc(v_a_4414_);
lean_inc_ref(v_a_4413_);
v___x_4486_ = lean_apply_12(v___x_22108__overap_4485_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, lean_box(0));
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4516_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4489_ = v___x_4486_;
v_isShared_4490_ = v_isSharedCheck_4516_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4486_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4516_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v_fst_4491_; 
v_fst_4491_ = lean_ctor_get(v_a_4487_, 0);
if (lean_obj_tag(v_fst_4491_) == 0)
{
lean_object* v_snd_4492_; lean_object* v___x_4493_; lean_object* v_caches_4494_; lean_object* v_typeAnalysis_4495_; lean_object* v_target_4496_; uint8_t v_didChange_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4510_; 
v_snd_4492_ = lean_ctor_get(v_a_4487_, 1);
lean_inc(v_snd_4492_);
lean_dec(v_a_4487_);
v___x_4493_ = lean_st_ref_take(v_a_4414_);
v_caches_4494_ = lean_ctor_get(v___x_4493_, 0);
v_typeAnalysis_4495_ = lean_ctor_get(v___x_4493_, 1);
v_target_4496_ = lean_ctor_get(v___x_4493_, 2);
v_didChange_4497_ = lean_ctor_get_uint8(v___x_4493_, sizeof(void*)*4);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4510_ == 0)
{
lean_object* v_unused_4511_; 
v_unused_4511_ = lean_ctor_get(v___x_4493_, 3);
lean_dec(v_unused_4511_);
v___x_4499_ = v___x_4493_;
v_isShared_4500_ = v_isSharedCheck_4510_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_target_4496_);
lean_inc(v_typeAnalysis_4495_);
lean_inc(v_caches_4494_);
lean_dec(v___x_4493_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4510_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 3, v_snd_4492_);
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_caches_4494_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_typeAnalysis_4495_);
lean_ctor_set(v_reuseFailAlloc_4509_, 2, v_target_4496_);
lean_ctor_set(v_reuseFailAlloc_4509_, 3, v_snd_4492_);
lean_ctor_set_uint8(v_reuseFailAlloc_4509_, sizeof(void*)*4, v_didChange_4497_);
v___x_4502_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; uint8_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4507_; 
v___x_4503_ = lean_st_ref_put(v_a_4414_, v___x_4502_);
v___x_4504_ = 0;
v___x_4505_ = lean_box(v___x_4504_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v___x_4505_);
v___x_4507_ = v___x_4489_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
else
{
lean_object* v_val_4512_; lean_object* v___x_4514_; 
lean_inc_ref(v_fst_4491_);
lean_dec(v_a_4487_);
v_val_4512_ = lean_ctor_get(v_fst_4491_, 0);
lean_inc(v_val_4512_);
lean_dec_ref_known(v_fst_4491_, 1);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v_val_4512_);
v___x_4514_ = v___x_4489_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_val_4512_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
v_a_4517_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4486_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4486_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_4531_, lean_object* v_methods_4532_, lean_object* v_config_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
uint8_t v_cacheId_boxed_4546_; lean_object* v_res_4547_; 
v_cacheId_boxed_4546_ = lean_unbox(v_cacheId_4531_);
v_res_4547_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_4546_, v_methods_4532_, v_config_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_4548_, lean_object* v_hypotheses_4549_, uint8_t v_cacheId_4550_, lean_object* v_methods_4551_, lean_object* v_config_4552_, lean_object* v___x_4553_, lean_object* v___x_4554_, lean_object* v___x_4555_, lean_object* v_toMonadRef_4556_, lean_object* v___f_4557_, lean_object* v_next_4558_, lean_object* v_acc_4559_, lean_object* v_h_4560_, lean_object* v_G_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v___y_4575_; uint8_t v___x_4597_; 
v___x_4597_ = lean_nat_dec_lt(v_next_4558_, v___x_4548_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
lean_dec_ref(v_G_4561_);
lean_dec(v___f_4557_);
lean_dec_ref(v_toMonadRef_4556_);
lean_dec_ref(v___x_4555_);
lean_dec_ref(v___x_4554_);
lean_dec(v___x_4553_);
lean_dec_ref(v_config_4552_);
lean_dec_ref(v_methods_4551_);
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_acc_4559_);
return v___x_4598_;
}
else
{
lean_object* v_snd_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4673_; 
v_snd_4599_ = lean_ctor_get(v_acc_4559_, 1);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_acc_4559_);
if (v_isSharedCheck_4673_ == 0)
{
lean_object* v_unused_4674_; 
v_unused_4674_ = lean_ctor_get(v_acc_4559_, 0);
lean_dec(v_unused_4674_);
v___x_4601_ = v_acc_4559_;
v_isShared_4602_ = v_isSharedCheck_4673_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_snd_4599_);
lean_dec(v_acc_4559_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4673_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4603_ = lean_array_fget_borrowed(v_hypotheses_4549_, v_next_4558_);
lean_inc(v___x_4603_);
v___x_4604_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4550_, v_methods_4551_, v_config_4552_, v___x_4603_, v___y_4563_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v_type_4606_; lean_object* v_value_4607_; uint8_t v___x_4608_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref_known(v___x_4604_, 1);
v_type_4606_ = lean_ctor_get(v_a_4605_, 1);
v_value_4607_ = lean_ctor_get(v_a_4605_, 2);
lean_inc_ref(v_type_4606_);
v___x_4608_ = l_Lean_Expr_isFalse(v_type_4606_);
if (v___x_4608_ == 0)
{
lean_object* v_type_4609_; lean_object* v___f_4610_; uint8_t v___x_4640_; 
lean_del_object(v___x_4601_);
v_type_4609_ = lean_ctor_get(v___x_4603_, 1);
lean_inc(v___x_4553_);
lean_inc(v_a_4605_);
lean_inc(v_snd_4599_);
v___f_4610_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4610_, 0, v_snd_4599_);
lean_closure_set(v___f_4610_, 1, v_a_4605_);
lean_closure_set(v___f_4610_, 2, v___x_4553_);
v___x_4640_ = lean_expr_eqv(v_type_4609_, v_type_4606_);
if (v___x_4640_ == 0)
{
lean_inc_ref(v_type_4606_);
lean_dec(v_a_4605_);
lean_dec(v_snd_4599_);
lean_dec(v___x_4553_);
goto v___jp_4614_;
}
else
{
if (v___x_4608_ == 0)
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
lean_dec_ref(v___f_4610_);
lean_dec(v___f_4557_);
lean_dec_ref(v_toMonadRef_4556_);
lean_dec_ref(v___x_4555_);
lean_dec_ref(v___x_4554_);
v___x_4641_ = lean_box(0);
v___x_4642_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4599_, v_a_4605_, v___x_4553_, v___x_4641_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
v___y_4575_ = v___x_4642_;
goto v___jp_4574_;
}
else
{
lean_inc_ref(v_type_4606_);
lean_dec(v_a_4605_);
lean_dec(v_snd_4599_);
lean_dec(v___x_4553_);
goto v___jp_4614_;
}
}
v___jp_4611_:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4612_ = lean_box(0);
v___x_4613_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4597_, v___f_4610_, v___x_4612_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
v___y_4575_ = v___x_4613_;
goto v___jp_4574_;
}
v___jp_4614_:
{
lean_object* v_toCold_4615_; lean_object* v_options_4616_; uint8_t v_hasTrace_4617_; 
v_toCold_4615_ = lean_ctor_get(v___y_4571_, 0);
v_options_4616_ = lean_ctor_get(v_toCold_4615_, 2);
v_hasTrace_4617_ = lean_ctor_get_uint8(v_options_4616_, sizeof(void*)*1);
if (v_hasTrace_4617_ == 0)
{
lean_dec_ref(v_type_4606_);
lean_dec(v___f_4557_);
lean_dec_ref(v_toMonadRef_4556_);
lean_dec_ref(v___x_4555_);
lean_dec_ref(v___x_4554_);
goto v___jp_4611_;
}
else
{
lean_object* v_inheritedTraceOptions_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; uint8_t v___x_4621_; 
v_inheritedTraceOptions_4618_ = lean_ctor_get(v_toCold_4615_, 11);
v___x_4619_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4620_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4621_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4618_, v_options_4616_, v___x_4620_);
if (v___x_4621_ == 0)
{
lean_dec_ref(v_type_4606_);
lean_dec(v___f_4557_);
lean_dec_ref(v_toMonadRef_4556_);
lean_dec_ref(v___x_4555_);
lean_dec_ref(v___x_4554_);
goto v___jp_4611_;
}
else
{
lean_object* v_type_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_22210__overap_4628_; lean_object* v___x_4629_; 
v_type_4622_ = lean_ctor_get(v___x_4603_, 1);
lean_inc_ref(v_type_4622_);
v___x_4623_ = l_Lean_MessageData_ofExpr(v_type_4622_);
v___x_4624_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4623_);
lean_ctor_set(v___x_4625_, 1, v___x_4624_);
v___x_4626_ = l_Lean_MessageData_ofExpr(v_type_4606_);
v___x_4627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4625_);
lean_ctor_set(v___x_4627_, 1, v___x_4626_);
v___x_22210__overap_4628_ = l_Lean_addTrace___redArg(v___x_4554_, v___x_4555_, v_toMonadRef_4556_, v___f_4557_, v___x_4619_, v___x_4627_);
lean_inc(v___y_4572_);
lean_inc_ref(v___y_4571_);
lean_inc(v___y_4570_);
lean_inc_ref(v___y_4569_);
lean_inc(v___y_4568_);
lean_inc_ref(v___y_4567_);
lean_inc(v___y_4566_);
lean_inc_ref(v___y_4565_);
lean_inc(v___y_4564_);
lean_inc(v___y_4563_);
lean_inc_ref(v___y_4562_);
v___x_4629_ = lean_apply_12(v___x_22210__overap_4628_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, lean_box(0));
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; lean_object* v___x_4631_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4630_);
lean_dec_ref_known(v___x_4629_, 1);
v___x_4631_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4597_, v___f_4610_, v_a_4630_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
v___y_4575_ = v___x_4631_;
goto v___jp_4574_;
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
lean_dec_ref(v___f_4610_);
lean_dec_ref(v_G_4561_);
v_a_4632_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4629_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4629_);
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
}
}
else
{
lean_object* v___x_4643_; 
lean_inc_ref(v_value_4607_);
lean_dec(v_a_4605_);
lean_dec_ref(v_G_4561_);
lean_dec(v___f_4557_);
lean_dec_ref(v_toMonadRef_4556_);
lean_dec_ref(v___x_4555_);
lean_dec_ref(v___x_4554_);
lean_dec(v___x_4553_);
v___x_4643_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4607_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4655_; 
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4655_ == 0)
{
lean_object* v_unused_4656_; 
v_unused_4656_ = lean_ctor_get(v___x_4643_, 0);
lean_dec(v_unused_4656_);
v___x_4645_ = v___x_4643_;
v_isShared_4646_ = v_isSharedCheck_4655_;
goto v_resetjp_4644_;
}
else
{
lean_dec(v___x_4643_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4655_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4650_; 
v___x_4647_ = lean_box(v___x_4597_);
v___x_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4648_);
v___x_4650_ = v___x_4601_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4648_);
lean_ctor_set(v_reuseFailAlloc_4654_, 1, v_snd_4599_);
v___x_4650_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
lean_object* v___x_4652_; 
if (v_isShared_4646_ == 0)
{
lean_ctor_set(v___x_4645_, 0, v___x_4650_);
v___x_4652_ = v___x_4645_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4650_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
else
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4664_; 
lean_del_object(v___x_4601_);
lean_dec(v_snd_4599_);
v_a_4657_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4659_ = v___x_4643_;
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4643_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4662_; 
if (v_isShared_4660_ == 0)
{
v___x_4662_ = v___x_4659_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
}
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
lean_del_object(v___x_4601_);
lean_dec(v_snd_4599_);
lean_dec_ref(v_G_4561_);
lean_dec(v___f_4557_);
lean_dec_ref(v_toMonadRef_4556_);
lean_dec_ref(v___x_4555_);
lean_dec_ref(v___x_4554_);
lean_dec(v___x_4553_);
v_a_4665_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4604_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4604_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
}
v___jp_4574_:
{
if (lean_obj_tag(v___y_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4588_; 
v_a_4576_ = lean_ctor_get(v___y_4575_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___y_4575_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4578_ = v___y_4575_;
v_isShared_4579_ = v_isSharedCheck_4588_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___y_4575_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4588_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
if (lean_obj_tag(v_a_4576_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4582_; 
lean_dec_ref(v_G_4561_);
v_a_4580_ = lean_ctor_get(v_a_4576_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v_a_4576_, 1);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v_a_4580_);
v___x_4582_ = v___x_4578_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
lean_del_object(v___x_4578_);
v_a_4584_ = lean_ctor_get(v_a_4576_, 0);
lean_inc(v_a_4584_);
lean_dec_ref_known(v_a_4576_, 1);
v___x_4585_ = lean_unsigned_to_nat(1u);
v___x_4586_ = lean_nat_add(v_next_4558_, v___x_4585_);
lean_inc(v___y_4572_);
lean_inc_ref(v___y_4571_);
lean_inc(v___y_4570_);
lean_inc_ref(v___y_4569_);
lean_inc(v___y_4568_);
lean_inc_ref(v___y_4567_);
lean_inc(v___y_4566_);
lean_inc_ref(v___y_4565_);
lean_inc(v___y_4564_);
lean_inc(v___y_4563_);
lean_inc_ref(v___y_4562_);
v___x_4587_ = lean_apply_16(v_G_4561_, v___x_4586_, v_a_4584_, lean_box(0), lean_box(0), v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, lean_box(0));
return v___x_4587_;
}
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec_ref(v_G_4561_);
v_a_4589_ = lean_ctor_get(v___y_4575_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___y_4575_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___y_4575_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___y_4575_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4675_ = _args[0];
lean_object* v_hypotheses_4676_ = _args[1];
lean_object* v_cacheId_4677_ = _args[2];
lean_object* v_methods_4678_ = _args[3];
lean_object* v_config_4679_ = _args[4];
lean_object* v___x_4680_ = _args[5];
lean_object* v___x_4681_ = _args[6];
lean_object* v___x_4682_ = _args[7];
lean_object* v_toMonadRef_4683_ = _args[8];
lean_object* v___f_4684_ = _args[9];
lean_object* v_next_4685_ = _args[10];
lean_object* v_acc_4686_ = _args[11];
lean_object* v_h_4687_ = _args[12];
lean_object* v_G_4688_ = _args[13];
lean_object* v___y_4689_ = _args[14];
lean_object* v___y_4690_ = _args[15];
lean_object* v___y_4691_ = _args[16];
lean_object* v___y_4692_ = _args[17];
lean_object* v___y_4693_ = _args[18];
lean_object* v___y_4694_ = _args[19];
lean_object* v___y_4695_ = _args[20];
lean_object* v___y_4696_ = _args[21];
lean_object* v___y_4697_ = _args[22];
lean_object* v___y_4698_ = _args[23];
lean_object* v___y_4699_ = _args[24];
lean_object* v___y_4700_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4701_; lean_object* v_res_4702_; 
v_cacheId_boxed_4701_ = lean_unbox(v_cacheId_4677_);
v_res_4702_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4675_, v_hypotheses_4676_, v_cacheId_boxed_4701_, v_methods_4678_, v_config_4679_, v___x_4680_, v___x_4681_, v___x_4682_, v_toMonadRef_4683_, v___f_4684_, v_next_4685_, v_acc_4686_, v_h_4687_, v_G_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v_next_4685_);
lean_dec_ref(v_hypotheses_4676_);
lean_dec(v___x_4675_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4703_, lean_object* v_methods_4704_, lean_object* v_config_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v___x_4718_; lean_object* v_toApplicative_4719_; lean_object* v_toFunctor_4720_; lean_object* v_toSeq_4721_; lean_object* v_toSeqLeft_4722_; lean_object* v_toSeqRight_4723_; lean_object* v___f_4724_; lean_object* v___f_4725_; lean_object* v___f_4726_; lean_object* v___f_4727_; lean_object* v___x_4728_; lean_object* v___f_4729_; lean_object* v___f_4730_; lean_object* v___f_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v_toApplicative_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4822_; 
v___x_4718_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4719_ = lean_ctor_get(v___x_4718_, 0);
v_toFunctor_4720_ = lean_ctor_get(v_toApplicative_4719_, 0);
v_toSeq_4721_ = lean_ctor_get(v_toApplicative_4719_, 2);
v_toSeqLeft_4722_ = lean_ctor_get(v_toApplicative_4719_, 3);
v_toSeqRight_4723_ = lean_ctor_get(v_toApplicative_4719_, 4);
v___f_4724_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4725_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4720_, 2);
v___f_4726_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4726_, 0, v_toFunctor_4720_);
v___f_4727_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4727_, 0, v_toFunctor_4720_);
v___x_4728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4728_, 0, v___f_4726_);
lean_ctor_set(v___x_4728_, 1, v___f_4727_);
lean_inc(v_toSeqRight_4723_);
v___f_4729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4729_, 0, v_toSeqRight_4723_);
lean_inc(v_toSeqLeft_4722_);
v___f_4730_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4730_, 0, v_toSeqLeft_4722_);
lean_inc(v_toSeq_4721_);
v___f_4731_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4731_, 0, v_toSeq_4721_);
v___x_4732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4728_);
lean_ctor_set(v___x_4732_, 1, v___f_4724_);
lean_ctor_set(v___x_4732_, 2, v___f_4731_);
lean_ctor_set(v___x_4732_, 3, v___f_4730_);
lean_ctor_set(v___x_4732_, 4, v___f_4729_);
v___x_4733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
lean_ctor_set(v___x_4733_, 1, v___f_4725_);
v___x_4734_ = l_StateRefT_x27_instMonad___redArg(v___x_4733_);
v_toApplicative_4735_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4822_ == 0)
{
lean_object* v_unused_4823_; 
v_unused_4823_ = lean_ctor_get(v___x_4734_, 1);
lean_dec(v_unused_4823_);
v___x_4737_ = v___x_4734_;
v_isShared_4738_ = v_isSharedCheck_4822_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_toApplicative_4735_);
lean_dec(v___x_4734_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4822_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v_toFunctor_4739_; lean_object* v_toSeq_4740_; lean_object* v_toSeqLeft_4741_; lean_object* v_toSeqRight_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4820_; 
v_toFunctor_4739_ = lean_ctor_get(v_toApplicative_4735_, 0);
v_toSeq_4740_ = lean_ctor_get(v_toApplicative_4735_, 2);
v_toSeqLeft_4741_ = lean_ctor_get(v_toApplicative_4735_, 3);
v_toSeqRight_4742_ = lean_ctor_get(v_toApplicative_4735_, 4);
v_isSharedCheck_4820_ = !lean_is_exclusive(v_toApplicative_4735_);
if (v_isSharedCheck_4820_ == 0)
{
lean_object* v_unused_4821_; 
v_unused_4821_ = lean_ctor_get(v_toApplicative_4735_, 1);
lean_dec(v_unused_4821_);
v___x_4744_ = v_toApplicative_4735_;
v_isShared_4745_ = v_isSharedCheck_4820_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_toSeqRight_4742_);
lean_inc(v_toSeqLeft_4741_);
lean_inc(v_toSeq_4740_);
lean_inc(v_toFunctor_4739_);
lean_dec(v_toApplicative_4735_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4820_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___f_4746_; lean_object* v___f_4747_; lean_object* v___f_4748_; lean_object* v___f_4749_; lean_object* v___x_4750_; lean_object* v___f_4751_; lean_object* v___f_4752_; lean_object* v___f_4753_; lean_object* v___x_4755_; 
v___f_4746_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4747_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4739_);
v___f_4748_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4748_, 0, v_toFunctor_4739_);
v___f_4749_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4749_, 0, v_toFunctor_4739_);
v___x_4750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___f_4748_);
lean_ctor_set(v___x_4750_, 1, v___f_4749_);
v___f_4751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4751_, 0, v_toSeqRight_4742_);
v___f_4752_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4752_, 0, v_toSeqLeft_4741_);
v___f_4753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4753_, 0, v_toSeq_4740_);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 4, v___f_4751_);
lean_ctor_set(v___x_4744_, 3, v___f_4752_);
lean_ctor_set(v___x_4744_, 2, v___f_4753_);
lean_ctor_set(v___x_4744_, 1, v___f_4746_);
lean_ctor_set(v___x_4744_, 0, v___x_4750_);
v___x_4755_ = v___x_4744_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4750_);
lean_ctor_set(v_reuseFailAlloc_4819_, 1, v___f_4746_);
lean_ctor_set(v_reuseFailAlloc_4819_, 2, v___f_4753_);
lean_ctor_set(v_reuseFailAlloc_4819_, 3, v___f_4752_);
lean_ctor_set(v_reuseFailAlloc_4819_, 4, v___f_4751_);
v___x_4755_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
lean_object* v___x_4757_; 
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 1, v___f_4747_);
lean_ctor_set(v___x_4737_, 0, v___x_4755_);
v___x_4757_ = v___x_4737_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4818_, 1, v___f_4747_);
v___x_4757_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v_toMonadRef_4766_; lean_object* v___f_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v_hypotheses_4770_; lean_object* v___x_4771_; lean_object* v_newHyps_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___f_4776_; lean_object* v___x_4777_; lean_object* v___x_22108__overap_4778_; lean_object* v___x_4779_; 
v___x_4758_ = l_StateRefT_x27_instMonad___redArg(v___x_4757_);
v___x_4759_ = l_ReaderT_instMonad___redArg(v___x_4758_);
v___x_4760_ = l_StateRefT_x27_instMonad___redArg(v___x_4759_);
v___x_4761_ = l_ReaderT_instMonad___redArg(v___x_4760_);
v___x_4762_ = l_ReaderT_instMonad___redArg(v___x_4761_);
v___x_4763_ = l_StateRefT_x27_instMonad___redArg(v___x_4762_);
v___x_4764_ = l_ReaderT_instMonad___redArg(v___x_4763_);
v___x_4765_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4766_ = lean_ctor_get(v___x_4765_, 0);
v___f_4767_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4768_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4769_ = lean_st_ref_get(v_a_4707_);
v_hypotheses_4770_ = lean_ctor_get(v___x_4769_, 3);
lean_inc_ref(v_hypotheses_4770_);
lean_dec(v___x_4769_);
v___x_4771_ = lean_array_get_size(v_hypotheses_4770_);
v_newHyps_4772_ = lean_mk_empty_array_with_capacity(v___x_4771_);
v___x_4773_ = lean_unsigned_to_nat(0u);
v___x_4774_ = lean_box(0);
v___x_4775_ = lean_box(v_cacheId_4703_);
lean_inc_ref(v_toMonadRef_4766_);
v___f_4776_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4776_, 0, v___x_4771_);
lean_closure_set(v___f_4776_, 1, v_hypotheses_4770_);
lean_closure_set(v___f_4776_, 2, v___x_4775_);
lean_closure_set(v___f_4776_, 3, v_methods_4704_);
lean_closure_set(v___f_4776_, 4, v_config_4705_);
lean_closure_set(v___f_4776_, 5, v___x_4774_);
lean_closure_set(v___f_4776_, 6, v___x_4764_);
lean_closure_set(v___f_4776_, 7, v___x_4768_);
lean_closure_set(v___f_4776_, 8, v_toMonadRef_4766_);
lean_closure_set(v___f_4776_, 9, v___f_4767_);
v___x_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4774_);
lean_ctor_set(v___x_4777_, 1, v_newHyps_4772_);
v___x_22108__overap_4778_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4776_, v___x_4773_, v___x_4777_, lean_box(0));
lean_inc(v_a_4716_);
lean_inc_ref(v_a_4715_);
lean_inc(v_a_4714_);
lean_inc_ref(v_a_4713_);
lean_inc(v_a_4712_);
lean_inc_ref(v_a_4711_);
lean_inc(v_a_4710_);
lean_inc_ref(v_a_4709_);
lean_inc(v_a_4708_);
lean_inc(v_a_4707_);
lean_inc_ref(v_a_4706_);
v___x_4779_ = lean_apply_12(v___x_22108__overap_4778_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, lean_box(0));
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4809_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4782_ = v___x_4779_;
v_isShared_4783_ = v_isSharedCheck_4809_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4809_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v_fst_4784_; 
v_fst_4784_ = lean_ctor_get(v_a_4780_, 0);
if (lean_obj_tag(v_fst_4784_) == 0)
{
lean_object* v_snd_4785_; lean_object* v___x_4786_; lean_object* v_caches_4787_; lean_object* v_typeAnalysis_4788_; lean_object* v_target_4789_; uint8_t v_didChange_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4803_; 
v_snd_4785_ = lean_ctor_get(v_a_4780_, 1);
lean_inc(v_snd_4785_);
lean_dec(v_a_4780_);
v___x_4786_ = lean_st_ref_take(v_a_4707_);
v_caches_4787_ = lean_ctor_get(v___x_4786_, 0);
v_typeAnalysis_4788_ = lean_ctor_get(v___x_4786_, 1);
v_target_4789_ = lean_ctor_get(v___x_4786_, 2);
v_didChange_4790_ = lean_ctor_get_uint8(v___x_4786_, sizeof(void*)*4);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4803_ == 0)
{
lean_object* v_unused_4804_; 
v_unused_4804_ = lean_ctor_get(v___x_4786_, 3);
lean_dec(v_unused_4804_);
v___x_4792_ = v___x_4786_;
v_isShared_4793_ = v_isSharedCheck_4803_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_target_4789_);
lean_inc(v_typeAnalysis_4788_);
lean_inc(v_caches_4787_);
lean_dec(v___x_4786_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4803_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 3, v_snd_4785_);
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_caches_4787_);
lean_ctor_set(v_reuseFailAlloc_4802_, 1, v_typeAnalysis_4788_);
lean_ctor_set(v_reuseFailAlloc_4802_, 2, v_target_4789_);
lean_ctor_set(v_reuseFailAlloc_4802_, 3, v_snd_4785_);
lean_ctor_set_uint8(v_reuseFailAlloc_4802_, sizeof(void*)*4, v_didChange_4790_);
v___x_4795_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
lean_object* v___x_4796_; uint8_t v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
v___x_4796_ = lean_st_ref_put(v_a_4707_, v___x_4795_);
v___x_4797_ = 0;
v___x_4798_ = lean_box(v___x_4797_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4798_);
v___x_4800_ = v___x_4782_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
else
{
lean_object* v_val_4805_; lean_object* v___x_4807_; 
lean_inc_ref(v_fst_4784_);
lean_dec(v_a_4780_);
v_val_4805_ = lean_ctor_get(v_fst_4784_, 0);
lean_inc(v_val_4805_);
lean_dec_ref_known(v_fst_4784_, 1);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v_val_4805_);
v___x_4807_ = v___x_4782_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_val_4805_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
v_a_4810_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4779_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4779_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4824_, lean_object* v_methods_4825_, lean_object* v_config_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
uint8_t v_cacheId_boxed_4839_; lean_object* v_res_4840_; 
v_cacheId_boxed_4839_ = lean_unbox(v_cacheId_4824_);
v_res_4840_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4839_, v_methods_4825_, v_config_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
lean_dec(v_a_4835_);
lean_dec_ref(v_a_4834_);
lean_dec(v_a_4833_);
lean_dec_ref(v_a_4832_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v___x_4847_; lean_object* v_env_4848_; uint8_t v___x_4849_; lean_object* v_env_4850_; lean_object* v___x_4851_; lean_object* v_toCold_4852_; lean_object* v_mctx_4853_; lean_object* v_lctx_4854_; lean_object* v_options_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4847_ = lean_st_ref_get(v___y_4845_);
v_env_4848_ = lean_ctor_get(v___x_4847_, 0);
lean_inc_ref(v_env_4848_);
lean_dec(v___x_4847_);
v___x_4849_ = 0;
v_env_4850_ = l_Lean_Environment_setRecordingDeps(v_env_4848_, v___x_4849_);
v___x_4851_ = lean_st_ref_get(v___y_4843_);
v_toCold_4852_ = lean_ctor_get(v___y_4844_, 0);
v_mctx_4853_ = lean_ctor_get(v___x_4851_, 0);
lean_inc_ref(v_mctx_4853_);
lean_dec(v___x_4851_);
v_lctx_4854_ = lean_ctor_get(v___y_4842_, 2);
v_options_4855_ = lean_ctor_get(v_toCold_4852_, 2);
lean_inc_ref(v_options_4855_);
lean_inc_ref(v_lctx_4854_);
v___x_4856_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4856_, 0, v_env_4850_);
lean_ctor_set(v___x_4856_, 1, v_mctx_4853_);
lean_ctor_set(v___x_4856_, 2, v_lctx_4854_);
lean_ctor_set(v___x_4856_, 3, v_options_4855_);
v___x_4857_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4856_);
lean_ctor_set(v___x_4857_, 1, v_msgData_4841_);
v___x_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4857_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
return v_res_4865_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4866_; double v___x_4867_; 
v___x_4866_ = lean_unsigned_to_nat(0u);
v___x_4867_ = lean_float_of_nat(v___x_4866_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4871_, lean_object* v_msg_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v_ref_4878_; lean_object* v___x_4879_; lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4925_; 
v_ref_4878_ = lean_ctor_get(v___y_4875_, 2);
v___x_4879_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4925_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4925_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4884_; lean_object* v_traceState_4885_; lean_object* v_env_4886_; lean_object* v_nextMacroScope_4887_; lean_object* v_ngen_4888_; lean_object* v_auxDeclNGen_4889_; lean_object* v_cache_4890_; lean_object* v_recordedDeps_4891_; lean_object* v_messages_4892_; lean_object* v_infoState_4893_; lean_object* v_snapshotTasks_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4924_; 
v___x_4884_ = lean_st_ref_take(v___y_4876_);
v_traceState_4885_ = lean_ctor_get(v___x_4884_, 4);
v_env_4886_ = lean_ctor_get(v___x_4884_, 0);
v_nextMacroScope_4887_ = lean_ctor_get(v___x_4884_, 1);
v_ngen_4888_ = lean_ctor_get(v___x_4884_, 2);
v_auxDeclNGen_4889_ = lean_ctor_get(v___x_4884_, 3);
v_cache_4890_ = lean_ctor_get(v___x_4884_, 5);
v_recordedDeps_4891_ = lean_ctor_get(v___x_4884_, 6);
v_messages_4892_ = lean_ctor_get(v___x_4884_, 7);
v_infoState_4893_ = lean_ctor_get(v___x_4884_, 8);
v_snapshotTasks_4894_ = lean_ctor_get(v___x_4884_, 9);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4896_ = v___x_4884_;
v_isShared_4897_ = v_isSharedCheck_4924_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_snapshotTasks_4894_);
lean_inc(v_infoState_4893_);
lean_inc(v_messages_4892_);
lean_inc(v_recordedDeps_4891_);
lean_inc(v_cache_4890_);
lean_inc(v_traceState_4885_);
lean_inc(v_auxDeclNGen_4889_);
lean_inc(v_ngen_4888_);
lean_inc(v_nextMacroScope_4887_);
lean_inc(v_env_4886_);
lean_dec(v___x_4884_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4924_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
uint64_t v_tid_4898_; lean_object* v_traces_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4923_; 
v_tid_4898_ = lean_ctor_get_uint64(v_traceState_4885_, sizeof(void*)*1);
v_traces_4899_ = lean_ctor_get(v_traceState_4885_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_traceState_4885_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4901_ = v_traceState_4885_;
v_isShared_4902_ = v_isSharedCheck_4923_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_traces_4899_);
lean_dec(v_traceState_4885_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4923_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; double v___x_4905_; uint8_t v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4914_; 
v___x_4903_ = lean_box(0);
v___x_4904_ = lean_box(0);
v___x_4905_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4906_ = 0;
v___x_4907_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4908_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4908_, 0, v_cls_4871_);
lean_ctor_set(v___x_4908_, 1, v___x_4904_);
lean_ctor_set(v___x_4908_, 2, v___x_4907_);
lean_ctor_set_float(v___x_4908_, sizeof(void*)*3, v___x_4905_);
lean_ctor_set_float(v___x_4908_, sizeof(void*)*3 + 8, v___x_4905_);
lean_ctor_set_uint8(v___x_4908_, sizeof(void*)*3 + 16, v___x_4906_);
v___x_4909_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4910_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4908_);
lean_ctor_set(v___x_4910_, 1, v_a_4880_);
lean_ctor_set(v___x_4910_, 2, v___x_4909_);
lean_inc(v_ref_4878_);
v___x_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4911_, 0, v_ref_4878_);
lean_ctor_set(v___x_4911_, 1, v___x_4910_);
v___x_4912_ = l_Lean_PersistentArray_push___redArg(v_traces_4899_, v___x_4911_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4912_);
v___x_4914_ = v___x_4901_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4912_);
lean_ctor_set_uint64(v_reuseFailAlloc_4922_, sizeof(void*)*1, v_tid_4898_);
v___x_4914_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
lean_object* v___x_4916_; 
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 4, v___x_4914_);
v___x_4916_ = v___x_4896_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_env_4886_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v_nextMacroScope_4887_);
lean_ctor_set(v_reuseFailAlloc_4921_, 2, v_ngen_4888_);
lean_ctor_set(v_reuseFailAlloc_4921_, 3, v_auxDeclNGen_4889_);
lean_ctor_set(v_reuseFailAlloc_4921_, 4, v___x_4914_);
lean_ctor_set(v_reuseFailAlloc_4921_, 5, v_cache_4890_);
lean_ctor_set(v_reuseFailAlloc_4921_, 6, v_recordedDeps_4891_);
lean_ctor_set(v_reuseFailAlloc_4921_, 7, v_messages_4892_);
lean_ctor_set(v_reuseFailAlloc_4921_, 8, v_infoState_4893_);
lean_ctor_set(v_reuseFailAlloc_4921_, 9, v_snapshotTasks_4894_);
v___x_4916_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
lean_object* v___x_4917_; lean_object* v___x_4919_; 
v___x_4917_ = lean_st_ref_put(v___y_4876_, v___x_4916_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4903_);
v___x_4919_ = v___x_4882_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4903_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4926_, lean_object* v_msg_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4926_, v_msg_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_4934_, lean_object* v___f_4935_, lean_object* v_____r_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
lean_object* v___x_4950_; lean_object* v_caches_4951_; lean_object* v_typeAnalysis_4952_; lean_object* v_target_4953_; lean_object* v_hypotheses_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4964_; 
v___x_4950_ = lean_st_ref_take(v___y_4939_);
v_caches_4951_ = lean_ctor_get(v___x_4950_, 0);
v_typeAnalysis_4952_ = lean_ctor_get(v___x_4950_, 1);
v_target_4953_ = lean_ctor_get(v___x_4950_, 2);
v_hypotheses_4954_ = lean_ctor_get(v___x_4950_, 3);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4956_ = v___x_4950_;
v_isShared_4957_ = v_isSharedCheck_4964_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_hypotheses_4954_);
lean_inc(v_target_4953_);
lean_inc(v_typeAnalysis_4952_);
lean_inc(v_caches_4951_);
lean_dec(v___x_4950_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4964_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4958_; lean_object* v___x_4960_; 
v___x_4958_ = lean_box(0);
if (v_isShared_4957_ == 0)
{
v___x_4960_ = v___x_4956_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_caches_4951_);
lean_ctor_set(v_reuseFailAlloc_4963_, 1, v_typeAnalysis_4952_);
lean_ctor_set(v_reuseFailAlloc_4963_, 2, v_target_4953_);
lean_ctor_set(v_reuseFailAlloc_4963_, 3, v_hypotheses_4954_);
v___x_4960_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; 
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*4, v___x_4934_);
v___x_4961_ = lean_st_ref_put(v___y_4939_, v___x_4960_);
lean_inc(v___y_4948_);
lean_inc_ref(v___y_4947_);
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
lean_inc(v___y_4944_);
lean_inc_ref(v___y_4943_);
lean_inc(v___y_4942_);
lean_inc_ref(v___y_4941_);
lean_inc(v___y_4940_);
lean_inc(v___y_4939_);
lean_inc_ref(v___y_4938_);
lean_inc(v___y_4937_);
v___x_4962_ = lean_apply_14(v___f_4935_, v___x_4958_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, lean_box(0));
return v___x_4962_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_4965_, lean_object* v___f_4966_, lean_object* v_____r_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_){
_start:
{
uint8_t v___x_35933__boxed_4981_; lean_object* v_res_4982_; 
v___x_35933__boxed_4981_ = lean_unbox(v___x_4965_);
v_res_4982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35933__boxed_4981_, v___f_4966_, v_____r_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec(v___y_4970_);
lean_dec_ref(v___y_4969_);
lean_dec(v___y_4968_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_4983_, lean_object* v_a_4984_, lean_object* v___x_4985_, lean_object* v_____r_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5000_ = lean_array_push(v_snd_4983_, v_a_4984_);
v___x_5001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___x_4985_);
lean_ctor_set(v___x_5001_, 1, v___x_5000_);
v___x_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5001_);
v___x_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5003_, 0, v___x_5002_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_5004_ = _args[0];
lean_object* v_a_5005_ = _args[1];
lean_object* v___x_5006_ = _args[2];
lean_object* v_____r_5007_ = _args[3];
lean_object* v___y_5008_ = _args[4];
lean_object* v___y_5009_ = _args[5];
lean_object* v___y_5010_ = _args[6];
lean_object* v___y_5011_ = _args[7];
lean_object* v___y_5012_ = _args[8];
lean_object* v___y_5013_ = _args[9];
lean_object* v___y_5014_ = _args[10];
lean_object* v___y_5015_ = _args[11];
lean_object* v___y_5016_ = _args[12];
lean_object* v___y_5017_ = _args[13];
lean_object* v___y_5018_ = _args[14];
lean_object* v___y_5019_ = _args[15];
lean_object* v___y_5020_ = _args[16];
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5004_, v_a_5005_, v___x_5006_, v_____r_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v___y_5013_);
lean_dec_ref(v___y_5012_);
lean_dec(v___y_5011_);
lean_dec(v___y_5010_);
lean_dec_ref(v___y_5009_);
lean_dec(v___y_5008_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5022_, lean_object* v___x_5023_, lean_object* v_methods_5024_, lean_object* v_config_5025_, lean_object* v_a_5026_, lean_object* v_b_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_){
_start:
{
lean_object* v___y_5042_; uint8_t v___x_5064_; 
v___x_5064_ = lean_nat_dec_lt(v_a_5026_, v_upperBound_5022_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5065_; 
lean_dec(v_a_5026_);
lean_dec_ref(v_config_5025_);
lean_dec_ref(v_methods_5024_);
v___x_5065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5065_, 0, v_b_5027_);
return v___x_5065_;
}
else
{
lean_object* v_snd_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5165_; 
v_snd_5066_ = lean_ctor_get(v_b_5027_, 1);
v_isSharedCheck_5165_ = !lean_is_exclusive(v_b_5027_);
if (v_isSharedCheck_5165_ == 0)
{
lean_object* v_unused_5166_; 
v_unused_5166_ = lean_ctor_get(v_b_5027_, 0);
lean_dec(v_unused_5166_);
v___x_5068_ = v_b_5027_;
v_isShared_5069_ = v_isSharedCheck_5165_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_snd_5066_);
lean_dec(v_b_5027_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5165_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v_type_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5070_ = lean_box(0);
v___x_5071_ = lean_array_fget_borrowed(v___x_5023_, v_a_5026_);
v___x_5072_ = lean_st_ref_take(v___y_5028_);
v___x_5073_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5074_ = lean_st_ref_put(v___y_5028_, v___x_5073_);
v_type_5075_ = lean_ctor_get(v___x_5071_, 1);
v___x_5076_ = lean_unsigned_to_nat(0u);
v___x_5077_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5076_);
lean_ctor_set(v___x_5077_, 1, v___x_5072_);
lean_ctor_set(v___x_5077_, 2, v___x_5073_);
lean_ctor_set(v___x_5077_, 3, v___x_5073_);
lean_inc_ref(v_type_5075_);
v___x_5078_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5078_, 0, v_type_5075_);
lean_inc_ref(v_config_5025_);
lean_inc_ref(v_methods_5024_);
v___x_5079_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5078_, v_methods_5024_, v_config_5025_, v___x_5077_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v_snd_5081_; lean_object* v_fst_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5156_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref_known(v___x_5079_, 1);
v_snd_5081_ = lean_ctor_get(v_a_5080_, 1);
v_fst_5082_ = lean_ctor_get(v_a_5080_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v_a_5080_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5084_ = v_a_5080_;
v_isShared_5085_ = v_isSharedCheck_5156_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_snd_5081_);
lean_inc(v_fst_5082_);
lean_dec(v_a_5080_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5156_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v_persistentCache_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
v_persistentCache_5086_ = lean_ctor_get(v_snd_5081_, 1);
lean_inc_ref(v_persistentCache_5086_);
lean_dec(v_snd_5081_);
v___x_5087_ = lean_st_ref_swap(v___y_5028_, v_persistentCache_5086_);
lean_dec(v___x_5087_);
lean_inc(v___x_5071_);
v___x_5088_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5071_, v_fst_5082_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_a_5089_; lean_object* v_type_5090_; lean_object* v_value_5091_; uint8_t v___x_5092_; 
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5089_);
lean_dec_ref_known(v___x_5088_, 1);
v_type_5090_ = lean_ctor_get(v_a_5089_, 1);
v_value_5091_ = lean_ctor_get(v_a_5089_, 2);
lean_inc_ref(v_type_5090_);
v___x_5092_ = l_Lean_Expr_isFalse(v_type_5090_);
if (v___x_5092_ == 0)
{
lean_object* v___f_5093_; uint8_t v___x_5123_; 
lean_del_object(v___x_5084_);
lean_inc(v_a_5089_);
lean_inc(v_snd_5066_);
v___f_5093_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5093_, 0, v_snd_5066_);
lean_closure_set(v___f_5093_, 1, v_a_5089_);
lean_closure_set(v___f_5093_, 2, v___x_5070_);
v___x_5123_ = lean_expr_eqv(v_type_5075_, v_type_5090_);
if (v___x_5123_ == 0)
{
lean_inc_ref(v_type_5090_);
lean_dec(v_a_5089_);
lean_dec(v_snd_5066_);
goto v___jp_5097_;
}
else
{
if (v___x_5092_ == 0)
{
lean_object* v___x_5124_; lean_object* v___x_5125_; 
lean_dec_ref(v___f_5093_);
lean_del_object(v___x_5068_);
v___x_5124_ = lean_box(0);
v___x_5125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5066_, v_a_5089_, v___x_5070_, v___x_5124_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
v___y_5042_ = v___x_5125_;
goto v___jp_5041_;
}
else
{
lean_inc_ref(v_type_5090_);
lean_dec(v_a_5089_);
lean_dec(v_snd_5066_);
goto v___jp_5097_;
}
}
v___jp_5094_:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5095_ = lean_box(0);
v___x_5096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5064_, v___f_5093_, v___x_5095_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
v___y_5042_ = v___x_5096_;
goto v___jp_5041_;
}
v___jp_5097_:
{
lean_object* v_toCold_5098_; lean_object* v_options_5099_; uint8_t v_hasTrace_5100_; 
v_toCold_5098_ = lean_ctor_get(v___y_5038_, 0);
v_options_5099_ = lean_ctor_get(v_toCold_5098_, 2);
v_hasTrace_5100_ = lean_ctor_get_uint8(v_options_5099_, sizeof(void*)*1);
if (v_hasTrace_5100_ == 0)
{
lean_dec_ref(v_type_5090_);
lean_del_object(v___x_5068_);
goto v___jp_5094_;
}
else
{
lean_object* v_inheritedTraceOptions_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
v_inheritedTraceOptions_5101_ = lean_ctor_get(v_toCold_5098_, 11);
v___x_5102_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5103_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5104_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5101_, v_options_5099_, v___x_5103_);
if (v___x_5104_ == 0)
{
lean_dec_ref(v_type_5090_);
lean_del_object(v___x_5068_);
goto v___jp_5094_;
}
else
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5108_; 
lean_inc_ref(v_type_5075_);
v___x_5105_ = l_Lean_MessageData_ofExpr(v_type_5075_);
v___x_5106_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5069_ == 0)
{
lean_ctor_set_tag(v___x_5068_, 7);
lean_ctor_set(v___x_5068_, 1, v___x_5106_);
lean_ctor_set(v___x_5068_, 0, v___x_5105_);
v___x_5108_ = v___x_5068_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5122_, 1, v___x_5106_);
v___x_5108_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5109_ = l_Lean_MessageData_ofExpr(v_type_5090_);
v___x_5110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5110_, 0, v___x_5108_);
lean_ctor_set(v___x_5110_, 1, v___x_5109_);
v___x_5111_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5102_, v___x_5110_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; lean_object* v___x_5113_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5112_);
lean_dec_ref_known(v___x_5111_, 1);
v___x_5113_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5064_, v___f_5093_, v_a_5112_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
v___y_5042_ = v___x_5113_;
goto v___jp_5041_;
}
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_dec_ref(v___f_5093_);
lean_dec(v_a_5026_);
lean_dec_ref(v_config_5025_);
lean_dec_ref(v_methods_5024_);
v_a_5114_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5111_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5111_);
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
}
}
}
else
{
lean_object* v___x_5126_; 
lean_inc_ref(v_value_5091_);
lean_dec(v_a_5089_);
lean_del_object(v___x_5068_);
lean_dec(v_a_5026_);
lean_dec_ref(v_config_5025_);
lean_dec_ref(v_methods_5024_);
v___x_5126_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5091_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5138_; 
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5138_ == 0)
{
lean_object* v_unused_5139_; 
v_unused_5139_ = lean_ctor_get(v___x_5126_, 0);
lean_dec(v_unused_5139_);
v___x_5128_ = v___x_5126_;
v_isShared_5129_ = v_isSharedCheck_5138_;
goto v_resetjp_5127_;
}
else
{
lean_dec(v___x_5126_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5138_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5133_; 
v___x_5130_ = lean_box(v___x_5064_);
v___x_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5131_, 0, v___x_5130_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 1, v_snd_5066_);
lean_ctor_set(v___x_5084_, 0, v___x_5131_);
v___x_5133_ = v___x_5084_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5131_);
lean_ctor_set(v_reuseFailAlloc_5137_, 1, v_snd_5066_);
v___x_5133_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
lean_object* v___x_5135_; 
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 0, v___x_5133_);
v___x_5135_ = v___x_5128_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v___x_5133_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
else
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5147_; 
lean_del_object(v___x_5084_);
lean_dec(v_snd_5066_);
v_a_5140_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5142_ = v___x_5126_;
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5126_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5145_; 
if (v_isShared_5143_ == 0)
{
v___x_5145_ = v___x_5142_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
}
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
lean_del_object(v___x_5084_);
lean_del_object(v___x_5068_);
lean_dec(v_snd_5066_);
lean_dec(v_a_5026_);
lean_dec_ref(v_config_5025_);
lean_dec_ref(v_methods_5024_);
v_a_5148_ = lean_ctor_get(v___x_5088_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5150_ = v___x_5088_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5088_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5148_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_del_object(v___x_5068_);
lean_dec(v_snd_5066_);
lean_dec(v_a_5026_);
lean_dec_ref(v_config_5025_);
lean_dec_ref(v_methods_5024_);
v_a_5157_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5079_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5079_);
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
v___jp_5041_:
{
if (lean_obj_tag(v___y_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5055_; 
v_a_5043_ = lean_ctor_get(v___y_5042_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___y_5042_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5045_ = v___y_5042_;
v_isShared_5046_ = v_isSharedCheck_5055_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v___y_5042_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5055_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
if (lean_obj_tag(v_a_5043_) == 0)
{
lean_object* v_a_5047_; lean_object* v___x_5049_; 
lean_dec(v_a_5026_);
lean_dec_ref(v_config_5025_);
lean_dec_ref(v_methods_5024_);
v_a_5047_ = lean_ctor_get(v_a_5043_, 0);
lean_inc(v_a_5047_);
lean_dec_ref_known(v_a_5043_, 1);
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 0, v_a_5047_);
v___x_5049_ = v___x_5045_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5047_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
else
{
lean_object* v_a_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
lean_del_object(v___x_5045_);
v_a_5051_ = lean_ctor_get(v_a_5043_, 0);
lean_inc(v_a_5051_);
lean_dec_ref_known(v_a_5043_, 1);
v___x_5052_ = lean_unsigned_to_nat(1u);
v___x_5053_ = lean_nat_add(v_a_5026_, v___x_5052_);
lean_dec(v_a_5026_);
v_a_5026_ = v___x_5053_;
v_b_5027_ = v_a_5051_;
goto _start;
}
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_dec(v_a_5026_);
lean_dec_ref(v_config_5025_);
lean_dec_ref(v_methods_5024_);
v_a_5056_ = lean_ctor_get(v___y_5042_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___y_5042_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___y_5042_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___y_5042_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5167_ = _args[0];
lean_object* v___x_5168_ = _args[1];
lean_object* v_methods_5169_ = _args[2];
lean_object* v_config_5170_ = _args[3];
lean_object* v_a_5171_ = _args[4];
lean_object* v_b_5172_ = _args[5];
lean_object* v___y_5173_ = _args[6];
lean_object* v___y_5174_ = _args[7];
lean_object* v___y_5175_ = _args[8];
lean_object* v___y_5176_ = _args[9];
lean_object* v___y_5177_ = _args[10];
lean_object* v___y_5178_ = _args[11];
lean_object* v___y_5179_ = _args[12];
lean_object* v___y_5180_ = _args[13];
lean_object* v___y_5181_ = _args[14];
lean_object* v___y_5182_ = _args[15];
lean_object* v___y_5183_ = _args[16];
lean_object* v___y_5184_ = _args[17];
lean_object* v___y_5185_ = _args[18];
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5167_, v___x_5168_, v_methods_5169_, v_config_5170_, v_a_5171_, v_b_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec_ref(v___y_5181_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5179_);
lean_dec(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___x_5168_);
lean_dec(v_upperBound_5167_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_5187_, lean_object* v_config_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_){
_start:
{
lean_object* v___x_5202_; lean_object* v_hypotheses_5203_; lean_object* v___x_5204_; lean_object* v_newHyps_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; 
v___x_5202_ = lean_st_ref_get(v_a_5191_);
v_hypotheses_5203_ = lean_ctor_get(v___x_5202_, 3);
lean_inc_ref(v_hypotheses_5203_);
lean_dec(v___x_5202_);
v___x_5204_ = lean_array_get_size(v_hypotheses_5203_);
v_newHyps_5205_ = lean_mk_empty_array_with_capacity(v___x_5204_);
v___x_5206_ = lean_unsigned_to_nat(0u);
v___x_5207_ = lean_box(0);
v___x_5208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5208_, 0, v___x_5207_);
lean_ctor_set(v___x_5208_, 1, v_newHyps_5205_);
v___x_5209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_5204_, v_hypotheses_5203_, v_methods_5187_, v_config_5188_, v___x_5206_, v___x_5208_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_, v_a_5200_);
lean_dec_ref(v_hypotheses_5203_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5239_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5212_ = v___x_5209_;
v_isShared_5213_ = v_isSharedCheck_5239_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5209_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5239_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v_fst_5214_; 
v_fst_5214_ = lean_ctor_get(v_a_5210_, 0);
if (lean_obj_tag(v_fst_5214_) == 0)
{
lean_object* v_snd_5215_; lean_object* v___x_5216_; lean_object* v_caches_5217_; lean_object* v_typeAnalysis_5218_; lean_object* v_target_5219_; uint8_t v_didChange_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5233_; 
v_snd_5215_ = lean_ctor_get(v_a_5210_, 1);
lean_inc(v_snd_5215_);
lean_dec(v_a_5210_);
v___x_5216_ = lean_st_ref_take(v_a_5191_);
v_caches_5217_ = lean_ctor_get(v___x_5216_, 0);
v_typeAnalysis_5218_ = lean_ctor_get(v___x_5216_, 1);
v_target_5219_ = lean_ctor_get(v___x_5216_, 2);
v_didChange_5220_ = lean_ctor_get_uint8(v___x_5216_, sizeof(void*)*4);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5233_ == 0)
{
lean_object* v_unused_5234_; 
v_unused_5234_ = lean_ctor_get(v___x_5216_, 3);
lean_dec(v_unused_5234_);
v___x_5222_ = v___x_5216_;
v_isShared_5223_ = v_isSharedCheck_5233_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_target_5219_);
lean_inc(v_typeAnalysis_5218_);
lean_inc(v_caches_5217_);
lean_dec(v___x_5216_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5233_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
lean_ctor_set(v___x_5222_, 3, v_snd_5215_);
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_caches_5217_);
lean_ctor_set(v_reuseFailAlloc_5232_, 1, v_typeAnalysis_5218_);
lean_ctor_set(v_reuseFailAlloc_5232_, 2, v_target_5219_);
lean_ctor_set(v_reuseFailAlloc_5232_, 3, v_snd_5215_);
lean_ctor_set_uint8(v_reuseFailAlloc_5232_, sizeof(void*)*4, v_didChange_5220_);
v___x_5225_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5226_; uint8_t v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5230_; 
v___x_5226_ = lean_st_ref_put(v_a_5191_, v___x_5225_);
v___x_5227_ = 0;
v___x_5228_ = lean_box(v___x_5227_);
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 0, v___x_5228_);
v___x_5230_ = v___x_5212_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5228_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
else
{
lean_object* v_val_5235_; lean_object* v___x_5237_; 
lean_inc_ref(v_fst_5214_);
lean_dec(v_a_5210_);
v_val_5235_ = lean_ctor_get(v_fst_5214_, 0);
lean_inc(v_val_5235_);
lean_dec_ref_known(v_fst_5214_, 1);
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 0, v_val_5235_);
v___x_5237_ = v___x_5212_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_val_5235_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
return v___x_5237_;
}
}
}
}
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5247_; 
v_a_5240_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5242_ = v___x_5209_;
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5209_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5245_; 
if (v_isShared_5243_ == 0)
{
v___x_5245_ = v___x_5242_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_a_5240_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_5248_, lean_object* v_config_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_){
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5248_, v_config_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
lean_dec(v_a_5257_);
lean_dec_ref(v_a_5256_);
lean_dec(v_a_5255_);
lean_dec_ref(v_a_5254_);
lean_dec(v_a_5253_);
lean_dec(v_a_5252_);
lean_dec_ref(v_a_5251_);
lean_dec(v_a_5250_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_5264_, lean_object* v_msg_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v___x_5279_; 
v___x_5279_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5264_, v_msg_5265_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_5280_, lean_object* v_msg_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5280_, v_msg_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
lean_dec(v___y_5289_);
lean_dec_ref(v___y_5288_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
return v_res_5295_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_upperBound_5296_, lean_object* v___x_5297_, lean_object* v_methods_5298_, lean_object* v_config_5299_, lean_object* v_inst_5300_, lean_object* v_R_5301_, lean_object* v_a_5302_, lean_object* v_b_5303_, lean_object* v_c_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_){
_start:
{
lean_object* v___x_5318_; 
v___x_5318_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5296_, v___x_5297_, v_methods_5298_, v_config_5299_, v_a_5302_, v_b_5303_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5319_ = _args[0];
lean_object* v___x_5320_ = _args[1];
lean_object* v_methods_5321_ = _args[2];
lean_object* v_config_5322_ = _args[3];
lean_object* v_inst_5323_ = _args[4];
lean_object* v_R_5324_ = _args[5];
lean_object* v_a_5325_ = _args[6];
lean_object* v_b_5326_ = _args[7];
lean_object* v_c_5327_ = _args[8];
lean_object* v___y_5328_ = _args[9];
lean_object* v___y_5329_ = _args[10];
lean_object* v___y_5330_ = _args[11];
lean_object* v___y_5331_ = _args[12];
lean_object* v___y_5332_ = _args[13];
lean_object* v___y_5333_ = _args[14];
lean_object* v___y_5334_ = _args[15];
lean_object* v___y_5335_ = _args[16];
lean_object* v___y_5336_ = _args[17];
lean_object* v___y_5337_ = _args[18];
lean_object* v___y_5338_ = _args[19];
lean_object* v___y_5339_ = _args[20];
lean_object* v___y_5340_ = _args[21];
_start:
{
lean_object* v_res_5341_; 
v_res_5341_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5319_, v___x_5320_, v_methods_5321_, v_config_5322_, v_inst_5323_, v_R_5324_, v_a_5325_, v_b_5326_, v_c_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___x_5320_);
lean_dec(v_upperBound_5319_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_5342_, lean_object* v_config_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_){
_start:
{
lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; 
v___x_5356_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5357_ = lean_st_mk_ref(v___x_5356_);
v___x_5358_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5342_, v_config_5343_, v___x_5357_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5367_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5361_ = v___x_5358_;
v_isShared_5362_ = v_isSharedCheck_5367_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_dec(v___x_5358_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5367_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5363_; lean_object* v___x_5365_; 
v___x_5363_ = lean_st_ref_get(v___x_5357_);
lean_dec(v___x_5357_);
lean_dec(v___x_5363_);
if (v_isShared_5362_ == 0)
{
v___x_5365_ = v___x_5361_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5359_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
else
{
lean_dec(v___x_5357_);
return v___x_5358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_5368_, lean_object* v_config_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_){
_start:
{
lean_object* v_res_5382_; 
v_res_5382_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5368_, v_config_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_);
lean_dec(v_a_5380_);
lean_dec_ref(v_a_5379_);
lean_dec(v_a_5378_);
lean_dec_ref(v_a_5377_);
lean_dec(v_a_5376_);
lean_dec_ref(v_a_5375_);
lean_dec(v_a_5374_);
lean_dec_ref(v_a_5373_);
lean_dec(v_a_5372_);
lean_dec(v_a_5371_);
lean_dec_ref(v_a_5370_);
return v_res_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_5383_, lean_object* v_msg_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
lean_object* v_ref_5390_; lean_object* v___x_5391_; lean_object* v_a_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5437_; 
v_ref_5390_ = lean_ctor_get(v___y_5387_, 2);
v___x_5391_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5394_ = v___x_5391_;
v_isShared_5395_ = v_isSharedCheck_5437_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_a_5392_);
lean_dec(v___x_5391_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5437_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v___x_5396_; lean_object* v_traceState_5397_; lean_object* v_env_5398_; lean_object* v_nextMacroScope_5399_; lean_object* v_ngen_5400_; lean_object* v_auxDeclNGen_5401_; lean_object* v_cache_5402_; lean_object* v_recordedDeps_5403_; lean_object* v_messages_5404_; lean_object* v_infoState_5405_; lean_object* v_snapshotTasks_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5436_; 
v___x_5396_ = lean_st_ref_take(v___y_5388_);
v_traceState_5397_ = lean_ctor_get(v___x_5396_, 4);
v_env_5398_ = lean_ctor_get(v___x_5396_, 0);
v_nextMacroScope_5399_ = lean_ctor_get(v___x_5396_, 1);
v_ngen_5400_ = lean_ctor_get(v___x_5396_, 2);
v_auxDeclNGen_5401_ = lean_ctor_get(v___x_5396_, 3);
v_cache_5402_ = lean_ctor_get(v___x_5396_, 5);
v_recordedDeps_5403_ = lean_ctor_get(v___x_5396_, 6);
v_messages_5404_ = lean_ctor_get(v___x_5396_, 7);
v_infoState_5405_ = lean_ctor_get(v___x_5396_, 8);
v_snapshotTasks_5406_ = lean_ctor_get(v___x_5396_, 9);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5396_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5408_ = v___x_5396_;
v_isShared_5409_ = v_isSharedCheck_5436_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_snapshotTasks_5406_);
lean_inc(v_infoState_5405_);
lean_inc(v_messages_5404_);
lean_inc(v_recordedDeps_5403_);
lean_inc(v_cache_5402_);
lean_inc(v_traceState_5397_);
lean_inc(v_auxDeclNGen_5401_);
lean_inc(v_ngen_5400_);
lean_inc(v_nextMacroScope_5399_);
lean_inc(v_env_5398_);
lean_dec(v___x_5396_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5436_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
uint64_t v_tid_5410_; lean_object* v_traces_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5435_; 
v_tid_5410_ = lean_ctor_get_uint64(v_traceState_5397_, sizeof(void*)*1);
v_traces_5411_ = lean_ctor_get(v_traceState_5397_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v_traceState_5397_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5413_ = v_traceState_5397_;
v_isShared_5414_ = v_isSharedCheck_5435_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_traces_5411_);
lean_dec(v_traceState_5397_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5435_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5415_; lean_object* v___x_5416_; double v___x_5417_; uint8_t v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5426_; 
v___x_5415_ = lean_box(0);
v___x_5416_ = lean_box(0);
v___x_5417_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5418_ = 0;
v___x_5419_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5420_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5420_, 0, v_cls_5383_);
lean_ctor_set(v___x_5420_, 1, v___x_5416_);
lean_ctor_set(v___x_5420_, 2, v___x_5419_);
lean_ctor_set_float(v___x_5420_, sizeof(void*)*3, v___x_5417_);
lean_ctor_set_float(v___x_5420_, sizeof(void*)*3 + 8, v___x_5417_);
lean_ctor_set_uint8(v___x_5420_, sizeof(void*)*3 + 16, v___x_5418_);
v___x_5421_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5422_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5422_, 0, v___x_5420_);
lean_ctor_set(v___x_5422_, 1, v_a_5392_);
lean_ctor_set(v___x_5422_, 2, v___x_5421_);
lean_inc(v_ref_5390_);
v___x_5423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5423_, 0, v_ref_5390_);
lean_ctor_set(v___x_5423_, 1, v___x_5422_);
v___x_5424_ = l_Lean_PersistentArray_push___redArg(v_traces_5411_, v___x_5423_);
if (v_isShared_5414_ == 0)
{
lean_ctor_set(v___x_5413_, 0, v___x_5424_);
v___x_5426_ = v___x_5413_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v___x_5424_);
lean_ctor_set_uint64(v_reuseFailAlloc_5434_, sizeof(void*)*1, v_tid_5410_);
v___x_5426_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
lean_object* v___x_5428_; 
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 4, v___x_5426_);
v___x_5428_ = v___x_5408_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_env_5398_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v_nextMacroScope_5399_);
lean_ctor_set(v_reuseFailAlloc_5433_, 2, v_ngen_5400_);
lean_ctor_set(v_reuseFailAlloc_5433_, 3, v_auxDeclNGen_5401_);
lean_ctor_set(v_reuseFailAlloc_5433_, 4, v___x_5426_);
lean_ctor_set(v_reuseFailAlloc_5433_, 5, v_cache_5402_);
lean_ctor_set(v_reuseFailAlloc_5433_, 6, v_recordedDeps_5403_);
lean_ctor_set(v_reuseFailAlloc_5433_, 7, v_messages_5404_);
lean_ctor_set(v_reuseFailAlloc_5433_, 8, v_infoState_5405_);
lean_ctor_set(v_reuseFailAlloc_5433_, 9, v_snapshotTasks_5406_);
v___x_5428_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
lean_object* v___x_5429_; lean_object* v___x_5431_; 
v___x_5429_ = lean_st_ref_put(v___y_5388_, v___x_5428_);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 0, v___x_5415_);
v___x_5431_ = v___x_5394_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v___x_5415_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5438_, lean_object* v_msg_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5438_, v_msg_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_);
lean_dec(v___y_5443_);
lean_dec_ref(v___y_5442_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5446_, lean_object* v___x_5447_, lean_object* v_methods_5448_, lean_object* v_config_5449_, lean_object* v_a_5450_, lean_object* v_b_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_){
_start:
{
lean_object* v___y_5466_; uint8_t v___x_5488_; 
v___x_5488_ = lean_nat_dec_lt(v_a_5450_, v_upperBound_5446_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5489_; 
lean_dec(v_a_5450_);
lean_dec_ref(v_config_5449_);
lean_dec_ref(v_methods_5448_);
v___x_5489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5489_, 0, v_b_5451_);
return v___x_5489_;
}
else
{
lean_object* v_snd_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5596_; 
v_snd_5490_ = lean_ctor_get(v_b_5451_, 1);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_b_5451_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v_b_5451_, 0);
lean_dec(v_unused_5597_);
v___x_5492_ = v_b_5451_;
v_isShared_5493_ = v_isSharedCheck_5596_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_snd_5490_);
lean_dec(v_b_5451_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5596_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v_type_5499_; lean_object* v___x_5500_; lean_object* v___x_5502_; 
v___x_5494_ = lean_box(0);
v___x_5495_ = lean_array_fget_borrowed(v___x_5447_, v_a_5450_);
v___x_5496_ = lean_st_ref_take(v___y_5452_);
v___x_5497_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5498_ = lean_st_ref_put(v___y_5452_, v___x_5497_);
v_type_5499_ = lean_ctor_get(v___x_5495_, 1);
v___x_5500_ = lean_unsigned_to_nat(0u);
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 1, v___x_5496_);
lean_ctor_set(v___x_5492_, 0, v___x_5500_);
v___x_5502_ = v___x_5492_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5500_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___x_5496_);
v___x_5502_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5503_; lean_object* v___x_5504_; 
lean_inc_ref(v_type_5499_);
v___x_5503_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5503_, 0, v_type_5499_);
lean_inc_ref(v_config_5449_);
lean_inc_ref(v_methods_5448_);
v___x_5504_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5503_, v_methods_5448_, v_config_5449_, v___x_5502_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v_a_5505_; lean_object* v_snd_5506_; lean_object* v_fst_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5586_; 
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
lean_inc(v_a_5505_);
lean_dec_ref_known(v___x_5504_, 1);
v_snd_5506_ = lean_ctor_get(v_a_5505_, 1);
v_fst_5507_ = lean_ctor_get(v_a_5505_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v_a_5505_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5509_ = v_a_5505_;
v_isShared_5510_ = v_isSharedCheck_5586_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_snd_5506_);
lean_inc(v_fst_5507_);
lean_dec(v_a_5505_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5586_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v_cache_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5584_; 
v_cache_5511_ = lean_ctor_get(v_snd_5506_, 1);
v_isSharedCheck_5584_ = !lean_is_exclusive(v_snd_5506_);
if (v_isSharedCheck_5584_ == 0)
{
lean_object* v_unused_5585_; 
v_unused_5585_ = lean_ctor_get(v_snd_5506_, 0);
lean_dec(v_unused_5585_);
v___x_5513_ = v_snd_5506_;
v_isShared_5514_ = v_isSharedCheck_5584_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_cache_5511_);
lean_dec(v_snd_5506_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5584_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5515_ = lean_st_ref_swap(v___y_5452_, v_cache_5511_);
lean_dec(v___x_5515_);
lean_inc(v___x_5495_);
v___x_5516_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5495_, v_fst_5507_);
lean_dec(v_fst_5507_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_object* v_a_5517_; lean_object* v_type_5518_; lean_object* v_value_5519_; uint8_t v___x_5520_; 
v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
lean_inc(v_a_5517_);
lean_dec_ref_known(v___x_5516_, 1);
v_type_5518_ = lean_ctor_get(v_a_5517_, 1);
v_value_5519_ = lean_ctor_get(v_a_5517_, 2);
lean_inc_ref(v_type_5518_);
v___x_5520_ = l_Lean_Expr_isFalse(v_type_5518_);
if (v___x_5520_ == 0)
{
lean_object* v___f_5521_; uint8_t v___x_5551_; 
lean_del_object(v___x_5509_);
lean_inc(v_a_5517_);
lean_inc(v_snd_5490_);
v___f_5521_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5521_, 0, v_snd_5490_);
lean_closure_set(v___f_5521_, 1, v_a_5517_);
lean_closure_set(v___f_5521_, 2, v___x_5494_);
v___x_5551_ = lean_expr_eqv(v_type_5499_, v_type_5518_);
if (v___x_5551_ == 0)
{
lean_inc_ref(v_type_5518_);
lean_dec(v_a_5517_);
lean_dec(v_snd_5490_);
goto v___jp_5525_;
}
else
{
if (v___x_5520_ == 0)
{
lean_object* v___x_5552_; lean_object* v___x_5553_; 
lean_dec_ref(v___f_5521_);
lean_del_object(v___x_5513_);
v___x_5552_ = lean_box(0);
v___x_5553_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5490_, v_a_5517_, v___x_5494_, v___x_5552_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
v___y_5466_ = v___x_5553_;
goto v___jp_5465_;
}
else
{
lean_inc_ref(v_type_5518_);
lean_dec(v_a_5517_);
lean_dec(v_snd_5490_);
goto v___jp_5525_;
}
}
v___jp_5522_:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; 
v___x_5523_ = lean_box(0);
v___x_5524_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5488_, v___f_5521_, v___x_5523_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
v___y_5466_ = v___x_5524_;
goto v___jp_5465_;
}
v___jp_5525_:
{
lean_object* v_toCold_5526_; lean_object* v_options_5527_; uint8_t v_hasTrace_5528_; 
v_toCold_5526_ = lean_ctor_get(v___y_5462_, 0);
v_options_5527_ = lean_ctor_get(v_toCold_5526_, 2);
v_hasTrace_5528_ = lean_ctor_get_uint8(v_options_5527_, sizeof(void*)*1);
if (v_hasTrace_5528_ == 0)
{
lean_dec_ref(v_type_5518_);
lean_del_object(v___x_5513_);
goto v___jp_5522_;
}
else
{
lean_object* v_inheritedTraceOptions_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; uint8_t v___x_5532_; 
v_inheritedTraceOptions_5529_ = lean_ctor_get(v_toCold_5526_, 11);
v___x_5530_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5531_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5529_, v_options_5527_, v___x_5531_);
if (v___x_5532_ == 0)
{
lean_dec_ref(v_type_5518_);
lean_del_object(v___x_5513_);
goto v___jp_5522_;
}
else
{
lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5536_; 
lean_inc_ref(v_type_5499_);
v___x_5533_ = l_Lean_MessageData_ofExpr(v_type_5499_);
v___x_5534_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5514_ == 0)
{
lean_ctor_set_tag(v___x_5513_, 7);
lean_ctor_set(v___x_5513_, 1, v___x_5534_);
lean_ctor_set(v___x_5513_, 0, v___x_5533_);
v___x_5536_ = v___x_5513_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v___x_5533_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; 
v___x_5537_ = l_Lean_MessageData_ofExpr(v_type_5518_);
v___x_5538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5538_, 0, v___x_5536_);
lean_ctor_set(v___x_5538_, 1, v___x_5537_);
v___x_5539_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5530_, v___x_5538_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
if (lean_obj_tag(v___x_5539_) == 0)
{
lean_object* v_a_5540_; lean_object* v___x_5541_; 
v_a_5540_ = lean_ctor_get(v___x_5539_, 0);
lean_inc(v_a_5540_);
lean_dec_ref_known(v___x_5539_, 1);
v___x_5541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5488_, v___f_5521_, v_a_5540_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
v___y_5466_ = v___x_5541_;
goto v___jp_5465_;
}
else
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5549_; 
lean_dec_ref(v___f_5521_);
lean_dec(v_a_5450_);
lean_dec_ref(v_config_5449_);
lean_dec_ref(v_methods_5448_);
v_a_5542_ = lean_ctor_get(v___x_5539_, 0);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5539_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5544_ = v___x_5539_;
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5539_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_a_5542_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
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
lean_object* v___x_5554_; 
lean_inc_ref(v_value_5519_);
lean_dec(v_a_5517_);
lean_del_object(v___x_5513_);
lean_dec(v_a_5450_);
lean_dec_ref(v_config_5449_);
lean_dec_ref(v_methods_5448_);
v___x_5554_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5519_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5566_; 
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5566_ == 0)
{
lean_object* v_unused_5567_; 
v_unused_5567_ = lean_ctor_get(v___x_5554_, 0);
lean_dec(v_unused_5567_);
v___x_5556_ = v___x_5554_;
v_isShared_5557_ = v_isSharedCheck_5566_;
goto v_resetjp_5555_;
}
else
{
lean_dec(v___x_5554_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5566_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5561_; 
v___x_5558_ = lean_box(v___x_5488_);
v___x_5559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5558_);
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 1, v_snd_5490_);
lean_ctor_set(v___x_5509_, 0, v___x_5559_);
v___x_5561_ = v___x_5509_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v_snd_5490_);
v___x_5561_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___x_5563_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 0, v___x_5561_);
v___x_5563_ = v___x_5556_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5561_);
v___x_5563_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
return v___x_5563_;
}
}
}
}
else
{
lean_object* v_a_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5575_; 
lean_del_object(v___x_5509_);
lean_dec(v_snd_5490_);
v_a_5568_ = lean_ctor_get(v___x_5554_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5570_ = v___x_5554_;
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_a_5568_);
lean_dec(v___x_5554_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5573_; 
if (v_isShared_5571_ == 0)
{
v___x_5573_ = v___x_5570_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
return v___x_5573_;
}
}
}
}
}
else
{
lean_object* v_a_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5583_; 
lean_del_object(v___x_5513_);
lean_del_object(v___x_5509_);
lean_dec(v_snd_5490_);
lean_dec(v_a_5450_);
lean_dec_ref(v_config_5449_);
lean_dec_ref(v_methods_5448_);
v_a_5576_ = lean_ctor_get(v___x_5516_, 0);
v_isSharedCheck_5583_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5583_ == 0)
{
v___x_5578_ = v___x_5516_;
v_isShared_5579_ = v_isSharedCheck_5583_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_a_5576_);
lean_dec(v___x_5516_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5583_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5581_; 
if (v_isShared_5579_ == 0)
{
v___x_5581_ = v___x_5578_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_a_5576_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
return v___x_5581_;
}
}
}
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
lean_dec(v_snd_5490_);
lean_dec(v_a_5450_);
lean_dec_ref(v_config_5449_);
lean_dec_ref(v_methods_5448_);
v_a_5587_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___x_5504_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v___x_5504_);
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
v___jp_5465_:
{
if (lean_obj_tag(v___y_5466_) == 0)
{
lean_object* v_a_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5479_; 
v_a_5467_ = lean_ctor_get(v___y_5466_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___y_5466_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5469_ = v___y_5466_;
v_isShared_5470_ = v_isSharedCheck_5479_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_a_5467_);
lean_dec(v___y_5466_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5479_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
if (lean_obj_tag(v_a_5467_) == 0)
{
lean_object* v_a_5471_; lean_object* v___x_5473_; 
lean_dec(v_a_5450_);
lean_dec_ref(v_config_5449_);
lean_dec_ref(v_methods_5448_);
v_a_5471_ = lean_ctor_get(v_a_5467_, 0);
lean_inc(v_a_5471_);
lean_dec_ref_known(v_a_5467_, 1);
if (v_isShared_5470_ == 0)
{
lean_ctor_set(v___x_5469_, 0, v_a_5471_);
v___x_5473_ = v___x_5469_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5471_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; 
lean_del_object(v___x_5469_);
v_a_5475_ = lean_ctor_get(v_a_5467_, 0);
lean_inc(v_a_5475_);
lean_dec_ref_known(v_a_5467_, 1);
v___x_5476_ = lean_unsigned_to_nat(1u);
v___x_5477_ = lean_nat_add(v_a_5450_, v___x_5476_);
lean_dec(v_a_5450_);
v_a_5450_ = v___x_5477_;
v_b_5451_ = v_a_5475_;
goto _start;
}
}
}
else
{
lean_object* v_a_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5487_; 
lean_dec(v_a_5450_);
lean_dec_ref(v_config_5449_);
lean_dec_ref(v_methods_5448_);
v_a_5480_ = lean_ctor_get(v___y_5466_, 0);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___y_5466_);
if (v_isSharedCheck_5487_ == 0)
{
v___x_5482_ = v___y_5466_;
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_a_5480_);
lean_dec(v___y_5466_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5485_; 
if (v_isShared_5483_ == 0)
{
v___x_5485_ = v___x_5482_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_a_5480_);
v___x_5485_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
return v___x_5485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5598_ = _args[0];
lean_object* v___x_5599_ = _args[1];
lean_object* v_methods_5600_ = _args[2];
lean_object* v_config_5601_ = _args[3];
lean_object* v_a_5602_ = _args[4];
lean_object* v_b_5603_ = _args[5];
lean_object* v___y_5604_ = _args[6];
lean_object* v___y_5605_ = _args[7];
lean_object* v___y_5606_ = _args[8];
lean_object* v___y_5607_ = _args[9];
lean_object* v___y_5608_ = _args[10];
lean_object* v___y_5609_ = _args[11];
lean_object* v___y_5610_ = _args[12];
lean_object* v___y_5611_ = _args[13];
lean_object* v___y_5612_ = _args[14];
lean_object* v___y_5613_ = _args[15];
lean_object* v___y_5614_ = _args[16];
lean_object* v___y_5615_ = _args[17];
lean_object* v___y_5616_ = _args[18];
_start:
{
lean_object* v_res_5617_; 
v_res_5617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5598_, v___x_5599_, v_methods_5600_, v_config_5601_, v_a_5602_, v_b_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
lean_dec(v___y_5611_);
lean_dec_ref(v___y_5610_);
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5608_);
lean_dec(v___y_5607_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec(v___y_5604_);
lean_dec_ref(v___x_5599_);
lean_dec(v_upperBound_5598_);
return v_res_5617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5618_, lean_object* v_config_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_){
_start:
{
lean_object* v___x_5633_; lean_object* v_hypotheses_5634_; lean_object* v___x_5635_; lean_object* v_newHyps_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; 
v___x_5633_ = lean_st_ref_get(v_a_5622_);
v_hypotheses_5634_ = lean_ctor_get(v___x_5633_, 3);
lean_inc_ref(v_hypotheses_5634_);
lean_dec(v___x_5633_);
v___x_5635_ = lean_array_get_size(v_hypotheses_5634_);
v_newHyps_5636_ = lean_mk_empty_array_with_capacity(v___x_5635_);
v___x_5637_ = lean_unsigned_to_nat(0u);
v___x_5638_ = lean_box(0);
v___x_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5639_, 0, v___x_5638_);
lean_ctor_set(v___x_5639_, 1, v_newHyps_5636_);
v___x_5640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5635_, v_hypotheses_5634_, v_methods_5618_, v_config_5619_, v___x_5637_, v___x_5639_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
lean_dec_ref(v_hypotheses_5634_);
if (lean_obj_tag(v___x_5640_) == 0)
{
lean_object* v_a_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5670_; 
v_a_5641_ = lean_ctor_get(v___x_5640_, 0);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5640_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5643_ = v___x_5640_;
v_isShared_5644_ = v_isSharedCheck_5670_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_a_5641_);
lean_dec(v___x_5640_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5670_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v_fst_5645_; 
v_fst_5645_ = lean_ctor_get(v_a_5641_, 0);
if (lean_obj_tag(v_fst_5645_) == 0)
{
lean_object* v_snd_5646_; lean_object* v___x_5647_; lean_object* v_caches_5648_; lean_object* v_typeAnalysis_5649_; lean_object* v_target_5650_; uint8_t v_didChange_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5664_; 
v_snd_5646_ = lean_ctor_get(v_a_5641_, 1);
lean_inc(v_snd_5646_);
lean_dec(v_a_5641_);
v___x_5647_ = lean_st_ref_take(v_a_5622_);
v_caches_5648_ = lean_ctor_get(v___x_5647_, 0);
v_typeAnalysis_5649_ = lean_ctor_get(v___x_5647_, 1);
v_target_5650_ = lean_ctor_get(v___x_5647_, 2);
v_didChange_5651_ = lean_ctor_get_uint8(v___x_5647_, sizeof(void*)*4);
v_isSharedCheck_5664_ = !lean_is_exclusive(v___x_5647_);
if (v_isSharedCheck_5664_ == 0)
{
lean_object* v_unused_5665_; 
v_unused_5665_ = lean_ctor_get(v___x_5647_, 3);
lean_dec(v_unused_5665_);
v___x_5653_ = v___x_5647_;
v_isShared_5654_ = v_isSharedCheck_5664_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_target_5650_);
lean_inc(v_typeAnalysis_5649_);
lean_inc(v_caches_5648_);
lean_dec(v___x_5647_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5664_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
lean_ctor_set(v___x_5653_, 3, v_snd_5646_);
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_caches_5648_);
lean_ctor_set(v_reuseFailAlloc_5663_, 1, v_typeAnalysis_5649_);
lean_ctor_set(v_reuseFailAlloc_5663_, 2, v_target_5650_);
lean_ctor_set(v_reuseFailAlloc_5663_, 3, v_snd_5646_);
lean_ctor_set_uint8(v_reuseFailAlloc_5663_, sizeof(void*)*4, v_didChange_5651_);
v___x_5656_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5657_; uint8_t v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5661_; 
v___x_5657_ = lean_st_ref_put(v_a_5622_, v___x_5656_);
v___x_5658_ = 0;
v___x_5659_ = lean_box(v___x_5658_);
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 0, v___x_5659_);
v___x_5661_ = v___x_5643_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v___x_5659_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
else
{
lean_object* v_val_5666_; lean_object* v___x_5668_; 
lean_inc_ref(v_fst_5645_);
lean_dec(v_a_5641_);
v_val_5666_ = lean_ctor_get(v_fst_5645_, 0);
lean_inc(v_val_5666_);
lean_dec_ref_known(v_fst_5645_, 1);
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 0, v_val_5666_);
v___x_5668_ = v___x_5643_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_val_5666_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
}
else
{
lean_object* v_a_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5678_; 
v_a_5671_ = lean_ctor_get(v___x_5640_, 0);
v_isSharedCheck_5678_ = !lean_is_exclusive(v___x_5640_);
if (v_isSharedCheck_5678_ == 0)
{
v___x_5673_ = v___x_5640_;
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_a_5671_);
lean_dec(v___x_5640_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v___x_5676_; 
if (v_isShared_5674_ == 0)
{
v___x_5676_ = v___x_5673_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5671_);
v___x_5676_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
return v___x_5676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5679_, lean_object* v_config_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_){
_start:
{
lean_object* v_res_5694_; 
v_res_5694_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5679_, v_config_5680_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_, v_a_5692_);
lean_dec(v_a_5692_);
lean_dec_ref(v_a_5691_);
lean_dec(v_a_5690_);
lean_dec_ref(v_a_5689_);
lean_dec(v_a_5688_);
lean_dec_ref(v_a_5687_);
lean_dec(v_a_5686_);
lean_dec_ref(v_a_5685_);
lean_dec(v_a_5684_);
lean_dec(v_a_5683_);
lean_dec_ref(v_a_5682_);
lean_dec(v_a_5681_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5695_, lean_object* v_msg_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_){
_start:
{
lean_object* v___x_5710_; 
v___x_5710_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5695_, v_msg_5696_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
return v___x_5710_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5711_, lean_object* v_msg_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
lean_object* v_res_5726_; 
v_res_5726_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5711_, v_msg_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec(v___y_5716_);
lean_dec(v___y_5715_);
lean_dec_ref(v___y_5714_);
lean_dec(v___y_5713_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5727_, lean_object* v___x_5728_, lean_object* v_methods_5729_, lean_object* v_config_5730_, lean_object* v_inst_5731_, lean_object* v_R_5732_, lean_object* v_a_5733_, lean_object* v_b_5734_, lean_object* v_c_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_){
_start:
{
lean_object* v___x_5749_; 
v___x_5749_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5727_, v___x_5728_, v_methods_5729_, v_config_5730_, v_a_5733_, v_b_5734_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
return v___x_5749_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5750_ = _args[0];
lean_object* v___x_5751_ = _args[1];
lean_object* v_methods_5752_ = _args[2];
lean_object* v_config_5753_ = _args[3];
lean_object* v_inst_5754_ = _args[4];
lean_object* v_R_5755_ = _args[5];
lean_object* v_a_5756_ = _args[6];
lean_object* v_b_5757_ = _args[7];
lean_object* v_c_5758_ = _args[8];
lean_object* v___y_5759_ = _args[9];
lean_object* v___y_5760_ = _args[10];
lean_object* v___y_5761_ = _args[11];
lean_object* v___y_5762_ = _args[12];
lean_object* v___y_5763_ = _args[13];
lean_object* v___y_5764_ = _args[14];
lean_object* v___y_5765_ = _args[15];
lean_object* v___y_5766_ = _args[16];
lean_object* v___y_5767_ = _args[17];
lean_object* v___y_5768_ = _args[18];
lean_object* v___y_5769_ = _args[19];
lean_object* v___y_5770_ = _args[20];
lean_object* v___y_5771_ = _args[21];
_start:
{
lean_object* v_res_5772_; 
v_res_5772_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5750_, v___x_5751_, v_methods_5752_, v_config_5753_, v_inst_5754_, v_R_5755_, v_a_5756_, v_b_5757_, v_c_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
lean_dec(v___y_5766_);
lean_dec_ref(v___y_5765_);
lean_dec(v___y_5764_);
lean_dec_ref(v___y_5763_);
lean_dec(v___y_5762_);
lean_dec(v___y_5761_);
lean_dec_ref(v___y_5760_);
lean_dec(v___y_5759_);
lean_dec_ref(v___x_5751_);
lean_dec(v_upperBound_5750_);
return v_res_5772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5773_, lean_object* v_config_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_){
_start:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; 
v___x_5787_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5788_ = lean_st_mk_ref(v___x_5787_);
v___x_5789_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5773_, v_config_5774_, v___x_5788_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_);
if (lean_obj_tag(v___x_5789_) == 0)
{
lean_object* v_a_5790_; lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5798_; 
v_a_5790_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5798_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5792_ = v___x_5789_;
v_isShared_5793_ = v_isSharedCheck_5798_;
goto v_resetjp_5791_;
}
else
{
lean_inc(v_a_5790_);
lean_dec(v___x_5789_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5798_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
lean_object* v___x_5794_; lean_object* v___x_5796_; 
v___x_5794_ = lean_st_ref_get(v___x_5788_);
lean_dec(v___x_5788_);
lean_dec(v___x_5794_);
if (v_isShared_5793_ == 0)
{
v___x_5796_ = v___x_5792_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_a_5790_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
return v___x_5796_;
}
}
}
else
{
lean_dec(v___x_5788_);
return v___x_5789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5799_, lean_object* v_config_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_){
_start:
{
lean_object* v_res_5813_; 
v_res_5813_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5799_, v_config_5800_, v_a_5801_, v_a_5802_, v_a_5803_, v_a_5804_, v_a_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_);
lean_dec(v_a_5811_);
lean_dec_ref(v_a_5810_);
lean_dec(v_a_5809_);
lean_dec_ref(v_a_5808_);
lean_dec(v_a_5807_);
lean_dec_ref(v_a_5806_);
lean_dec(v_a_5805_);
lean_dec_ref(v_a_5804_);
lean_dec(v_a_5803_);
lean_dec(v_a_5802_);
lean_dec_ref(v_a_5801_);
return v_res_5813_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5815_; lean_object* v___x_5816_; 
v___x_5815_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
return v___x_5816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5817_, lean_object* v_x_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_){
_start:
{
lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5831_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5832_ = l_Lean_MessageData_ofName(v_name_5817_);
v___x_5833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5833_, 0, v___x_5831_);
lean_ctor_set(v___x_5833_, 1, v___x_5832_);
v___x_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5833_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5835_, lean_object* v_x_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_){
_start:
{
lean_object* v_res_5849_; 
v_res_5849_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5835_, v_x_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
lean_dec(v___y_5845_);
lean_dec_ref(v___y_5844_);
lean_dec(v___y_5843_);
lean_dec_ref(v___y_5842_);
lean_dec(v___y_5841_);
lean_dec_ref(v___y_5840_);
lean_dec(v___y_5839_);
lean_dec(v___y_5838_);
lean_dec_ref(v___y_5837_);
lean_dec_ref(v_x_5836_);
return v_res_5849_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5850_; 
v___x_5850_ = l_instMonadExceptOfEIO___redArg();
return v___x_5850_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5852_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5851_);
return v___x_5852_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5853_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5854_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5853_);
return v___x_5854_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5855_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5856_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5855_);
return v___x_5856_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5857_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5858_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5857_);
return v___x_5858_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5859_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5860_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5859_);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5861_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5862_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5861_);
return v___x_5862_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5863_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5864_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5863_);
return v___x_5864_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5866_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5865_);
return v___x_5866_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5867_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5868_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5867_);
return v___x_5868_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5869_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5870_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5869_);
return v___x_5870_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5871_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5872_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5871_);
return v___x_5872_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5874_; double v___x_5875_; 
v___x_5874_ = lean_unsigned_to_nat(1000000000u);
v___x_5875_ = lean_float_of_nat(v___x_5874_);
return v___x_5875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5876_, lean_object* v_a_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_){
_start:
{
lean_object* v___x_5889_; lean_object* v_toApplicative_5890_; lean_object* v_toFunctor_5891_; lean_object* v_toSeq_5892_; lean_object* v_toSeqLeft_5893_; lean_object* v_toSeqRight_5894_; lean_object* v___f_5895_; lean_object* v___f_5896_; lean_object* v___f_5897_; lean_object* v___f_5898_; lean_object* v___x_5899_; lean_object* v___f_5900_; lean_object* v___f_5901_; lean_object* v___f_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v_toApplicative_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_6049_; 
v___x_5889_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5890_ = lean_ctor_get(v___x_5889_, 0);
v_toFunctor_5891_ = lean_ctor_get(v_toApplicative_5890_, 0);
v_toSeq_5892_ = lean_ctor_get(v_toApplicative_5890_, 2);
v_toSeqLeft_5893_ = lean_ctor_get(v_toApplicative_5890_, 3);
v_toSeqRight_5894_ = lean_ctor_get(v_toApplicative_5890_, 4);
v___f_5895_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5896_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5891_, 2);
v___f_5897_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5897_, 0, v_toFunctor_5891_);
v___f_5898_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5898_, 0, v_toFunctor_5891_);
v___x_5899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___f_5897_);
lean_ctor_set(v___x_5899_, 1, v___f_5898_);
lean_inc(v_toSeqRight_5894_);
v___f_5900_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5900_, 0, v_toSeqRight_5894_);
lean_inc(v_toSeqLeft_5893_);
v___f_5901_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5901_, 0, v_toSeqLeft_5893_);
lean_inc(v_toSeq_5892_);
v___f_5902_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5902_, 0, v_toSeq_5892_);
v___x_5903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5899_);
lean_ctor_set(v___x_5903_, 1, v___f_5895_);
lean_ctor_set(v___x_5903_, 2, v___f_5902_);
lean_ctor_set(v___x_5903_, 3, v___f_5901_);
lean_ctor_set(v___x_5903_, 4, v___f_5900_);
v___x_5904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5903_);
lean_ctor_set(v___x_5904_, 1, v___f_5896_);
v___x_5905_ = l_StateRefT_x27_instMonad___redArg(v___x_5904_);
v_toApplicative_5906_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_6049_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_6049_ == 0)
{
lean_object* v_unused_6050_; 
v_unused_6050_ = lean_ctor_get(v___x_5905_, 1);
lean_dec(v_unused_6050_);
v___x_5908_ = v___x_5905_;
v_isShared_5909_ = v_isSharedCheck_6049_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_toApplicative_5906_);
lean_dec(v___x_5905_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_6049_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
lean_object* v_toFunctor_5910_; lean_object* v_toSeq_5911_; lean_object* v_toSeqLeft_5912_; lean_object* v_toSeqRight_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_6047_; 
v_toFunctor_5910_ = lean_ctor_get(v_toApplicative_5906_, 0);
v_toSeq_5911_ = lean_ctor_get(v_toApplicative_5906_, 2);
v_toSeqLeft_5912_ = lean_ctor_get(v_toApplicative_5906_, 3);
v_toSeqRight_5913_ = lean_ctor_get(v_toApplicative_5906_, 4);
v_isSharedCheck_6047_ = !lean_is_exclusive(v_toApplicative_5906_);
if (v_isSharedCheck_6047_ == 0)
{
lean_object* v_unused_6048_; 
v_unused_6048_ = lean_ctor_get(v_toApplicative_5906_, 1);
lean_dec(v_unused_6048_);
v___x_5915_ = v_toApplicative_5906_;
v_isShared_5916_ = v_isSharedCheck_6047_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_toSeqRight_5913_);
lean_inc(v_toSeqLeft_5912_);
lean_inc(v_toSeq_5911_);
lean_inc(v_toFunctor_5910_);
lean_dec(v_toApplicative_5906_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_6047_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v___f_5917_; lean_object* v___f_5918_; lean_object* v___f_5919_; lean_object* v___f_5920_; lean_object* v___x_5921_; lean_object* v___f_5922_; lean_object* v___f_5923_; lean_object* v___f_5924_; lean_object* v___x_5926_; 
v___f_5917_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5918_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5910_);
v___f_5919_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5919_, 0, v_toFunctor_5910_);
v___f_5920_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5920_, 0, v_toFunctor_5910_);
v___x_5921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___f_5919_);
lean_ctor_set(v___x_5921_, 1, v___f_5920_);
v___f_5922_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5922_, 0, v_toSeqRight_5913_);
v___f_5923_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5923_, 0, v_toSeqLeft_5912_);
v___f_5924_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5924_, 0, v_toSeq_5911_);
if (v_isShared_5916_ == 0)
{
lean_ctor_set(v___x_5915_, 4, v___f_5922_);
lean_ctor_set(v___x_5915_, 3, v___f_5923_);
lean_ctor_set(v___x_5915_, 2, v___f_5924_);
lean_ctor_set(v___x_5915_, 1, v___f_5917_);
lean_ctor_set(v___x_5915_, 0, v___x_5921_);
v___x_5926_ = v___x_5915_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v___x_5921_);
lean_ctor_set(v_reuseFailAlloc_6046_, 1, v___f_5917_);
lean_ctor_set(v_reuseFailAlloc_6046_, 2, v___f_5924_);
lean_ctor_set(v_reuseFailAlloc_6046_, 3, v___f_5923_);
lean_ctor_set(v_reuseFailAlloc_6046_, 4, v___f_5922_);
v___x_5926_ = v_reuseFailAlloc_6046_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
lean_object* v___x_5928_; 
if (v_isShared_5909_ == 0)
{
lean_ctor_set(v___x_5908_, 1, v___f_5918_);
lean_ctor_set(v___x_5908_, 0, v___x_5926_);
v___x_5928_ = v___x_5908_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_6045_; 
v_reuseFailAlloc_6045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6045_, 0, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_6045_, 1, v___f_5918_);
v___x_5928_ = v_reuseFailAlloc_6045_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v_toMonadRef_5938_; lean_object* v___x_5939_; lean_object* v_name_5940_; lean_object* v_run_x27_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_6044_; 
v___x_5929_ = l_StateRefT_x27_instMonad___redArg(v___x_5928_);
v___x_5930_ = l_ReaderT_instMonad___redArg(v___x_5929_);
v___x_5931_ = l_StateRefT_x27_instMonad___redArg(v___x_5930_);
v___x_5932_ = l_ReaderT_instMonad___redArg(v___x_5931_);
v___x_5933_ = l_ReaderT_instMonad___redArg(v___x_5932_);
v___x_5934_ = l_StateRefT_x27_instMonad___redArg(v___x_5933_);
v___x_5935_ = l_ReaderT_instMonad___redArg(v___x_5934_);
v___x_5936_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5937_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_5938_ = lean_ctor_get(v___x_5937_, 0);
v___x_5939_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_name_5940_ = lean_ctor_get(v_pass_5876_, 0);
v_run_x27_5941_ = lean_ctor_get(v_pass_5876_, 1);
v_isSharedCheck_6044_ = !lean_is_exclusive(v_pass_5876_);
if (v_isSharedCheck_6044_ == 0)
{
v___x_5943_ = v_pass_5876_;
v_isShared_5944_ = v_isSharedCheck_6044_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_run_x27_5941_);
lean_inc(v_name_5940_);
lean_dec(v_pass_5876_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_6044_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
lean_object* v___x_5945_; lean_object* v_toCold_5946_; lean_object* v_options_5947_; uint8_t v_hasTrace_5948_; 
v___x_5945_ = l_Lean_KVMap_instValueBool;
v_toCold_5946_ = lean_ctor_get(v_a_5886_, 0);
v_options_5947_ = lean_ctor_get(v_toCold_5946_, 2);
v_hasTrace_5948_ = lean_ctor_get_uint8(v_options_5947_, sizeof(void*)*1);
if (v_hasTrace_5948_ == 0)
{
lean_object* v___x_5949_; 
lean_del_object(v___x_5943_);
lean_dec(v_name_5940_);
lean_dec_ref(v___x_5935_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc(v_a_5878_);
lean_inc_ref(v_a_5877_);
v___x_5949_ = lean_apply_12(v_run_x27_5941_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, lean_box(0));
return v___x_5949_;
}
else
{
lean_object* v_inheritedTraceOptions_5950_; lean_object* v___f_5951_; lean_object* v___f_5952_; lean_object* v___f_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; uint8_t v___x_5957_; lean_object* v___y_5959_; lean_object* v___y_5960_; lean_object* v_a_5961_; lean_object* v___y_5977_; lean_object* v___y_5978_; lean_object* v_a_5979_; 
v_inheritedTraceOptions_5950_ = lean_ctor_get(v_toCold_5946_, 11);
v___f_5951_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5951_, 0, v_name_5940_);
v___f_5952_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_5953_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5954_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5955_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5956_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5957_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5950_, v_options_5947_, v___x_5956_);
if (v___x_5957_ == 0)
{
lean_object* v___x_6040_; lean_object* v___x_6041_; uint8_t v___x_6042_; 
v___x_6040_ = l_Lean_trace_profiler;
v___x_6041_ = l_Lean_Option_get___redArg(v___x_5945_, v_options_5947_, v___x_6040_);
v___x_6042_ = lean_unbox(v___x_6041_);
lean_dec(v___x_6041_);
if (v___x_6042_ == 0)
{
lean_object* v___x_6043_; 
lean_dec_ref(v___f_5951_);
lean_del_object(v___x_5943_);
lean_dec_ref(v___x_5935_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc(v_a_5878_);
lean_inc_ref(v_a_5877_);
v___x_6043_ = lean_apply_12(v_run_x27_5941_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, lean_box(0));
return v___x_6043_;
}
else
{
goto v___jp_5989_;
}
}
else
{
goto v___jp_5989_;
}
v___jp_5958_:
{
lean_object* v___x_5962_; double v___x_5963_; double v___x_5964_; double v___x_5965_; double v___x_5966_; double v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5971_; 
v___x_5962_ = lean_io_mono_nanos_now();
v___x_5963_ = lean_float_of_nat(v___y_5959_);
v___x_5964_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5965_ = lean_float_div(v___x_5963_, v___x_5964_);
v___x_5966_ = lean_float_of_nat(v___x_5962_);
v___x_5967_ = lean_float_div(v___x_5966_, v___x_5964_);
v___x_5968_ = lean_box_float(v___x_5965_);
v___x_5969_ = lean_box_float(v___x_5967_);
if (v_isShared_5944_ == 0)
{
lean_ctor_set(v___x_5943_, 1, v___x_5969_);
lean_ctor_set(v___x_5943_, 0, v___x_5968_);
v___x_5971_ = v___x_5943_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v___x_5968_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v___x_5969_);
v___x_5971_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
lean_object* v___x_5972_; lean_object* v___x_28875__overap_5973_; lean_object* v___x_5974_; 
v___x_5972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5972_, 0, v_a_5961_);
lean_ctor_set(v___x_5972_, 1, v___x_5971_);
lean_inc_ref(v_toMonadRef_5938_);
v___x_28875__overap_5973_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5935_, v___x_5936_, v_toMonadRef_5938_, v___f_5952_, lean_box(0), v___x_5939_, v___f_5953_, v___x_5954_, v_hasTrace_5948_, v___x_5955_, v_options_5947_, v___x_5957_, v___y_5960_, v___f_5951_, v___x_5972_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc(v_a_5878_);
lean_inc_ref(v_a_5877_);
v___x_5974_ = lean_apply_12(v___x_28875__overap_5973_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, lean_box(0));
return v___x_5974_;
}
}
v___jp_5976_:
{
lean_object* v___x_5980_; double v___x_5981_; double v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_28896__overap_5987_; lean_object* v___x_5988_; 
v___x_5980_ = lean_io_get_num_heartbeats();
v___x_5981_ = lean_float_of_nat(v___y_5977_);
v___x_5982_ = lean_float_of_nat(v___x_5980_);
v___x_5983_ = lean_box_float(v___x_5981_);
v___x_5984_ = lean_box_float(v___x_5982_);
v___x_5985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5983_);
lean_ctor_set(v___x_5985_, 1, v___x_5984_);
v___x_5986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5986_, 0, v_a_5979_);
lean_ctor_set(v___x_5986_, 1, v___x_5985_);
lean_inc_ref(v_toMonadRef_5938_);
v___x_28896__overap_5987_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5935_, v___x_5936_, v_toMonadRef_5938_, v___f_5952_, lean_box(0), v___x_5939_, v___f_5953_, v___x_5954_, v_hasTrace_5948_, v___x_5955_, v_options_5947_, v___x_5957_, v___y_5978_, v___f_5951_, v___x_5986_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc(v_a_5878_);
lean_inc_ref(v_a_5877_);
v___x_5988_ = lean_apply_12(v___x_28896__overap_5987_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, lean_box(0));
return v___x_5988_;
}
v___jp_5989_:
{
lean_object* v___x_28853__overap_5990_; lean_object* v___x_5991_; 
lean_inc_ref(v___x_5935_);
v___x_28853__overap_5990_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5935_, v___x_5936_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc(v_a_5878_);
lean_inc_ref(v_a_5877_);
v___x_5991_ = lean_apply_12(v___x_28853__overap_5990_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, lean_box(0));
if (lean_obj_tag(v___x_5991_) == 0)
{
lean_object* v_a_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; uint8_t v___x_5995_; 
v_a_5992_ = lean_ctor_get(v___x_5991_, 0);
lean_inc(v_a_5992_);
lean_dec_ref_known(v___x_5991_, 1);
v___x_5993_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5994_ = l_Lean_Option_get___redArg(v___x_5945_, v_options_5947_, v___x_5993_);
v___x_5995_ = lean_unbox(v___x_5994_);
lean_dec(v___x_5994_);
if (v___x_5995_ == 0)
{
lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5996_ = lean_io_mono_nanos_now();
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc(v_a_5878_);
lean_inc_ref(v_a_5877_);
v___x_5997_ = lean_apply_12(v_run_x27_5941_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, lean_box(0));
if (lean_obj_tag(v___x_5997_) == 0)
{
lean_object* v_a_5998_; lean_object* v___x_6000_; uint8_t v_isShared_6001_; uint8_t v_isSharedCheck_6005_; 
v_a_5998_ = lean_ctor_get(v___x_5997_, 0);
v_isSharedCheck_6005_ = !lean_is_exclusive(v___x_5997_);
if (v_isSharedCheck_6005_ == 0)
{
v___x_6000_ = v___x_5997_;
v_isShared_6001_ = v_isSharedCheck_6005_;
goto v_resetjp_5999_;
}
else
{
lean_inc(v_a_5998_);
lean_dec(v___x_5997_);
v___x_6000_ = lean_box(0);
v_isShared_6001_ = v_isSharedCheck_6005_;
goto v_resetjp_5999_;
}
v_resetjp_5999_:
{
lean_object* v___x_6003_; 
if (v_isShared_6001_ == 0)
{
lean_ctor_set_tag(v___x_6000_, 1);
v___x_6003_ = v___x_6000_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_a_5998_);
v___x_6003_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
v___y_5959_ = v___x_5996_;
v___y_5960_ = v_a_5992_;
v_a_5961_ = v___x_6003_;
goto v___jp_5958_;
}
}
}
else
{
lean_object* v_a_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6013_; 
v_a_6006_ = lean_ctor_get(v___x_5997_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v___x_5997_);
if (v_isSharedCheck_6013_ == 0)
{
v___x_6008_ = v___x_5997_;
v_isShared_6009_ = v_isSharedCheck_6013_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_a_6006_);
lean_dec(v___x_5997_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6013_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6011_; 
if (v_isShared_6009_ == 0)
{
lean_ctor_set_tag(v___x_6008_, 0);
v___x_6011_ = v___x_6008_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v_a_6006_);
v___x_6011_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
v___y_5959_ = v___x_5996_;
v___y_5960_ = v_a_5992_;
v_a_5961_ = v___x_6011_;
goto v___jp_5958_;
}
}
}
}
else
{
lean_object* v___x_6014_; lean_object* v___x_6015_; 
lean_del_object(v___x_5943_);
v___x_6014_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc(v_a_5878_);
lean_inc_ref(v_a_5877_);
v___x_6015_ = lean_apply_12(v_run_x27_5941_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, lean_box(0));
if (lean_obj_tag(v___x_6015_) == 0)
{
lean_object* v_a_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6023_; 
v_a_6016_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6023_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6023_ == 0)
{
v___x_6018_ = v___x_6015_;
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_a_6016_);
lean_dec(v___x_6015_);
v___x_6018_ = lean_box(0);
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
v_resetjp_6017_:
{
lean_object* v___x_6021_; 
if (v_isShared_6019_ == 0)
{
lean_ctor_set_tag(v___x_6018_, 1);
v___x_6021_ = v___x_6018_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_a_6016_);
v___x_6021_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
v___y_5977_ = v___x_6014_;
v___y_5978_ = v_a_5992_;
v_a_5979_ = v___x_6021_;
goto v___jp_5976_;
}
}
}
else
{
lean_object* v_a_6024_; lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6031_; 
v_a_6024_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6031_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6031_ == 0)
{
v___x_6026_ = v___x_6015_;
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
else
{
lean_inc(v_a_6024_);
lean_dec(v___x_6015_);
v___x_6026_ = lean_box(0);
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
v_resetjp_6025_:
{
lean_object* v___x_6029_; 
if (v_isShared_6027_ == 0)
{
lean_ctor_set_tag(v___x_6026_, 0);
v___x_6029_ = v___x_6026_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6030_; 
v_reuseFailAlloc_6030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
v___x_6029_ = v_reuseFailAlloc_6030_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
v___y_5977_ = v___x_6014_;
v___y_5978_ = v_a_5992_;
v_a_5979_ = v___x_6029_;
goto v___jp_5976_;
}
}
}
}
}
else
{
lean_object* v_a_6032_; lean_object* v___x_6034_; uint8_t v_isShared_6035_; uint8_t v_isSharedCheck_6039_; 
lean_dec_ref(v___f_5951_);
lean_del_object(v___x_5943_);
lean_dec_ref(v_run_x27_5941_);
lean_dec_ref(v___x_5935_);
v_a_6032_ = lean_ctor_get(v___x_5991_, 0);
v_isSharedCheck_6039_ = !lean_is_exclusive(v___x_5991_);
if (v_isSharedCheck_6039_ == 0)
{
v___x_6034_ = v___x_5991_;
v_isShared_6035_ = v_isSharedCheck_6039_;
goto v_resetjp_6033_;
}
else
{
lean_inc(v_a_6032_);
lean_dec(v___x_5991_);
v___x_6034_ = lean_box(0);
v_isShared_6035_ = v_isSharedCheck_6039_;
goto v_resetjp_6033_;
}
v_resetjp_6033_:
{
lean_object* v___x_6037_; 
if (v_isShared_6035_ == 0)
{
v___x_6037_ = v___x_6034_;
goto v_reusejp_6036_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_a_6032_);
v___x_6037_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6036_;
}
v_reusejp_6036_:
{
return v___x_6037_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_){
_start:
{
lean_object* v_res_6064_; 
v_res_6064_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6051_, v_a_6052_, v_a_6053_, v_a_6054_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_, v_a_6059_, v_a_6060_, v_a_6061_, v_a_6062_);
lean_dec(v_a_6062_);
lean_dec_ref(v_a_6061_);
lean_dec(v_a_6060_);
lean_dec_ref(v_a_6059_);
lean_dec(v_a_6058_);
lean_dec_ref(v_a_6057_);
lean_dec(v_a_6056_);
lean_dec_ref(v_a_6055_);
lean_dec(v_a_6054_);
lean_dec(v_a_6053_);
lean_dec_ref(v_a_6052_);
return v_res_6064_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; 
v___x_6065_ = lean_unsigned_to_nat(32u);
v___x_6066_ = lean_mk_empty_array_with_capacity(v___x_6065_);
v___x_6067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
return v___x_6067_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6068_ = ((size_t)5ULL);
v___x_6069_ = lean_unsigned_to_nat(0u);
v___x_6070_ = lean_unsigned_to_nat(32u);
v___x_6071_ = lean_mk_empty_array_with_capacity(v___x_6070_);
v___x_6072_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6073_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
lean_ctor_set(v___x_6073_, 1, v___x_6071_);
lean_ctor_set(v___x_6073_, 2, v___x_6069_);
lean_ctor_set(v___x_6073_, 3, v___x_6069_);
lean_ctor_set_usize(v___x_6073_, 4, v___x_6068_);
return v___x_6073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6074_){
_start:
{
lean_object* v___x_6076_; lean_object* v_traceState_6077_; lean_object* v_traces_6078_; lean_object* v___x_6079_; lean_object* v_traceState_6080_; lean_object* v_env_6081_; lean_object* v_nextMacroScope_6082_; lean_object* v_ngen_6083_; lean_object* v_auxDeclNGen_6084_; lean_object* v_cache_6085_; lean_object* v_recordedDeps_6086_; lean_object* v_messages_6087_; lean_object* v_infoState_6088_; lean_object* v_snapshotTasks_6089_; lean_object* v___x_6091_; uint8_t v_isShared_6092_; uint8_t v_isSharedCheck_6108_; 
v___x_6076_ = lean_st_ref_get(v___y_6074_);
v_traceState_6077_ = lean_ctor_get(v___x_6076_, 4);
lean_inc_ref(v_traceState_6077_);
lean_dec(v___x_6076_);
v_traces_6078_ = lean_ctor_get(v_traceState_6077_, 0);
lean_inc_ref(v_traces_6078_);
lean_dec_ref(v_traceState_6077_);
v___x_6079_ = lean_st_ref_take(v___y_6074_);
v_traceState_6080_ = lean_ctor_get(v___x_6079_, 4);
v_env_6081_ = lean_ctor_get(v___x_6079_, 0);
v_nextMacroScope_6082_ = lean_ctor_get(v___x_6079_, 1);
v_ngen_6083_ = lean_ctor_get(v___x_6079_, 2);
v_auxDeclNGen_6084_ = lean_ctor_get(v___x_6079_, 3);
v_cache_6085_ = lean_ctor_get(v___x_6079_, 5);
v_recordedDeps_6086_ = lean_ctor_get(v___x_6079_, 6);
v_messages_6087_ = lean_ctor_get(v___x_6079_, 7);
v_infoState_6088_ = lean_ctor_get(v___x_6079_, 8);
v_snapshotTasks_6089_ = lean_ctor_get(v___x_6079_, 9);
v_isSharedCheck_6108_ = !lean_is_exclusive(v___x_6079_);
if (v_isSharedCheck_6108_ == 0)
{
v___x_6091_ = v___x_6079_;
v_isShared_6092_ = v_isSharedCheck_6108_;
goto v_resetjp_6090_;
}
else
{
lean_inc(v_snapshotTasks_6089_);
lean_inc(v_infoState_6088_);
lean_inc(v_messages_6087_);
lean_inc(v_recordedDeps_6086_);
lean_inc(v_cache_6085_);
lean_inc(v_traceState_6080_);
lean_inc(v_auxDeclNGen_6084_);
lean_inc(v_ngen_6083_);
lean_inc(v_nextMacroScope_6082_);
lean_inc(v_env_6081_);
lean_dec(v___x_6079_);
v___x_6091_ = lean_box(0);
v_isShared_6092_ = v_isSharedCheck_6108_;
goto v_resetjp_6090_;
}
v_resetjp_6090_:
{
uint64_t v_tid_6093_; lean_object* v___x_6095_; uint8_t v_isShared_6096_; uint8_t v_isSharedCheck_6106_; 
v_tid_6093_ = lean_ctor_get_uint64(v_traceState_6080_, sizeof(void*)*1);
v_isSharedCheck_6106_ = !lean_is_exclusive(v_traceState_6080_);
if (v_isSharedCheck_6106_ == 0)
{
lean_object* v_unused_6107_; 
v_unused_6107_ = lean_ctor_get(v_traceState_6080_, 0);
lean_dec(v_unused_6107_);
v___x_6095_ = v_traceState_6080_;
v_isShared_6096_ = v_isSharedCheck_6106_;
goto v_resetjp_6094_;
}
else
{
lean_dec(v_traceState_6080_);
v___x_6095_ = lean_box(0);
v_isShared_6096_ = v_isSharedCheck_6106_;
goto v_resetjp_6094_;
}
v_resetjp_6094_:
{
lean_object* v___x_6097_; lean_object* v___x_6099_; 
v___x_6097_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6096_ == 0)
{
lean_ctor_set(v___x_6095_, 0, v___x_6097_);
v___x_6099_ = v___x_6095_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6097_);
lean_ctor_set_uint64(v_reuseFailAlloc_6105_, sizeof(void*)*1, v_tid_6093_);
v___x_6099_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
lean_object* v___x_6101_; 
if (v_isShared_6092_ == 0)
{
lean_ctor_set(v___x_6091_, 4, v___x_6099_);
v___x_6101_ = v___x_6091_;
goto v_reusejp_6100_;
}
else
{
lean_object* v_reuseFailAlloc_6104_; 
v_reuseFailAlloc_6104_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6104_, 0, v_env_6081_);
lean_ctor_set(v_reuseFailAlloc_6104_, 1, v_nextMacroScope_6082_);
lean_ctor_set(v_reuseFailAlloc_6104_, 2, v_ngen_6083_);
lean_ctor_set(v_reuseFailAlloc_6104_, 3, v_auxDeclNGen_6084_);
lean_ctor_set(v_reuseFailAlloc_6104_, 4, v___x_6099_);
lean_ctor_set(v_reuseFailAlloc_6104_, 5, v_cache_6085_);
lean_ctor_set(v_reuseFailAlloc_6104_, 6, v_recordedDeps_6086_);
lean_ctor_set(v_reuseFailAlloc_6104_, 7, v_messages_6087_);
lean_ctor_set(v_reuseFailAlloc_6104_, 8, v_infoState_6088_);
lean_ctor_set(v_reuseFailAlloc_6104_, 9, v_snapshotTasks_6089_);
v___x_6101_ = v_reuseFailAlloc_6104_;
goto v_reusejp_6100_;
}
v_reusejp_6100_:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6102_ = lean_st_ref_put(v___y_6074_, v___x_6101_);
v___x_6103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6103_, 0, v_traces_6078_);
return v___x_6103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6109_, lean_object* v___y_6110_){
_start:
{
lean_object* v_res_6111_; 
v_res_6111_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6109_);
lean_dec(v___y_6109_);
return v_res_6111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_){
_start:
{
lean_object* v___x_6124_; 
v___x_6124_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6122_);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_){
_start:
{
lean_object* v_res_6137_; 
v_res_6137_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
lean_dec(v___y_6131_);
lean_dec_ref(v___y_6130_);
lean_dec(v___y_6129_);
lean_dec_ref(v___y_6128_);
lean_dec(v___y_6127_);
lean_dec(v___y_6126_);
lean_dec_ref(v___y_6125_);
return v_res_6137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6138_, lean_object* v_opt_6139_){
_start:
{
lean_object* v_name_6140_; lean_object* v_defValue_6141_; lean_object* v_map_6142_; lean_object* v___x_6143_; 
v_name_6140_ = lean_ctor_get(v_opt_6139_, 0);
v_defValue_6141_ = lean_ctor_get(v_opt_6139_, 1);
v_map_6142_ = lean_ctor_get(v_opts_6138_, 0);
v___x_6143_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6142_, v_name_6140_);
if (lean_obj_tag(v___x_6143_) == 0)
{
uint8_t v___x_6144_; 
v___x_6144_ = lean_unbox(v_defValue_6141_);
return v___x_6144_;
}
else
{
lean_object* v_val_6145_; 
v_val_6145_ = lean_ctor_get(v___x_6143_, 0);
lean_inc(v_val_6145_);
lean_dec_ref_known(v___x_6143_, 1);
if (lean_obj_tag(v_val_6145_) == 1)
{
uint8_t v_v_6146_; 
v_v_6146_ = lean_ctor_get_uint8(v_val_6145_, 0);
lean_dec_ref_known(v_val_6145_, 0);
return v_v_6146_;
}
else
{
uint8_t v___x_6147_; 
lean_dec(v_val_6145_);
v___x_6147_ = lean_unbox(v_defValue_6141_);
return v___x_6147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6148_, lean_object* v_opt_6149_){
_start:
{
uint8_t v_res_6150_; lean_object* v_r_6151_; 
v_res_6150_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6148_, v_opt_6149_);
lean_dec_ref(v_opt_6149_);
lean_dec_ref(v_opts_6148_);
v_r_6151_ = lean_box(v_res_6150_);
return v_r_6151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6152_, lean_object* v_msg_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
lean_object* v_ref_6159_; lean_object* v___x_6160_; lean_object* v_a_6161_; lean_object* v___x_6163_; uint8_t v_isShared_6164_; uint8_t v_isSharedCheck_6206_; 
v_ref_6159_ = lean_ctor_get(v___y_6156_, 2);
v___x_6160_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
v_a_6161_ = lean_ctor_get(v___x_6160_, 0);
v_isSharedCheck_6206_ = !lean_is_exclusive(v___x_6160_);
if (v_isSharedCheck_6206_ == 0)
{
v___x_6163_ = v___x_6160_;
v_isShared_6164_ = v_isSharedCheck_6206_;
goto v_resetjp_6162_;
}
else
{
lean_inc(v_a_6161_);
lean_dec(v___x_6160_);
v___x_6163_ = lean_box(0);
v_isShared_6164_ = v_isSharedCheck_6206_;
goto v_resetjp_6162_;
}
v_resetjp_6162_:
{
lean_object* v___x_6165_; lean_object* v_traceState_6166_; lean_object* v_env_6167_; lean_object* v_nextMacroScope_6168_; lean_object* v_ngen_6169_; lean_object* v_auxDeclNGen_6170_; lean_object* v_cache_6171_; lean_object* v_recordedDeps_6172_; lean_object* v_messages_6173_; lean_object* v_infoState_6174_; lean_object* v_snapshotTasks_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6205_; 
v___x_6165_ = lean_st_ref_take(v___y_6157_);
v_traceState_6166_ = lean_ctor_get(v___x_6165_, 4);
v_env_6167_ = lean_ctor_get(v___x_6165_, 0);
v_nextMacroScope_6168_ = lean_ctor_get(v___x_6165_, 1);
v_ngen_6169_ = lean_ctor_get(v___x_6165_, 2);
v_auxDeclNGen_6170_ = lean_ctor_get(v___x_6165_, 3);
v_cache_6171_ = lean_ctor_get(v___x_6165_, 5);
v_recordedDeps_6172_ = lean_ctor_get(v___x_6165_, 6);
v_messages_6173_ = lean_ctor_get(v___x_6165_, 7);
v_infoState_6174_ = lean_ctor_get(v___x_6165_, 8);
v_snapshotTasks_6175_ = lean_ctor_get(v___x_6165_, 9);
v_isSharedCheck_6205_ = !lean_is_exclusive(v___x_6165_);
if (v_isSharedCheck_6205_ == 0)
{
v___x_6177_ = v___x_6165_;
v_isShared_6178_ = v_isSharedCheck_6205_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_snapshotTasks_6175_);
lean_inc(v_infoState_6174_);
lean_inc(v_messages_6173_);
lean_inc(v_recordedDeps_6172_);
lean_inc(v_cache_6171_);
lean_inc(v_traceState_6166_);
lean_inc(v_auxDeclNGen_6170_);
lean_inc(v_ngen_6169_);
lean_inc(v_nextMacroScope_6168_);
lean_inc(v_env_6167_);
lean_dec(v___x_6165_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6205_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
uint64_t v_tid_6179_; lean_object* v_traces_6180_; lean_object* v___x_6182_; uint8_t v_isShared_6183_; uint8_t v_isSharedCheck_6204_; 
v_tid_6179_ = lean_ctor_get_uint64(v_traceState_6166_, sizeof(void*)*1);
v_traces_6180_ = lean_ctor_get(v_traceState_6166_, 0);
v_isSharedCheck_6204_ = !lean_is_exclusive(v_traceState_6166_);
if (v_isSharedCheck_6204_ == 0)
{
v___x_6182_ = v_traceState_6166_;
v_isShared_6183_ = v_isSharedCheck_6204_;
goto v_resetjp_6181_;
}
else
{
lean_inc(v_traces_6180_);
lean_dec(v_traceState_6166_);
v___x_6182_ = lean_box(0);
v_isShared_6183_ = v_isSharedCheck_6204_;
goto v_resetjp_6181_;
}
v_resetjp_6181_:
{
lean_object* v___x_6184_; lean_object* v___x_6185_; double v___x_6186_; uint8_t v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6195_; 
v___x_6184_ = lean_box(0);
v___x_6185_ = lean_box(0);
v___x_6186_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6187_ = 0;
v___x_6188_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6189_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6189_, 0, v_cls_6152_);
lean_ctor_set(v___x_6189_, 1, v___x_6185_);
lean_ctor_set(v___x_6189_, 2, v___x_6188_);
lean_ctor_set_float(v___x_6189_, sizeof(void*)*3, v___x_6186_);
lean_ctor_set_float(v___x_6189_, sizeof(void*)*3 + 8, v___x_6186_);
lean_ctor_set_uint8(v___x_6189_, sizeof(void*)*3 + 16, v___x_6187_);
v___x_6190_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6191_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6191_, 0, v___x_6189_);
lean_ctor_set(v___x_6191_, 1, v_a_6161_);
lean_ctor_set(v___x_6191_, 2, v___x_6190_);
lean_inc(v_ref_6159_);
v___x_6192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6192_, 0, v_ref_6159_);
lean_ctor_set(v___x_6192_, 1, v___x_6191_);
v___x_6193_ = l_Lean_PersistentArray_push___redArg(v_traces_6180_, v___x_6192_);
if (v_isShared_6183_ == 0)
{
lean_ctor_set(v___x_6182_, 0, v___x_6193_);
v___x_6195_ = v___x_6182_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6203_; 
v_reuseFailAlloc_6203_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6203_, 0, v___x_6193_);
lean_ctor_set_uint64(v_reuseFailAlloc_6203_, sizeof(void*)*1, v_tid_6179_);
v___x_6195_ = v_reuseFailAlloc_6203_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
lean_object* v___x_6197_; 
if (v_isShared_6178_ == 0)
{
lean_ctor_set(v___x_6177_, 4, v___x_6195_);
v___x_6197_ = v___x_6177_;
goto v_reusejp_6196_;
}
else
{
lean_object* v_reuseFailAlloc_6202_; 
v_reuseFailAlloc_6202_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6202_, 0, v_env_6167_);
lean_ctor_set(v_reuseFailAlloc_6202_, 1, v_nextMacroScope_6168_);
lean_ctor_set(v_reuseFailAlloc_6202_, 2, v_ngen_6169_);
lean_ctor_set(v_reuseFailAlloc_6202_, 3, v_auxDeclNGen_6170_);
lean_ctor_set(v_reuseFailAlloc_6202_, 4, v___x_6195_);
lean_ctor_set(v_reuseFailAlloc_6202_, 5, v_cache_6171_);
lean_ctor_set(v_reuseFailAlloc_6202_, 6, v_recordedDeps_6172_);
lean_ctor_set(v_reuseFailAlloc_6202_, 7, v_messages_6173_);
lean_ctor_set(v_reuseFailAlloc_6202_, 8, v_infoState_6174_);
lean_ctor_set(v_reuseFailAlloc_6202_, 9, v_snapshotTasks_6175_);
v___x_6197_ = v_reuseFailAlloc_6202_;
goto v_reusejp_6196_;
}
v_reusejp_6196_:
{
lean_object* v___x_6198_; lean_object* v___x_6200_; 
v___x_6198_ = lean_st_ref_put(v___y_6157_, v___x_6197_);
if (v_isShared_6164_ == 0)
{
lean_ctor_set(v___x_6163_, 0, v___x_6184_);
v___x_6200_ = v___x_6163_;
goto v_reusejp_6199_;
}
else
{
lean_object* v_reuseFailAlloc_6201_; 
v_reuseFailAlloc_6201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6201_, 0, v___x_6184_);
v___x_6200_ = v_reuseFailAlloc_6201_;
goto v_reusejp_6199_;
}
v_reusejp_6199_:
{
return v___x_6200_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6207_, lean_object* v_msg_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_){
_start:
{
lean_object* v_res_6214_; 
v_res_6214_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6207_, v_msg_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
lean_dec(v___y_6212_);
lean_dec_ref(v___y_6211_);
lean_dec(v___y_6210_);
lean_dec_ref(v___y_6209_);
return v_res_6214_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6215_){
_start:
{
if (lean_obj_tag(v_e_6215_) == 0)
{
uint8_t v___x_6216_; 
v___x_6216_ = 2;
return v___x_6216_;
}
else
{
lean_object* v_a_6217_; uint8_t v___x_6218_; 
v_a_6217_ = lean_ctor_get(v_e_6215_, 0);
v___x_6218_ = lean_unbox(v_a_6217_);
if (v___x_6218_ == 0)
{
uint8_t v___x_6219_; 
v___x_6219_ = 1;
return v___x_6219_;
}
else
{
uint8_t v___x_6220_; 
v___x_6220_ = 0;
return v___x_6220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6221_){
_start:
{
uint8_t v_res_6222_; lean_object* v_r_6223_; 
v_res_6222_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6221_);
lean_dec_ref(v_e_6221_);
v_r_6223_ = lean_box(v_res_6222_);
return v_r_6223_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6224_){
_start:
{
if (lean_obj_tag(v_x_6224_) == 0)
{
lean_object* v_a_6226_; lean_object* v___x_6228_; uint8_t v_isShared_6229_; uint8_t v_isSharedCheck_6233_; 
v_a_6226_ = lean_ctor_get(v_x_6224_, 0);
v_isSharedCheck_6233_ = !lean_is_exclusive(v_x_6224_);
if (v_isSharedCheck_6233_ == 0)
{
v___x_6228_ = v_x_6224_;
v_isShared_6229_ = v_isSharedCheck_6233_;
goto v_resetjp_6227_;
}
else
{
lean_inc(v_a_6226_);
lean_dec(v_x_6224_);
v___x_6228_ = lean_box(0);
v_isShared_6229_ = v_isSharedCheck_6233_;
goto v_resetjp_6227_;
}
v_resetjp_6227_:
{
lean_object* v___x_6231_; 
if (v_isShared_6229_ == 0)
{
lean_ctor_set_tag(v___x_6228_, 1);
v___x_6231_ = v___x_6228_;
goto v_reusejp_6230_;
}
else
{
lean_object* v_reuseFailAlloc_6232_; 
v_reuseFailAlloc_6232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6232_, 0, v_a_6226_);
v___x_6231_ = v_reuseFailAlloc_6232_;
goto v_reusejp_6230_;
}
v_reusejp_6230_:
{
return v___x_6231_;
}
}
}
else
{
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6241_; 
v_a_6234_ = lean_ctor_get(v_x_6224_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v_x_6224_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6236_ = v_x_6224_;
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v_x_6224_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6239_; 
if (v_isShared_6237_ == 0)
{
lean_ctor_set_tag(v___x_6236_, 0);
v___x_6239_ = v___x_6236_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
return v___x_6239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6242_, lean_object* v___y_6243_){
_start:
{
lean_object* v_res_6244_; 
v_res_6244_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6242_);
return v_res_6244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6245_, lean_object* v_opt_6246_){
_start:
{
lean_object* v_name_6247_; lean_object* v_defValue_6248_; lean_object* v_map_6249_; lean_object* v___x_6250_; 
v_name_6247_ = lean_ctor_get(v_opt_6246_, 0);
v_defValue_6248_ = lean_ctor_get(v_opt_6246_, 1);
v_map_6249_ = lean_ctor_get(v_opts_6245_, 0);
v___x_6250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6249_, v_name_6247_);
if (lean_obj_tag(v___x_6250_) == 0)
{
lean_inc(v_defValue_6248_);
return v_defValue_6248_;
}
else
{
lean_object* v_val_6251_; 
v_val_6251_ = lean_ctor_get(v___x_6250_, 0);
lean_inc(v_val_6251_);
lean_dec_ref_known(v___x_6250_, 1);
if (lean_obj_tag(v_val_6251_) == 3)
{
lean_object* v_v_6252_; 
v_v_6252_ = lean_ctor_get(v_val_6251_, 0);
lean_inc(v_v_6252_);
lean_dec_ref_known(v_val_6251_, 1);
return v_v_6252_;
}
else
{
lean_dec(v_val_6251_);
lean_inc(v_defValue_6248_);
return v_defValue_6248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6253_, lean_object* v_opt_6254_){
_start:
{
lean_object* v_res_6255_; 
v_res_6255_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6253_, v_opt_6254_);
lean_dec_ref(v_opt_6254_);
lean_dec_ref(v_opts_6253_);
return v_res_6255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6256_, size_t v_i_6257_, lean_object* v_bs_6258_){
_start:
{
uint8_t v___x_6259_; 
v___x_6259_ = lean_usize_dec_lt(v_i_6257_, v_sz_6256_);
if (v___x_6259_ == 0)
{
return v_bs_6258_;
}
else
{
lean_object* v_v_6260_; lean_object* v_msg_6261_; lean_object* v___x_6262_; lean_object* v_bs_x27_6263_; size_t v___x_6264_; size_t v___x_6265_; lean_object* v___x_6266_; 
v_v_6260_ = lean_array_uget_borrowed(v_bs_6258_, v_i_6257_);
v_msg_6261_ = lean_ctor_get(v_v_6260_, 1);
lean_inc_ref(v_msg_6261_);
v___x_6262_ = lean_unsigned_to_nat(0u);
v_bs_x27_6263_ = lean_array_uset(v_bs_6258_, v_i_6257_, v___x_6262_);
v___x_6264_ = ((size_t)1ULL);
v___x_6265_ = lean_usize_add(v_i_6257_, v___x_6264_);
v___x_6266_ = lean_array_uset(v_bs_x27_6263_, v_i_6257_, v_msg_6261_);
v_i_6257_ = v___x_6265_;
v_bs_6258_ = v___x_6266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6268_, lean_object* v_i_6269_, lean_object* v_bs_6270_){
_start:
{
size_t v_sz_boxed_6271_; size_t v_i_boxed_6272_; lean_object* v_res_6273_; 
v_sz_boxed_6271_ = lean_unbox_usize(v_sz_6268_);
lean_dec(v_sz_6268_);
v_i_boxed_6272_ = lean_unbox_usize(v_i_6269_);
lean_dec(v_i_6269_);
v_res_6273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6271_, v_i_boxed_6272_, v_bs_6270_);
return v_res_6273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6274_, lean_object* v_data_6275_, lean_object* v_ref_6276_, lean_object* v_msg_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_){
_start:
{
lean_object* v_toCold_6283_; lean_object* v_currRecDepth_6284_; lean_object* v_ref_6285_; uint16_t v_optionFlags_6286_; uint8_t v_suppressElabErrors_6287_; uint8_t v_isRecordingDeps_6288_; lean_object* v_ref_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v_traceState_6292_; lean_object* v_traces_6293_; lean_object* v___x_6294_; size_t v_sz_6295_; size_t v___x_6296_; lean_object* v___x_6297_; lean_object* v_msg_6298_; lean_object* v___x_6299_; lean_object* v_a_6300_; lean_object* v___x_6302_; uint8_t v_isShared_6303_; uint8_t v_isSharedCheck_6338_; 
v_toCold_6283_ = lean_ctor_get(v___y_6280_, 0);
v_currRecDepth_6284_ = lean_ctor_get(v___y_6280_, 1);
v_ref_6285_ = lean_ctor_get(v___y_6280_, 2);
v_optionFlags_6286_ = lean_ctor_get_uint16(v___y_6280_, sizeof(void*)*3);
v_suppressElabErrors_6287_ = lean_ctor_get_uint8(v___y_6280_, sizeof(void*)*3 + 2);
v_isRecordingDeps_6288_ = lean_ctor_get_uint8(v___y_6280_, sizeof(void*)*3 + 3);
v_ref_6289_ = l_Lean_replaceRef(v_ref_6276_, v_ref_6285_);
lean_inc(v_currRecDepth_6284_);
lean_inc_ref(v_toCold_6283_);
v___x_6290_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_6290_, 0, v_toCold_6283_);
lean_ctor_set(v___x_6290_, 1, v_currRecDepth_6284_);
lean_ctor_set(v___x_6290_, 2, v_ref_6289_);
lean_ctor_set_uint16(v___x_6290_, sizeof(void*)*3, v_optionFlags_6286_);
lean_ctor_set_uint8(v___x_6290_, sizeof(void*)*3 + 2, v_suppressElabErrors_6287_);
lean_ctor_set_uint8(v___x_6290_, sizeof(void*)*3 + 3, v_isRecordingDeps_6288_);
v___x_6291_ = lean_st_ref_get(v___y_6281_);
v_traceState_6292_ = lean_ctor_get(v___x_6291_, 4);
lean_inc_ref(v_traceState_6292_);
lean_dec(v___x_6291_);
v_traces_6293_ = lean_ctor_get(v_traceState_6292_, 0);
lean_inc_ref(v_traces_6293_);
lean_dec_ref(v_traceState_6292_);
v___x_6294_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6293_);
lean_dec_ref(v_traces_6293_);
v_sz_6295_ = lean_array_size(v___x_6294_);
v___x_6296_ = ((size_t)0ULL);
v___x_6297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6295_, v___x_6296_, v___x_6294_);
v_msg_6298_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6298_, 0, v_data_6275_);
lean_ctor_set(v_msg_6298_, 1, v_msg_6277_);
lean_ctor_set(v_msg_6298_, 2, v___x_6297_);
v___x_6299_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6298_, v___y_6278_, v___y_6279_, v___x_6290_, v___y_6281_);
lean_dec_ref_known(v___x_6290_, 3);
v_a_6300_ = lean_ctor_get(v___x_6299_, 0);
v_isSharedCheck_6338_ = !lean_is_exclusive(v___x_6299_);
if (v_isSharedCheck_6338_ == 0)
{
v___x_6302_ = v___x_6299_;
v_isShared_6303_ = v_isSharedCheck_6338_;
goto v_resetjp_6301_;
}
else
{
lean_inc(v_a_6300_);
lean_dec(v___x_6299_);
v___x_6302_ = lean_box(0);
v_isShared_6303_ = v_isSharedCheck_6338_;
goto v_resetjp_6301_;
}
v_resetjp_6301_:
{
lean_object* v___x_6304_; lean_object* v_traceState_6305_; lean_object* v_env_6306_; lean_object* v_nextMacroScope_6307_; lean_object* v_ngen_6308_; lean_object* v_auxDeclNGen_6309_; lean_object* v_cache_6310_; lean_object* v_recordedDeps_6311_; lean_object* v_messages_6312_; lean_object* v_infoState_6313_; lean_object* v_snapshotTasks_6314_; lean_object* v___x_6316_; uint8_t v_isShared_6317_; uint8_t v_isSharedCheck_6337_; 
v___x_6304_ = lean_st_ref_take(v___y_6281_);
v_traceState_6305_ = lean_ctor_get(v___x_6304_, 4);
v_env_6306_ = lean_ctor_get(v___x_6304_, 0);
v_nextMacroScope_6307_ = lean_ctor_get(v___x_6304_, 1);
v_ngen_6308_ = lean_ctor_get(v___x_6304_, 2);
v_auxDeclNGen_6309_ = lean_ctor_get(v___x_6304_, 3);
v_cache_6310_ = lean_ctor_get(v___x_6304_, 5);
v_recordedDeps_6311_ = lean_ctor_get(v___x_6304_, 6);
v_messages_6312_ = lean_ctor_get(v___x_6304_, 7);
v_infoState_6313_ = lean_ctor_get(v___x_6304_, 8);
v_snapshotTasks_6314_ = lean_ctor_get(v___x_6304_, 9);
v_isSharedCheck_6337_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6337_ == 0)
{
v___x_6316_ = v___x_6304_;
v_isShared_6317_ = v_isSharedCheck_6337_;
goto v_resetjp_6315_;
}
else
{
lean_inc(v_snapshotTasks_6314_);
lean_inc(v_infoState_6313_);
lean_inc(v_messages_6312_);
lean_inc(v_recordedDeps_6311_);
lean_inc(v_cache_6310_);
lean_inc(v_traceState_6305_);
lean_inc(v_auxDeclNGen_6309_);
lean_inc(v_ngen_6308_);
lean_inc(v_nextMacroScope_6307_);
lean_inc(v_env_6306_);
lean_dec(v___x_6304_);
v___x_6316_ = lean_box(0);
v_isShared_6317_ = v_isSharedCheck_6337_;
goto v_resetjp_6315_;
}
v_resetjp_6315_:
{
uint64_t v_tid_6318_; lean_object* v___x_6320_; uint8_t v_isShared_6321_; uint8_t v_isSharedCheck_6335_; 
v_tid_6318_ = lean_ctor_get_uint64(v_traceState_6305_, sizeof(void*)*1);
v_isSharedCheck_6335_ = !lean_is_exclusive(v_traceState_6305_);
if (v_isSharedCheck_6335_ == 0)
{
lean_object* v_unused_6336_; 
v_unused_6336_ = lean_ctor_get(v_traceState_6305_, 0);
lean_dec(v_unused_6336_);
v___x_6320_ = v_traceState_6305_;
v_isShared_6321_ = v_isSharedCheck_6335_;
goto v_resetjp_6319_;
}
else
{
lean_dec(v_traceState_6305_);
v___x_6320_ = lean_box(0);
v_isShared_6321_ = v_isSharedCheck_6335_;
goto v_resetjp_6319_;
}
v_resetjp_6319_:
{
lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6326_; 
v___x_6322_ = lean_box(0);
v___x_6323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6323_, 0, v_ref_6276_);
lean_ctor_set(v___x_6323_, 1, v_a_6300_);
v___x_6324_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6274_, v___x_6323_);
if (v_isShared_6321_ == 0)
{
lean_ctor_set(v___x_6320_, 0, v___x_6324_);
v___x_6326_ = v___x_6320_;
goto v_reusejp_6325_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v___x_6324_);
lean_ctor_set_uint64(v_reuseFailAlloc_6334_, sizeof(void*)*1, v_tid_6318_);
v___x_6326_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6325_;
}
v_reusejp_6325_:
{
lean_object* v___x_6328_; 
if (v_isShared_6317_ == 0)
{
lean_ctor_set(v___x_6316_, 4, v___x_6326_);
v___x_6328_ = v___x_6316_;
goto v_reusejp_6327_;
}
else
{
lean_object* v_reuseFailAlloc_6333_; 
v_reuseFailAlloc_6333_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6333_, 0, v_env_6306_);
lean_ctor_set(v_reuseFailAlloc_6333_, 1, v_nextMacroScope_6307_);
lean_ctor_set(v_reuseFailAlloc_6333_, 2, v_ngen_6308_);
lean_ctor_set(v_reuseFailAlloc_6333_, 3, v_auxDeclNGen_6309_);
lean_ctor_set(v_reuseFailAlloc_6333_, 4, v___x_6326_);
lean_ctor_set(v_reuseFailAlloc_6333_, 5, v_cache_6310_);
lean_ctor_set(v_reuseFailAlloc_6333_, 6, v_recordedDeps_6311_);
lean_ctor_set(v_reuseFailAlloc_6333_, 7, v_messages_6312_);
lean_ctor_set(v_reuseFailAlloc_6333_, 8, v_infoState_6313_);
lean_ctor_set(v_reuseFailAlloc_6333_, 9, v_snapshotTasks_6314_);
v___x_6328_ = v_reuseFailAlloc_6333_;
goto v_reusejp_6327_;
}
v_reusejp_6327_:
{
lean_object* v___x_6329_; lean_object* v___x_6331_; 
v___x_6329_ = lean_st_ref_put(v___y_6281_, v___x_6328_);
if (v_isShared_6303_ == 0)
{
lean_ctor_set(v___x_6302_, 0, v___x_6322_);
v___x_6331_ = v___x_6302_;
goto v_reusejp_6330_;
}
else
{
lean_object* v_reuseFailAlloc_6332_; 
v_reuseFailAlloc_6332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6332_, 0, v___x_6322_);
v___x_6331_ = v_reuseFailAlloc_6332_;
goto v_reusejp_6330_;
}
v_reusejp_6330_:
{
return v___x_6331_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6339_, lean_object* v_data_6340_, lean_object* v_ref_6341_, lean_object* v_msg_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_){
_start:
{
lean_object* v_res_6348_; 
v_res_6348_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6339_, v_data_6340_, v_ref_6341_, v_msg_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_);
lean_dec(v___y_6346_);
lean_dec_ref(v___y_6345_);
lean_dec(v___y_6344_);
lean_dec_ref(v___y_6343_);
return v_res_6348_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6350_; lean_object* v___x_6351_; 
v___x_6350_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6351_ = l_Lean_stringToMessageData(v___x_6350_);
return v___x_6351_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6352_; double v___x_6353_; 
v___x_6352_ = lean_unsigned_to_nat(1000u);
v___x_6353_ = lean_float_of_nat(v___x_6352_);
return v___x_6353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6354_, uint8_t v_collapsed_6355_, lean_object* v_tag_6356_, lean_object* v_opts_6357_, uint8_t v_clsEnabled_6358_, lean_object* v_oldTraces_6359_, lean_object* v_msg_6360_, lean_object* v_resStartStop_6361_, lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_){
_start:
{
lean_object* v_fst_6374_; lean_object* v_snd_6375_; lean_object* v___y_6377_; lean_object* v___y_6378_; lean_object* v_data_6379_; lean_object* v_fst_6390_; lean_object* v_snd_6391_; lean_object* v___x_6392_; uint8_t v___x_6393_; lean_object* v___y_6395_; lean_object* v_a_6396_; uint8_t v___y_6411_; double v___y_6443_; 
v_fst_6374_ = lean_ctor_get(v_resStartStop_6361_, 0);
lean_inc(v_fst_6374_);
v_snd_6375_ = lean_ctor_get(v_resStartStop_6361_, 1);
lean_inc(v_snd_6375_);
lean_dec_ref(v_resStartStop_6361_);
v_fst_6390_ = lean_ctor_get(v_snd_6375_, 0);
lean_inc(v_fst_6390_);
v_snd_6391_ = lean_ctor_get(v_snd_6375_, 1);
lean_inc(v_snd_6391_);
lean_dec(v_snd_6375_);
v___x_6392_ = l_Lean_trace_profiler;
v___x_6393_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6357_, v___x_6392_);
if (v___x_6393_ == 0)
{
v___y_6411_ = v___x_6393_;
goto v___jp_6410_;
}
else
{
lean_object* v___x_6448_; uint8_t v___x_6449_; 
v___x_6448_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6449_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6357_, v___x_6448_);
if (v___x_6449_ == 0)
{
lean_object* v___x_6450_; lean_object* v___x_6451_; double v___x_6452_; double v___x_6453_; double v___x_6454_; 
v___x_6450_ = l_Lean_trace_profiler_threshold;
v___x_6451_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6357_, v___x_6450_);
v___x_6452_ = lean_float_of_nat(v___x_6451_);
v___x_6453_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6454_ = lean_float_div(v___x_6452_, v___x_6453_);
v___y_6443_ = v___x_6454_;
goto v___jp_6442_;
}
else
{
lean_object* v___x_6455_; lean_object* v___x_6456_; double v___x_6457_; 
v___x_6455_ = l_Lean_trace_profiler_threshold;
v___x_6456_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6357_, v___x_6455_);
v___x_6457_ = lean_float_of_nat(v___x_6456_);
v___y_6443_ = v___x_6457_;
goto v___jp_6442_;
}
}
v___jp_6376_:
{
lean_object* v___x_6380_; 
lean_inc(v___y_6378_);
v___x_6380_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6359_, v_data_6379_, v___y_6378_, v___y_6377_, v___y_6369_, v___y_6370_, v___y_6371_, v___y_6372_);
if (lean_obj_tag(v___x_6380_) == 0)
{
lean_object* v___x_6381_; 
lean_dec_ref_known(v___x_6380_, 1);
v___x_6381_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6374_);
return v___x_6381_;
}
else
{
lean_object* v_a_6382_; lean_object* v___x_6384_; uint8_t v_isShared_6385_; uint8_t v_isSharedCheck_6389_; 
lean_dec(v_fst_6374_);
v_a_6382_ = lean_ctor_get(v___x_6380_, 0);
v_isSharedCheck_6389_ = !lean_is_exclusive(v___x_6380_);
if (v_isSharedCheck_6389_ == 0)
{
v___x_6384_ = v___x_6380_;
v_isShared_6385_ = v_isSharedCheck_6389_;
goto v_resetjp_6383_;
}
else
{
lean_inc(v_a_6382_);
lean_dec(v___x_6380_);
v___x_6384_ = lean_box(0);
v_isShared_6385_ = v_isSharedCheck_6389_;
goto v_resetjp_6383_;
}
v_resetjp_6383_:
{
lean_object* v___x_6387_; 
if (v_isShared_6385_ == 0)
{
v___x_6387_ = v___x_6384_;
goto v_reusejp_6386_;
}
else
{
lean_object* v_reuseFailAlloc_6388_; 
v_reuseFailAlloc_6388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_a_6382_);
v___x_6387_ = v_reuseFailAlloc_6388_;
goto v_reusejp_6386_;
}
v_reusejp_6386_:
{
return v___x_6387_;
}
}
}
}
v___jp_6394_:
{
uint8_t v_result_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; double v___x_6400_; lean_object* v_data_6401_; 
v_result_6397_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6374_);
v___x_6398_ = lean_box(v_result_6397_);
v___x_6399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6399_, 0, v___x_6398_);
v___x_6400_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6356_);
lean_inc_ref(v___x_6399_);
lean_inc(v_cls_6354_);
v_data_6401_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6401_, 0, v_cls_6354_);
lean_ctor_set(v_data_6401_, 1, v___x_6399_);
lean_ctor_set(v_data_6401_, 2, v_tag_6356_);
lean_ctor_set_float(v_data_6401_, sizeof(void*)*3, v___x_6400_);
lean_ctor_set_float(v_data_6401_, sizeof(void*)*3 + 8, v___x_6400_);
lean_ctor_set_uint8(v_data_6401_, sizeof(void*)*3 + 16, v_collapsed_6355_);
if (v___x_6393_ == 0)
{
lean_dec_ref_known(v___x_6399_, 1);
lean_dec(v_snd_6391_);
lean_dec(v_fst_6390_);
lean_dec_ref(v_tag_6356_);
lean_dec(v_cls_6354_);
v___y_6377_ = v_a_6396_;
v___y_6378_ = v___y_6395_;
v_data_6379_ = v_data_6401_;
goto v___jp_6376_;
}
else
{
lean_object* v_data_6402_; double v___x_6403_; double v___x_6404_; 
lean_dec_ref_known(v_data_6401_, 3);
v_data_6402_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6402_, 0, v_cls_6354_);
lean_ctor_set(v_data_6402_, 1, v___x_6399_);
lean_ctor_set(v_data_6402_, 2, v_tag_6356_);
v___x_6403_ = lean_unbox_float(v_fst_6390_);
lean_dec(v_fst_6390_);
lean_ctor_set_float(v_data_6402_, sizeof(void*)*3, v___x_6403_);
v___x_6404_ = lean_unbox_float(v_snd_6391_);
lean_dec(v_snd_6391_);
lean_ctor_set_float(v_data_6402_, sizeof(void*)*3 + 8, v___x_6404_);
lean_ctor_set_uint8(v_data_6402_, sizeof(void*)*3 + 16, v_collapsed_6355_);
v___y_6377_ = v_a_6396_;
v___y_6378_ = v___y_6395_;
v_data_6379_ = v_data_6402_;
goto v___jp_6376_;
}
}
v___jp_6405_:
{
lean_object* v_ref_6406_; lean_object* v___x_6407_; 
v_ref_6406_ = lean_ctor_get(v___y_6371_, 2);
lean_inc(v___y_6372_);
lean_inc_ref(v___y_6371_);
lean_inc(v___y_6370_);
lean_inc_ref(v___y_6369_);
lean_inc(v___y_6368_);
lean_inc_ref(v___y_6367_);
lean_inc(v___y_6366_);
lean_inc_ref(v___y_6365_);
lean_inc(v___y_6364_);
lean_inc(v___y_6363_);
lean_inc_ref(v___y_6362_);
lean_inc(v_fst_6374_);
v___x_6407_ = lean_apply_13(v_msg_6360_, v_fst_6374_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_, v___y_6372_, lean_box(0));
if (lean_obj_tag(v___x_6407_) == 0)
{
lean_object* v_a_6408_; 
v_a_6408_ = lean_ctor_get(v___x_6407_, 0);
lean_inc(v_a_6408_);
lean_dec_ref_known(v___x_6407_, 1);
v___y_6395_ = v_ref_6406_;
v_a_6396_ = v_a_6408_;
goto v___jp_6394_;
}
else
{
lean_object* v___x_6409_; 
lean_dec_ref_known(v___x_6407_, 1);
v___x_6409_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6395_ = v_ref_6406_;
v_a_6396_ = v___x_6409_;
goto v___jp_6394_;
}
}
v___jp_6410_:
{
if (v_clsEnabled_6358_ == 0)
{
if (v___y_6411_ == 0)
{
lean_object* v___x_6412_; lean_object* v_traceState_6413_; lean_object* v_env_6414_; lean_object* v_nextMacroScope_6415_; lean_object* v_ngen_6416_; lean_object* v_auxDeclNGen_6417_; lean_object* v_cache_6418_; lean_object* v_recordedDeps_6419_; lean_object* v_messages_6420_; lean_object* v_infoState_6421_; lean_object* v_snapshotTasks_6422_; lean_object* v___x_6424_; uint8_t v_isShared_6425_; uint8_t v_isSharedCheck_6441_; 
lean_dec(v_snd_6391_);
lean_dec(v_fst_6390_);
lean_dec_ref(v_msg_6360_);
lean_dec_ref(v_tag_6356_);
lean_dec(v_cls_6354_);
v___x_6412_ = lean_st_ref_take(v___y_6372_);
v_traceState_6413_ = lean_ctor_get(v___x_6412_, 4);
v_env_6414_ = lean_ctor_get(v___x_6412_, 0);
v_nextMacroScope_6415_ = lean_ctor_get(v___x_6412_, 1);
v_ngen_6416_ = lean_ctor_get(v___x_6412_, 2);
v_auxDeclNGen_6417_ = lean_ctor_get(v___x_6412_, 3);
v_cache_6418_ = lean_ctor_get(v___x_6412_, 5);
v_recordedDeps_6419_ = lean_ctor_get(v___x_6412_, 6);
v_messages_6420_ = lean_ctor_get(v___x_6412_, 7);
v_infoState_6421_ = lean_ctor_get(v___x_6412_, 8);
v_snapshotTasks_6422_ = lean_ctor_get(v___x_6412_, 9);
v_isSharedCheck_6441_ = !lean_is_exclusive(v___x_6412_);
if (v_isSharedCheck_6441_ == 0)
{
v___x_6424_ = v___x_6412_;
v_isShared_6425_ = v_isSharedCheck_6441_;
goto v_resetjp_6423_;
}
else
{
lean_inc(v_snapshotTasks_6422_);
lean_inc(v_infoState_6421_);
lean_inc(v_messages_6420_);
lean_inc(v_recordedDeps_6419_);
lean_inc(v_cache_6418_);
lean_inc(v_traceState_6413_);
lean_inc(v_auxDeclNGen_6417_);
lean_inc(v_ngen_6416_);
lean_inc(v_nextMacroScope_6415_);
lean_inc(v_env_6414_);
lean_dec(v___x_6412_);
v___x_6424_ = lean_box(0);
v_isShared_6425_ = v_isSharedCheck_6441_;
goto v_resetjp_6423_;
}
v_resetjp_6423_:
{
uint64_t v_tid_6426_; lean_object* v_traces_6427_; lean_object* v___x_6429_; uint8_t v_isShared_6430_; uint8_t v_isSharedCheck_6440_; 
v_tid_6426_ = lean_ctor_get_uint64(v_traceState_6413_, sizeof(void*)*1);
v_traces_6427_ = lean_ctor_get(v_traceState_6413_, 0);
v_isSharedCheck_6440_ = !lean_is_exclusive(v_traceState_6413_);
if (v_isSharedCheck_6440_ == 0)
{
v___x_6429_ = v_traceState_6413_;
v_isShared_6430_ = v_isSharedCheck_6440_;
goto v_resetjp_6428_;
}
else
{
lean_inc(v_traces_6427_);
lean_dec(v_traceState_6413_);
v___x_6429_ = lean_box(0);
v_isShared_6430_ = v_isSharedCheck_6440_;
goto v_resetjp_6428_;
}
v_resetjp_6428_:
{
lean_object* v___x_6431_; lean_object* v___x_6433_; 
v___x_6431_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6359_, v_traces_6427_);
lean_dec_ref(v_traces_6427_);
if (v_isShared_6430_ == 0)
{
lean_ctor_set(v___x_6429_, 0, v___x_6431_);
v___x_6433_ = v___x_6429_;
goto v_reusejp_6432_;
}
else
{
lean_object* v_reuseFailAlloc_6439_; 
v_reuseFailAlloc_6439_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6439_, 0, v___x_6431_);
lean_ctor_set_uint64(v_reuseFailAlloc_6439_, sizeof(void*)*1, v_tid_6426_);
v___x_6433_ = v_reuseFailAlloc_6439_;
goto v_reusejp_6432_;
}
v_reusejp_6432_:
{
lean_object* v___x_6435_; 
if (v_isShared_6425_ == 0)
{
lean_ctor_set(v___x_6424_, 4, v___x_6433_);
v___x_6435_ = v___x_6424_;
goto v_reusejp_6434_;
}
else
{
lean_object* v_reuseFailAlloc_6438_; 
v_reuseFailAlloc_6438_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6438_, 0, v_env_6414_);
lean_ctor_set(v_reuseFailAlloc_6438_, 1, v_nextMacroScope_6415_);
lean_ctor_set(v_reuseFailAlloc_6438_, 2, v_ngen_6416_);
lean_ctor_set(v_reuseFailAlloc_6438_, 3, v_auxDeclNGen_6417_);
lean_ctor_set(v_reuseFailAlloc_6438_, 4, v___x_6433_);
lean_ctor_set(v_reuseFailAlloc_6438_, 5, v_cache_6418_);
lean_ctor_set(v_reuseFailAlloc_6438_, 6, v_recordedDeps_6419_);
lean_ctor_set(v_reuseFailAlloc_6438_, 7, v_messages_6420_);
lean_ctor_set(v_reuseFailAlloc_6438_, 8, v_infoState_6421_);
lean_ctor_set(v_reuseFailAlloc_6438_, 9, v_snapshotTasks_6422_);
v___x_6435_ = v_reuseFailAlloc_6438_;
goto v_reusejp_6434_;
}
v_reusejp_6434_:
{
lean_object* v___x_6436_; lean_object* v___x_6437_; 
v___x_6436_ = lean_st_ref_put(v___y_6372_, v___x_6435_);
v___x_6437_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6374_);
return v___x_6437_;
}
}
}
}
}
else
{
goto v___jp_6405_;
}
}
else
{
goto v___jp_6405_;
}
}
v___jp_6442_:
{
double v___x_6444_; double v___x_6445_; double v___x_6446_; uint8_t v___x_6447_; 
v___x_6444_ = lean_unbox_float(v_snd_6391_);
v___x_6445_ = lean_unbox_float(v_fst_6390_);
v___x_6446_ = lean_float_sub(v___x_6444_, v___x_6445_);
v___x_6447_ = lean_float_decLt(v___y_6443_, v___x_6446_);
v___y_6411_ = v___x_6447_;
goto v___jp_6410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6458_ = _args[0];
lean_object* v_collapsed_6459_ = _args[1];
lean_object* v_tag_6460_ = _args[2];
lean_object* v_opts_6461_ = _args[3];
lean_object* v_clsEnabled_6462_ = _args[4];
lean_object* v_oldTraces_6463_ = _args[5];
lean_object* v_msg_6464_ = _args[6];
lean_object* v_resStartStop_6465_ = _args[7];
lean_object* v___y_6466_ = _args[8];
lean_object* v___y_6467_ = _args[9];
lean_object* v___y_6468_ = _args[10];
lean_object* v___y_6469_ = _args[11];
lean_object* v___y_6470_ = _args[12];
lean_object* v___y_6471_ = _args[13];
lean_object* v___y_6472_ = _args[14];
lean_object* v___y_6473_ = _args[15];
lean_object* v___y_6474_ = _args[16];
lean_object* v___y_6475_ = _args[17];
lean_object* v___y_6476_ = _args[18];
lean_object* v___y_6477_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6478_; uint8_t v_clsEnabled_boxed_6479_; lean_object* v_res_6480_; 
v_collapsed_boxed_6478_ = lean_unbox(v_collapsed_6459_);
v_clsEnabled_boxed_6479_ = lean_unbox(v_clsEnabled_6462_);
v_res_6480_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6458_, v_collapsed_boxed_6478_, v_tag_6460_, v_opts_6461_, v_clsEnabled_boxed_6479_, v_oldTraces_6463_, v_msg_6464_, v_resStartStop_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_);
lean_dec(v___y_6476_);
lean_dec_ref(v___y_6475_);
lean_dec(v___y_6474_);
lean_dec_ref(v___y_6473_);
lean_dec(v___y_6472_);
lean_dec_ref(v___y_6471_);
lean_dec(v___y_6470_);
lean_dec_ref(v___y_6469_);
lean_dec(v___y_6468_);
lean_dec(v___y_6467_);
lean_dec_ref(v___y_6466_);
lean_dec_ref(v_opts_6461_);
return v_res_6480_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6485_; lean_object* v___x_6486_; 
v___x_6485_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6486_ = l_Lean_stringToMessageData(v___x_6485_);
return v___x_6486_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6487_, lean_object* v_b_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_){
_start:
{
if (lean_obj_tag(v_as_x27_6487_) == 0)
{
lean_object* v___x_6501_; 
v___x_6501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6501_, 0, v_b_6488_);
return v___x_6501_;
}
else
{
lean_object* v_head_6502_; lean_object* v_toCold_6503_; lean_object* v_options_6504_; lean_object* v_tail_6505_; lean_object* v_name_6506_; lean_object* v_run_x27_6507_; lean_object* v_inheritedTraceOptions_6508_; uint8_t v_hasTrace_6509_; lean_object* v___x_6510_; uint8_t v___y_6512_; lean_object* v___x_6517_; lean_object* v___y_6519_; 
lean_dec_ref(v_b_6488_);
v_head_6502_ = lean_ctor_get(v_as_x27_6487_, 0);
v_toCold_6503_ = lean_ctor_get(v___y_6498_, 0);
v_options_6504_ = lean_ctor_get(v_toCold_6503_, 2);
v_tail_6505_ = lean_ctor_get(v_as_x27_6487_, 1);
v_name_6506_ = lean_ctor_get(v_head_6502_, 0);
v_run_x27_6507_ = lean_ctor_get(v_head_6502_, 1);
v_inheritedTraceOptions_6508_ = lean_ctor_get(v_toCold_6503_, 11);
v_hasTrace_6509_ = lean_ctor_get_uint8(v_options_6504_, sizeof(void*)*1);
v___x_6510_ = lean_box(0);
v___x_6517_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6509_ == 0)
{
lean_object* v___x_6547_; 
lean_inc_ref(v_run_x27_6507_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
lean_inc(v___y_6497_);
lean_inc_ref(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc_ref(v___y_6494_);
lean_inc(v___y_6493_);
lean_inc_ref(v___y_6492_);
lean_inc(v___y_6491_);
lean_inc(v___y_6490_);
lean_inc_ref(v___y_6489_);
v___x_6547_ = lean_apply_12(v_run_x27_6507_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, lean_box(0));
v___y_6519_ = v___x_6547_;
goto v___jp_6518_;
}
else
{
lean_object* v___f_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; uint8_t v___x_6552_; lean_object* v___y_6554_; lean_object* v___y_6555_; lean_object* v_a_6556_; lean_object* v___y_6569_; lean_object* v___y_6570_; lean_object* v_a_6571_; 
lean_inc(v_name_6506_);
v___f_6548_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6548_, 0, v_name_6506_);
v___x_6549_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6550_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6551_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6552_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6508_, v_options_6504_, v___x_6551_);
if (v___x_6552_ == 0)
{
lean_object* v___x_6621_; uint8_t v___x_6622_; 
v___x_6621_ = l_Lean_trace_profiler;
v___x_6622_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6504_, v___x_6621_);
if (v___x_6622_ == 0)
{
lean_object* v___x_6623_; 
lean_dec_ref(v___f_6548_);
lean_inc_ref(v_run_x27_6507_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
lean_inc(v___y_6497_);
lean_inc_ref(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc_ref(v___y_6494_);
lean_inc(v___y_6493_);
lean_inc_ref(v___y_6492_);
lean_inc(v___y_6491_);
lean_inc(v___y_6490_);
lean_inc_ref(v___y_6489_);
v___x_6623_ = lean_apply_12(v_run_x27_6507_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, lean_box(0));
v___y_6519_ = v___x_6623_;
goto v___jp_6518_;
}
else
{
goto v___jp_6580_;
}
}
else
{
goto v___jp_6580_;
}
v___jp_6553_:
{
lean_object* v___x_6557_; double v___x_6558_; double v___x_6559_; double v___x_6560_; double v___x_6561_; double v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; 
v___x_6557_ = lean_io_mono_nanos_now();
v___x_6558_ = lean_float_of_nat(v___y_6554_);
v___x_6559_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6560_ = lean_float_div(v___x_6558_, v___x_6559_);
v___x_6561_ = lean_float_of_nat(v___x_6557_);
v___x_6562_ = lean_float_div(v___x_6561_, v___x_6559_);
v___x_6563_ = lean_box_float(v___x_6560_);
v___x_6564_ = lean_box_float(v___x_6562_);
v___x_6565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6565_, 0, v___x_6563_);
lean_ctor_set(v___x_6565_, 1, v___x_6564_);
v___x_6566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6566_, 0, v_a_6556_);
lean_ctor_set(v___x_6566_, 1, v___x_6565_);
v___x_6567_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6549_, v_hasTrace_6509_, v___x_6550_, v_options_6504_, v___x_6552_, v___y_6555_, v___f_6548_, v___x_6566_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_);
v___y_6519_ = v___x_6567_;
goto v___jp_6518_;
}
v___jp_6568_:
{
lean_object* v___x_6572_; double v___x_6573_; double v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; 
v___x_6572_ = lean_io_get_num_heartbeats();
v___x_6573_ = lean_float_of_nat(v___y_6569_);
v___x_6574_ = lean_float_of_nat(v___x_6572_);
v___x_6575_ = lean_box_float(v___x_6573_);
v___x_6576_ = lean_box_float(v___x_6574_);
v___x_6577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6577_, 0, v___x_6575_);
lean_ctor_set(v___x_6577_, 1, v___x_6576_);
v___x_6578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6578_, 0, v_a_6571_);
lean_ctor_set(v___x_6578_, 1, v___x_6577_);
v___x_6579_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6549_, v_hasTrace_6509_, v___x_6550_, v_options_6504_, v___x_6552_, v___y_6570_, v___f_6548_, v___x_6578_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_);
v___y_6519_ = v___x_6579_;
goto v___jp_6518_;
}
v___jp_6580_:
{
lean_object* v___x_6581_; lean_object* v_a_6582_; lean_object* v___x_6583_; uint8_t v___x_6584_; 
v___x_6581_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6499_);
v_a_6582_ = lean_ctor_get(v___x_6581_, 0);
lean_inc(v_a_6582_);
lean_dec_ref(v___x_6581_);
v___x_6583_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6584_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6504_, v___x_6583_);
if (v___x_6584_ == 0)
{
lean_object* v___x_6585_; lean_object* v___x_6586_; 
v___x_6585_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_6507_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
lean_inc(v___y_6497_);
lean_inc_ref(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc_ref(v___y_6494_);
lean_inc(v___y_6493_);
lean_inc_ref(v___y_6492_);
lean_inc(v___y_6491_);
lean_inc(v___y_6490_);
lean_inc_ref(v___y_6489_);
v___x_6586_ = lean_apply_12(v_run_x27_6507_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, lean_box(0));
if (lean_obj_tag(v___x_6586_) == 0)
{
lean_object* v_a_6587_; lean_object* v___x_6589_; uint8_t v_isShared_6590_; uint8_t v_isSharedCheck_6594_; 
v_a_6587_ = lean_ctor_get(v___x_6586_, 0);
v_isSharedCheck_6594_ = !lean_is_exclusive(v___x_6586_);
if (v_isSharedCheck_6594_ == 0)
{
v___x_6589_ = v___x_6586_;
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
else
{
lean_inc(v_a_6587_);
lean_dec(v___x_6586_);
v___x_6589_ = lean_box(0);
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
v_resetjp_6588_:
{
lean_object* v___x_6592_; 
if (v_isShared_6590_ == 0)
{
lean_ctor_set_tag(v___x_6589_, 1);
v___x_6592_ = v___x_6589_;
goto v_reusejp_6591_;
}
else
{
lean_object* v_reuseFailAlloc_6593_; 
v_reuseFailAlloc_6593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6587_);
v___x_6592_ = v_reuseFailAlloc_6593_;
goto v_reusejp_6591_;
}
v_reusejp_6591_:
{
v___y_6554_ = v___x_6585_;
v___y_6555_ = v_a_6582_;
v_a_6556_ = v___x_6592_;
goto v___jp_6553_;
}
}
}
else
{
lean_object* v_a_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6602_; 
v_a_6595_ = lean_ctor_get(v___x_6586_, 0);
v_isSharedCheck_6602_ = !lean_is_exclusive(v___x_6586_);
if (v_isSharedCheck_6602_ == 0)
{
v___x_6597_ = v___x_6586_;
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_a_6595_);
lean_dec(v___x_6586_);
v___x_6597_ = lean_box(0);
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
v_resetjp_6596_:
{
lean_object* v___x_6600_; 
if (v_isShared_6598_ == 0)
{
lean_ctor_set_tag(v___x_6597_, 0);
v___x_6600_ = v___x_6597_;
goto v_reusejp_6599_;
}
else
{
lean_object* v_reuseFailAlloc_6601_; 
v_reuseFailAlloc_6601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6601_, 0, v_a_6595_);
v___x_6600_ = v_reuseFailAlloc_6601_;
goto v_reusejp_6599_;
}
v_reusejp_6599_:
{
v___y_6554_ = v___x_6585_;
v___y_6555_ = v_a_6582_;
v_a_6556_ = v___x_6600_;
goto v___jp_6553_;
}
}
}
}
else
{
lean_object* v___x_6603_; lean_object* v___x_6604_; 
v___x_6603_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_6507_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
lean_inc(v___y_6497_);
lean_inc_ref(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc_ref(v___y_6494_);
lean_inc(v___y_6493_);
lean_inc_ref(v___y_6492_);
lean_inc(v___y_6491_);
lean_inc(v___y_6490_);
lean_inc_ref(v___y_6489_);
v___x_6604_ = lean_apply_12(v_run_x27_6507_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, lean_box(0));
if (lean_obj_tag(v___x_6604_) == 0)
{
lean_object* v_a_6605_; lean_object* v___x_6607_; uint8_t v_isShared_6608_; uint8_t v_isSharedCheck_6612_; 
v_a_6605_ = lean_ctor_get(v___x_6604_, 0);
v_isSharedCheck_6612_ = !lean_is_exclusive(v___x_6604_);
if (v_isSharedCheck_6612_ == 0)
{
v___x_6607_ = v___x_6604_;
v_isShared_6608_ = v_isSharedCheck_6612_;
goto v_resetjp_6606_;
}
else
{
lean_inc(v_a_6605_);
lean_dec(v___x_6604_);
v___x_6607_ = lean_box(0);
v_isShared_6608_ = v_isSharedCheck_6612_;
goto v_resetjp_6606_;
}
v_resetjp_6606_:
{
lean_object* v___x_6610_; 
if (v_isShared_6608_ == 0)
{
lean_ctor_set_tag(v___x_6607_, 1);
v___x_6610_ = v___x_6607_;
goto v_reusejp_6609_;
}
else
{
lean_object* v_reuseFailAlloc_6611_; 
v_reuseFailAlloc_6611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6611_, 0, v_a_6605_);
v___x_6610_ = v_reuseFailAlloc_6611_;
goto v_reusejp_6609_;
}
v_reusejp_6609_:
{
v___y_6569_ = v___x_6603_;
v___y_6570_ = v_a_6582_;
v_a_6571_ = v___x_6610_;
goto v___jp_6568_;
}
}
}
else
{
lean_object* v_a_6613_; lean_object* v___x_6615_; uint8_t v_isShared_6616_; uint8_t v_isSharedCheck_6620_; 
v_a_6613_ = lean_ctor_get(v___x_6604_, 0);
v_isSharedCheck_6620_ = !lean_is_exclusive(v___x_6604_);
if (v_isSharedCheck_6620_ == 0)
{
v___x_6615_ = v___x_6604_;
v_isShared_6616_ = v_isSharedCheck_6620_;
goto v_resetjp_6614_;
}
else
{
lean_inc(v_a_6613_);
lean_dec(v___x_6604_);
v___x_6615_ = lean_box(0);
v_isShared_6616_ = v_isSharedCheck_6620_;
goto v_resetjp_6614_;
}
v_resetjp_6614_:
{
lean_object* v___x_6618_; 
if (v_isShared_6616_ == 0)
{
lean_ctor_set_tag(v___x_6615_, 0);
v___x_6618_ = v___x_6615_;
goto v_reusejp_6617_;
}
else
{
lean_object* v_reuseFailAlloc_6619_; 
v_reuseFailAlloc_6619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6619_, 0, v_a_6613_);
v___x_6618_ = v_reuseFailAlloc_6619_;
goto v_reusejp_6617_;
}
v_reusejp_6617_:
{
v___y_6569_ = v___x_6603_;
v___y_6570_ = v_a_6582_;
v_a_6571_ = v___x_6618_;
goto v___jp_6568_;
}
}
}
}
}
}
v___jp_6511_:
{
lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; 
v___x_6513_ = lean_box(v___y_6512_);
v___x_6514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6514_, 0, v___x_6513_);
v___x_6515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6515_, 0, v___x_6514_);
lean_ctor_set(v___x_6515_, 1, v___x_6510_);
v___x_6516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6516_, 0, v___x_6515_);
return v___x_6516_;
}
v___jp_6518_:
{
if (lean_obj_tag(v___y_6519_) == 0)
{
lean_object* v_a_6520_; uint8_t v___x_6521_; 
v_a_6520_ = lean_ctor_get(v___y_6519_, 0);
lean_inc(v_a_6520_);
lean_dec_ref_known(v___y_6519_, 1);
v___x_6521_ = lean_unbox(v_a_6520_);
if (v___x_6521_ == 0)
{
lean_dec(v_a_6520_);
v_as_x27_6487_ = v_tail_6505_;
v_b_6488_ = v___x_6517_;
goto _start;
}
else
{
if (v_hasTrace_6509_ == 0)
{
uint8_t v___x_6523_; 
v___x_6523_ = lean_unbox(v_a_6520_);
lean_dec(v_a_6520_);
v___y_6512_ = v___x_6523_;
goto v___jp_6511_;
}
else
{
lean_object* v___x_6524_; lean_object* v___x_6525_; uint8_t v___x_6526_; 
v___x_6524_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6525_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6526_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6508_, v_options_6504_, v___x_6525_);
if (v___x_6526_ == 0)
{
uint8_t v___x_6527_; 
v___x_6527_ = lean_unbox(v_a_6520_);
lean_dec(v_a_6520_);
v___y_6512_ = v___x_6527_;
goto v___jp_6511_;
}
else
{
lean_object* v___x_6528_; lean_object* v___x_6529_; 
v___x_6528_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_6529_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6524_, v___x_6528_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_);
if (lean_obj_tag(v___x_6529_) == 0)
{
uint8_t v___x_6530_; 
lean_dec_ref_known(v___x_6529_, 1);
v___x_6530_ = lean_unbox(v_a_6520_);
lean_dec(v_a_6520_);
v___y_6512_ = v___x_6530_;
goto v___jp_6511_;
}
else
{
lean_object* v_a_6531_; lean_object* v___x_6533_; uint8_t v_isShared_6534_; uint8_t v_isSharedCheck_6538_; 
lean_dec(v_a_6520_);
v_a_6531_ = lean_ctor_get(v___x_6529_, 0);
v_isSharedCheck_6538_ = !lean_is_exclusive(v___x_6529_);
if (v_isSharedCheck_6538_ == 0)
{
v___x_6533_ = v___x_6529_;
v_isShared_6534_ = v_isSharedCheck_6538_;
goto v_resetjp_6532_;
}
else
{
lean_inc(v_a_6531_);
lean_dec(v___x_6529_);
v___x_6533_ = lean_box(0);
v_isShared_6534_ = v_isSharedCheck_6538_;
goto v_resetjp_6532_;
}
v_resetjp_6532_:
{
lean_object* v___x_6536_; 
if (v_isShared_6534_ == 0)
{
v___x_6536_ = v___x_6533_;
goto v_reusejp_6535_;
}
else
{
lean_object* v_reuseFailAlloc_6537_; 
v_reuseFailAlloc_6537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6537_, 0, v_a_6531_);
v___x_6536_ = v_reuseFailAlloc_6537_;
goto v_reusejp_6535_;
}
v_reusejp_6535_:
{
return v___x_6536_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6539_; lean_object* v___x_6541_; uint8_t v_isShared_6542_; uint8_t v_isSharedCheck_6546_; 
v_a_6539_ = lean_ctor_get(v___y_6519_, 0);
v_isSharedCheck_6546_ = !lean_is_exclusive(v___y_6519_);
if (v_isSharedCheck_6546_ == 0)
{
v___x_6541_ = v___y_6519_;
v_isShared_6542_ = v_isSharedCheck_6546_;
goto v_resetjp_6540_;
}
else
{
lean_inc(v_a_6539_);
lean_dec(v___y_6519_);
v___x_6541_ = lean_box(0);
v_isShared_6542_ = v_isSharedCheck_6546_;
goto v_resetjp_6540_;
}
v_resetjp_6540_:
{
lean_object* v___x_6544_; 
if (v_isShared_6542_ == 0)
{
v___x_6544_ = v___x_6541_;
goto v_reusejp_6543_;
}
else
{
lean_object* v_reuseFailAlloc_6545_; 
v_reuseFailAlloc_6545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6545_, 0, v_a_6539_);
v___x_6544_ = v_reuseFailAlloc_6545_;
goto v_reusejp_6543_;
}
v_reusejp_6543_:
{
return v___x_6544_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_6624_, lean_object* v_b_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_){
_start:
{
lean_object* v_res_6638_; 
v_res_6638_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6624_, v_b_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_);
lean_dec(v___y_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
lean_dec(v___y_6632_);
lean_dec_ref(v___y_6631_);
lean_dec(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec(v___y_6628_);
lean_dec(v___y_6627_);
lean_dec_ref(v___y_6626_);
lean_dec(v_as_x27_6624_);
return v_res_6638_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_6641_; lean_object* v___x_6642_; 
v___x_6641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_6642_ = l_Lean_stringToMessageData(v___x_6641_);
return v___x_6642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_6644_; lean_object* v___x_6645_; 
v___x_6644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_6645_ = l_Lean_stringToMessageData(v___x_6644_);
return v___x_6645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_6646_, lean_object* v_a_6647_, lean_object* v_a_6648_, lean_object* v_a_6649_, lean_object* v_a_6650_, lean_object* v_a_6651_, lean_object* v_a_6652_, lean_object* v_a_6653_, lean_object* v_a_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_, lean_object* v_a_6657_){
_start:
{
lean_object* v___x_6659_; lean_object* v___x_6660_; 
v___x_6659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_6660_ = l_Lean_Core_checkSystem(v___x_6659_, v_a_6656_, v_a_6657_);
if (lean_obj_tag(v___x_6660_) == 0)
{
lean_object* v___x_6661_; lean_object* v_caches_6662_; lean_object* v_typeAnalysis_6663_; lean_object* v_target_6664_; lean_object* v_hypotheses_6665_; lean_object* v___x_6667_; uint8_t v_isShared_6668_; uint8_t v_isSharedCheck_6750_; 
lean_dec_ref_known(v___x_6660_, 1);
v___x_6661_ = lean_st_ref_take(v_a_6648_);
v_caches_6662_ = lean_ctor_get(v___x_6661_, 0);
v_typeAnalysis_6663_ = lean_ctor_get(v___x_6661_, 1);
v_target_6664_ = lean_ctor_get(v___x_6661_, 2);
v_hypotheses_6665_ = lean_ctor_get(v___x_6661_, 3);
v_isSharedCheck_6750_ = !lean_is_exclusive(v___x_6661_);
if (v_isSharedCheck_6750_ == 0)
{
v___x_6667_ = v___x_6661_;
v_isShared_6668_ = v_isSharedCheck_6750_;
goto v_resetjp_6666_;
}
else
{
lean_inc(v_hypotheses_6665_);
lean_inc(v_target_6664_);
lean_inc(v_typeAnalysis_6663_);
lean_inc(v_caches_6662_);
lean_dec(v___x_6661_);
v___x_6667_ = lean_box(0);
v_isShared_6668_ = v_isSharedCheck_6750_;
goto v_resetjp_6666_;
}
v_resetjp_6666_:
{
uint8_t v___x_6669_; lean_object* v___x_6671_; 
v___x_6669_ = 0;
if (v_isShared_6668_ == 0)
{
v___x_6671_ = v___x_6667_;
goto v_reusejp_6670_;
}
else
{
lean_object* v_reuseFailAlloc_6749_; 
v_reuseFailAlloc_6749_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6749_, 0, v_caches_6662_);
lean_ctor_set(v_reuseFailAlloc_6749_, 1, v_typeAnalysis_6663_);
lean_ctor_set(v_reuseFailAlloc_6749_, 2, v_target_6664_);
lean_ctor_set(v_reuseFailAlloc_6749_, 3, v_hypotheses_6665_);
v___x_6671_ = v_reuseFailAlloc_6749_;
goto v_reusejp_6670_;
}
v_reusejp_6670_:
{
lean_object* v___x_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; 
lean_ctor_set_uint8(v___x_6671_, sizeof(void*)*4, v___x_6669_);
v___x_6672_ = lean_st_ref_put(v_a_6648_, v___x_6671_);
v___x_6673_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_6674_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_6646_, v___x_6673_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_, v_a_6653_, v_a_6654_, v_a_6655_, v_a_6656_, v_a_6657_);
if (lean_obj_tag(v___x_6674_) == 0)
{
lean_object* v_a_6675_; lean_object* v___x_6677_; uint8_t v_isShared_6678_; uint8_t v_isSharedCheck_6740_; 
v_a_6675_ = lean_ctor_get(v___x_6674_, 0);
v_isSharedCheck_6740_ = !lean_is_exclusive(v___x_6674_);
if (v_isSharedCheck_6740_ == 0)
{
v___x_6677_ = v___x_6674_;
v_isShared_6678_ = v_isSharedCheck_6740_;
goto v_resetjp_6676_;
}
else
{
lean_inc(v_a_6675_);
lean_dec(v___x_6674_);
v___x_6677_ = lean_box(0);
v_isShared_6678_ = v_isSharedCheck_6740_;
goto v_resetjp_6676_;
}
v_resetjp_6676_:
{
lean_object* v_fst_6679_; 
v_fst_6679_ = lean_ctor_get(v_a_6675_, 0);
lean_inc(v_fst_6679_);
lean_dec(v_a_6675_);
if (lean_obj_tag(v_fst_6679_) == 0)
{
lean_object* v___x_6680_; uint8_t v_didChange_6681_; 
v___x_6680_ = lean_st_ref_get(v_a_6648_);
v_didChange_6681_ = lean_ctor_get_uint8(v___x_6680_, sizeof(void*)*4);
lean_dec(v___x_6680_);
if (v_didChange_6681_ == 0)
{
lean_object* v_toCold_6682_; lean_object* v_options_6683_; uint8_t v_hasTrace_6684_; 
v_toCold_6682_ = lean_ctor_get(v_a_6656_, 0);
v_options_6683_ = lean_ctor_get(v_toCold_6682_, 2);
v_hasTrace_6684_ = lean_ctor_get_uint8(v_options_6683_, sizeof(void*)*1);
if (v_hasTrace_6684_ == 0)
{
lean_object* v___x_6685_; lean_object* v___x_6687_; 
v___x_6685_ = lean_box(v_didChange_6681_);
if (v_isShared_6678_ == 0)
{
lean_ctor_set(v___x_6677_, 0, v___x_6685_);
v___x_6687_ = v___x_6677_;
goto v_reusejp_6686_;
}
else
{
lean_object* v_reuseFailAlloc_6688_; 
v_reuseFailAlloc_6688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6688_, 0, v___x_6685_);
v___x_6687_ = v_reuseFailAlloc_6688_;
goto v_reusejp_6686_;
}
v_reusejp_6686_:
{
return v___x_6687_;
}
}
else
{
lean_object* v_inheritedTraceOptions_6689_; lean_object* v___x_6690_; lean_object* v___x_6691_; uint8_t v___x_6692_; 
v_inheritedTraceOptions_6689_ = lean_ctor_get(v_toCold_6682_, 11);
v___x_6690_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6691_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6689_, v_options_6683_, v___x_6691_);
if (v___x_6692_ == 0)
{
lean_object* v___x_6693_; lean_object* v___x_6695_; 
v___x_6693_ = lean_box(v_didChange_6681_);
if (v_isShared_6678_ == 0)
{
lean_ctor_set(v___x_6677_, 0, v___x_6693_);
v___x_6695_ = v___x_6677_;
goto v_reusejp_6694_;
}
else
{
lean_object* v_reuseFailAlloc_6696_; 
v_reuseFailAlloc_6696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6696_, 0, v___x_6693_);
v___x_6695_ = v_reuseFailAlloc_6696_;
goto v_reusejp_6694_;
}
v_reusejp_6694_:
{
return v___x_6695_;
}
}
else
{
lean_object* v___x_6697_; lean_object* v___x_6698_; 
lean_del_object(v___x_6677_);
v___x_6697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6698_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6690_, v___x_6697_, v_a_6654_, v_a_6655_, v_a_6656_, v_a_6657_);
if (lean_obj_tag(v___x_6698_) == 0)
{
lean_object* v___x_6700_; uint8_t v_isShared_6701_; uint8_t v_isSharedCheck_6706_; 
v_isSharedCheck_6706_ = !lean_is_exclusive(v___x_6698_);
if (v_isSharedCheck_6706_ == 0)
{
lean_object* v_unused_6707_; 
v_unused_6707_ = lean_ctor_get(v___x_6698_, 0);
lean_dec(v_unused_6707_);
v___x_6700_ = v___x_6698_;
v_isShared_6701_ = v_isSharedCheck_6706_;
goto v_resetjp_6699_;
}
else
{
lean_dec(v___x_6698_);
v___x_6700_ = lean_box(0);
v_isShared_6701_ = v_isSharedCheck_6706_;
goto v_resetjp_6699_;
}
v_resetjp_6699_:
{
lean_object* v___x_6702_; lean_object* v___x_6704_; 
v___x_6702_ = lean_box(v_didChange_6681_);
if (v_isShared_6701_ == 0)
{
lean_ctor_set(v___x_6700_, 0, v___x_6702_);
v___x_6704_ = v___x_6700_;
goto v_reusejp_6703_;
}
else
{
lean_object* v_reuseFailAlloc_6705_; 
v_reuseFailAlloc_6705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6705_, 0, v___x_6702_);
v___x_6704_ = v_reuseFailAlloc_6705_;
goto v_reusejp_6703_;
}
v_reusejp_6703_:
{
return v___x_6704_;
}
}
}
else
{
lean_object* v_a_6708_; lean_object* v___x_6710_; uint8_t v_isShared_6711_; uint8_t v_isSharedCheck_6715_; 
v_a_6708_ = lean_ctor_get(v___x_6698_, 0);
v_isSharedCheck_6715_ = !lean_is_exclusive(v___x_6698_);
if (v_isSharedCheck_6715_ == 0)
{
v___x_6710_ = v___x_6698_;
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
else
{
lean_inc(v_a_6708_);
lean_dec(v___x_6698_);
v___x_6710_ = lean_box(0);
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
v_resetjp_6709_:
{
lean_object* v___x_6713_; 
if (v_isShared_6711_ == 0)
{
v___x_6713_ = v___x_6710_;
goto v_reusejp_6712_;
}
else
{
lean_object* v_reuseFailAlloc_6714_; 
v_reuseFailAlloc_6714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_a_6708_);
v___x_6713_ = v_reuseFailAlloc_6714_;
goto v_reusejp_6712_;
}
v_reusejp_6712_:
{
return v___x_6713_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_6716_; lean_object* v_options_6717_; uint8_t v_hasTrace_6718_; 
lean_del_object(v___x_6677_);
v_toCold_6716_ = lean_ctor_get(v_a_6656_, 0);
v_options_6717_ = lean_ctor_get(v_toCold_6716_, 2);
v_hasTrace_6718_ = lean_ctor_get_uint8(v_options_6717_, sizeof(void*)*1);
if (v_hasTrace_6718_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; uint8_t v___x_6723_; 
v_inheritedTraceOptions_6720_ = lean_ctor_get(v_toCold_6716_, 11);
v___x_6721_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6722_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6720_, v_options_6717_, v___x_6722_);
if (v___x_6723_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6725_; lean_object* v___x_6726_; 
v___x_6725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6726_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6721_, v___x_6725_, v_a_6654_, v_a_6655_, v_a_6656_, v_a_6657_);
if (lean_obj_tag(v___x_6726_) == 0)
{
lean_dec_ref_known(v___x_6726_, 1);
goto _start;
}
else
{
lean_object* v_a_6728_; lean_object* v___x_6730_; uint8_t v_isShared_6731_; uint8_t v_isSharedCheck_6735_; 
v_a_6728_ = lean_ctor_get(v___x_6726_, 0);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6726_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6730_ = v___x_6726_;
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_a_6728_);
lean_dec(v___x_6726_);
v___x_6730_ = lean_box(0);
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
v_resetjp_6729_:
{
lean_object* v___x_6733_; 
if (v_isShared_6731_ == 0)
{
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
return v___x_6733_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_6736_; lean_object* v___x_6738_; 
v_val_6736_ = lean_ctor_get(v_fst_6679_, 0);
lean_inc(v_val_6736_);
lean_dec_ref_known(v_fst_6679_, 1);
if (v_isShared_6678_ == 0)
{
lean_ctor_set(v___x_6677_, 0, v_val_6736_);
v___x_6738_ = v___x_6677_;
goto v_reusejp_6737_;
}
else
{
lean_object* v_reuseFailAlloc_6739_; 
v_reuseFailAlloc_6739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6739_, 0, v_val_6736_);
v___x_6738_ = v_reuseFailAlloc_6739_;
goto v_reusejp_6737_;
}
v_reusejp_6737_:
{
return v___x_6738_;
}
}
}
}
else
{
lean_object* v_a_6741_; lean_object* v___x_6743_; uint8_t v_isShared_6744_; uint8_t v_isSharedCheck_6748_; 
v_a_6741_ = lean_ctor_get(v___x_6674_, 0);
v_isSharedCheck_6748_ = !lean_is_exclusive(v___x_6674_);
if (v_isSharedCheck_6748_ == 0)
{
v___x_6743_ = v___x_6674_;
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
else
{
lean_inc(v_a_6741_);
lean_dec(v___x_6674_);
v___x_6743_ = lean_box(0);
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
v_resetjp_6742_:
{
lean_object* v___x_6746_; 
if (v_isShared_6744_ == 0)
{
v___x_6746_ = v___x_6743_;
goto v_reusejp_6745_;
}
else
{
lean_object* v_reuseFailAlloc_6747_; 
v_reuseFailAlloc_6747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6747_, 0, v_a_6741_);
v___x_6746_ = v_reuseFailAlloc_6747_;
goto v_reusejp_6745_;
}
v_reusejp_6745_:
{
return v___x_6746_;
}
}
}
}
}
}
else
{
lean_object* v_a_6751_; lean_object* v___x_6753_; uint8_t v_isShared_6754_; uint8_t v_isSharedCheck_6758_; 
v_a_6751_ = lean_ctor_get(v___x_6660_, 0);
v_isSharedCheck_6758_ = !lean_is_exclusive(v___x_6660_);
if (v_isSharedCheck_6758_ == 0)
{
v___x_6753_ = v___x_6660_;
v_isShared_6754_ = v_isSharedCheck_6758_;
goto v_resetjp_6752_;
}
else
{
lean_inc(v_a_6751_);
lean_dec(v___x_6660_);
v___x_6753_ = lean_box(0);
v_isShared_6754_ = v_isSharedCheck_6758_;
goto v_resetjp_6752_;
}
v_resetjp_6752_:
{
lean_object* v___x_6756_; 
if (v_isShared_6754_ == 0)
{
v___x_6756_ = v___x_6753_;
goto v_reusejp_6755_;
}
else
{
lean_object* v_reuseFailAlloc_6757_; 
v_reuseFailAlloc_6757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6757_, 0, v_a_6751_);
v___x_6756_ = v_reuseFailAlloc_6757_;
goto v_reusejp_6755_;
}
v_reusejp_6755_:
{
return v___x_6756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6759_, lean_object* v_a_6760_, lean_object* v_a_6761_, lean_object* v_a_6762_, lean_object* v_a_6763_, lean_object* v_a_6764_, lean_object* v_a_6765_, lean_object* v_a_6766_, lean_object* v_a_6767_, lean_object* v_a_6768_, lean_object* v_a_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_){
_start:
{
lean_object* v_res_6772_; 
v_res_6772_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6759_, v_a_6760_, v_a_6761_, v_a_6762_, v_a_6763_, v_a_6764_, v_a_6765_, v_a_6766_, v_a_6767_, v_a_6768_, v_a_6769_, v_a_6770_);
lean_dec(v_a_6770_);
lean_dec_ref(v_a_6769_);
lean_dec(v_a_6768_);
lean_dec_ref(v_a_6767_);
lean_dec(v_a_6766_);
lean_dec_ref(v_a_6765_);
lean_dec(v_a_6764_);
lean_dec_ref(v_a_6763_);
lean_dec(v_a_6762_);
lean_dec(v_a_6761_);
lean_dec_ref(v_a_6760_);
lean_dec(v_passes_6759_);
return v_res_6772_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6773_, lean_object* v_msg_6774_, lean_object* v___y_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_){
_start:
{
lean_object* v___x_6787_; 
v___x_6787_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6773_, v_msg_6774_, v___y_6782_, v___y_6783_, v___y_6784_, v___y_6785_);
return v___x_6787_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6788_, lean_object* v_msg_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_){
_start:
{
lean_object* v_res_6802_; 
v_res_6802_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6788_, v_msg_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_);
lean_dec(v___y_6800_);
lean_dec_ref(v___y_6799_);
lean_dec(v___y_6798_);
lean_dec_ref(v___y_6797_);
lean_dec(v___y_6796_);
lean_dec_ref(v___y_6795_);
lean_dec(v___y_6794_);
lean_dec_ref(v___y_6793_);
lean_dec(v___y_6792_);
lean_dec(v___y_6791_);
lean_dec_ref(v___y_6790_);
return v_res_6802_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6803_, lean_object* v_x_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_, lean_object* v___y_6809_, lean_object* v___y_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_){
_start:
{
lean_object* v___x_6817_; 
v___x_6817_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6804_);
return v___x_6817_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6818_, lean_object* v_x_6819_, lean_object* v___y_6820_, lean_object* v___y_6821_, lean_object* v___y_6822_, lean_object* v___y_6823_, lean_object* v___y_6824_, lean_object* v___y_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_){
_start:
{
lean_object* v_res_6832_; 
v_res_6832_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6818_, v_x_6819_, v___y_6820_, v___y_6821_, v___y_6822_, v___y_6823_, v___y_6824_, v___y_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_);
lean_dec(v___y_6830_);
lean_dec_ref(v___y_6829_);
lean_dec(v___y_6828_);
lean_dec_ref(v___y_6827_);
lean_dec(v___y_6826_);
lean_dec_ref(v___y_6825_);
lean_dec(v___y_6824_);
lean_dec_ref(v___y_6823_);
lean_dec(v___y_6822_);
lean_dec(v___y_6821_);
lean_dec_ref(v___y_6820_);
return v_res_6832_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6833_, lean_object* v_as_x27_6834_, lean_object* v_b_6835_, lean_object* v_a_6836_, lean_object* v___y_6837_, lean_object* v___y_6838_, lean_object* v___y_6839_, lean_object* v___y_6840_, lean_object* v___y_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_, lean_object* v___y_6847_){
_start:
{
lean_object* v___x_6849_; 
v___x_6849_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6834_, v_b_6835_, v___y_6837_, v___y_6838_, v___y_6839_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_, v___y_6845_, v___y_6846_, v___y_6847_);
return v___x_6849_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6850_, lean_object* v_as_x27_6851_, lean_object* v_b_6852_, lean_object* v_a_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_){
_start:
{
lean_object* v_res_6866_; 
v_res_6866_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6850_, v_as_x27_6851_, v_b_6852_, v_a_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_);
lean_dec(v___y_6864_);
lean_dec_ref(v___y_6863_);
lean_dec(v___y_6862_);
lean_dec_ref(v___y_6861_);
lean_dec(v___y_6860_);
lean_dec_ref(v___y_6859_);
lean_dec(v___y_6858_);
lean_dec_ref(v___y_6857_);
lean_dec(v___y_6856_);
lean_dec(v___y_6855_);
lean_dec_ref(v___y_6854_);
lean_dec(v_as_x27_6851_);
lean_dec(v_as_6850_);
return v_res_6866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6867_, lean_object* v_data_6868_, lean_object* v_ref_6869_, lean_object* v_msg_6870_, lean_object* v___y_6871_, lean_object* v___y_6872_, lean_object* v___y_6873_, lean_object* v___y_6874_, lean_object* v___y_6875_, lean_object* v___y_6876_, lean_object* v___y_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_, lean_object* v___y_6880_, lean_object* v___y_6881_){
_start:
{
lean_object* v___x_6883_; 
v___x_6883_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6867_, v_data_6868_, v_ref_6869_, v_msg_6870_, v___y_6878_, v___y_6879_, v___y_6880_, v___y_6881_);
return v___x_6883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6884_, lean_object* v_data_6885_, lean_object* v_ref_6886_, lean_object* v_msg_6887_, lean_object* v___y_6888_, lean_object* v___y_6889_, lean_object* v___y_6890_, lean_object* v___y_6891_, lean_object* v___y_6892_, lean_object* v___y_6893_, lean_object* v___y_6894_, lean_object* v___y_6895_, lean_object* v___y_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_, lean_object* v___y_6899_){
_start:
{
lean_object* v_res_6900_; 
v_res_6900_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6884_, v_data_6885_, v_ref_6886_, v_msg_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_, v___y_6894_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
lean_dec(v___y_6898_);
lean_dec_ref(v___y_6897_);
lean_dec(v___y_6896_);
lean_dec_ref(v___y_6895_);
lean_dec(v___y_6894_);
lean_dec_ref(v___y_6893_);
lean_dec(v___y_6892_);
lean_dec_ref(v___y_6891_);
lean_dec(v___y_6890_);
lean_dec(v___y_6889_);
lean_dec_ref(v___y_6888_);
return v_res_6900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6901_, lean_object* v_a_6902_, lean_object* v_a_6903_, lean_object* v_a_6904_, lean_object* v_a_6905_, lean_object* v_a_6906_, lean_object* v_a_6907_, lean_object* v_a_6908_, lean_object* v_a_6909_, lean_object* v_a_6910_, lean_object* v_a_6911_, lean_object* v_a_6912_){
_start:
{
lean_object* v___x_6914_; 
v___x_6914_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6901_, v_a_6902_, v_a_6903_, v_a_6904_, v_a_6905_, v_a_6906_, v_a_6907_, v_a_6908_, v_a_6909_, v_a_6910_, v_a_6911_, v_a_6912_);
if (lean_obj_tag(v___x_6914_) == 0)
{
lean_object* v_a_6915_; lean_object* v___x_6916_; lean_object* v___x_6918_; uint8_t v_isShared_6919_; uint8_t v_isSharedCheck_6923_; 
v_a_6915_ = lean_ctor_get(v___x_6914_, 0);
lean_inc(v_a_6915_);
lean_dec_ref_known(v___x_6914_, 1);
v___x_6916_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_6902_, v_a_6903_);
v_isSharedCheck_6923_ = !lean_is_exclusive(v___x_6916_);
if (v_isSharedCheck_6923_ == 0)
{
lean_object* v_unused_6924_; 
v_unused_6924_ = lean_ctor_get(v___x_6916_, 0);
lean_dec(v_unused_6924_);
v___x_6918_ = v___x_6916_;
v_isShared_6919_ = v_isSharedCheck_6923_;
goto v_resetjp_6917_;
}
else
{
lean_dec(v___x_6916_);
v___x_6918_ = lean_box(0);
v_isShared_6919_ = v_isSharedCheck_6923_;
goto v_resetjp_6917_;
}
v_resetjp_6917_:
{
lean_object* v___x_6921_; 
if (v_isShared_6919_ == 0)
{
lean_ctor_set(v___x_6918_, 0, v_a_6915_);
v___x_6921_ = v___x_6918_;
goto v_reusejp_6920_;
}
else
{
lean_object* v_reuseFailAlloc_6922_; 
v_reuseFailAlloc_6922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6922_, 0, v_a_6915_);
v___x_6921_ = v_reuseFailAlloc_6922_;
goto v_reusejp_6920_;
}
v_reusejp_6920_:
{
return v___x_6921_;
}
}
}
else
{
return v___x_6914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6925_, lean_object* v_a_6926_, lean_object* v_a_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_, lean_object* v_a_6930_, lean_object* v_a_6931_, lean_object* v_a_6932_, lean_object* v_a_6933_, lean_object* v_a_6934_, lean_object* v_a_6935_, lean_object* v_a_6936_, lean_object* v_a_6937_){
_start:
{
lean_object* v_res_6938_; 
v_res_6938_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6925_, v_a_6926_, v_a_6927_, v_a_6928_, v_a_6929_, v_a_6930_, v_a_6931_, v_a_6932_, v_a_6933_, v_a_6934_, v_a_6935_, v_a_6936_);
lean_dec(v_a_6936_);
lean_dec_ref(v_a_6935_);
lean_dec(v_a_6934_);
lean_dec_ref(v_a_6933_);
lean_dec(v_a_6932_);
lean_dec_ref(v_a_6931_);
lean_dec(v_a_6930_);
lean_dec_ref(v_a_6929_);
lean_dec(v_a_6928_);
lean_dec(v_a_6927_);
lean_dec_ref(v_a_6926_);
lean_dec(v_passes_6925_);
return v_res_6938_;
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
