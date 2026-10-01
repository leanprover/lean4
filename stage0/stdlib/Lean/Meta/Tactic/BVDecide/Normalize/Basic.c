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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx(lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(0u);
return v___x_41_;
}
else
{
lean_object* v___x_42_; 
v___x_42_ = lean_unsigned_to_nat(1u);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx(v_x_43_);
lean_dec_ref(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(lean_object* v_t_45_, lean_object* v_k_46_){
_start:
{
if (lean_obj_tag(v_t_45_) == 0)
{
lean_object* v_mvar_47_; lean_object* v___x_48_; 
v_mvar_47_ = lean_ctor_get(v_t_45_, 0);
lean_inc(v_mvar_47_);
lean_dec_ref_known(v_t_45_, 1);
v___x_48_ = lean_apply_1(v_k_46_, v_mvar_47_);
return v___x_48_;
}
else
{
lean_object* v_goal_49_; lean_object* v___x_50_; 
v_goal_49_ = lean_ctor_get(v_t_45_, 0);
lean_inc_ref(v_goal_49_);
lean_dec_ref_known(v_t_45_, 1);
v___x_50_ = lean_apply_1(v_k_46_, v_goal_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim(lean_object* v_motive_51_, lean_object* v_ctorIdx_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_53_, v_k_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___boxed(lean_object* v_motive_57_, lean_object* v_ctorIdx_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_k_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim(v_motive_57_, v_ctorIdx_58_, v_t_59_, v_h_60_, v_k_61_);
lean_dec(v_ctorIdx_58_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim___redArg(lean_object* v_t_63_, lean_object* v_mvarIdTarget_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_63_, v_mvarIdTarget_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_mvarIdTarget_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_67_, v_mvarIdTarget_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim___redArg(lean_object* v_t_71_, lean_object* v_grindTarget_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_71_, v_grindTarget_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_grindTarget_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_75_, v_grindTarget_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v_mvar_84_; 
v_mvar_84_ = lean_ctor_get(v_x_83_, 0);
lean_inc(v_mvar_84_);
return v_mvar_84_;
}
else
{
lean_object* v_goal_85_; lean_object* v_mvarId_86_; 
v_goal_85_ = lean_ctor_get(v_x_83_, 0);
v_mvarId_86_ = lean_ctor_get(v_goal_85_, 1);
lean_inc(v_mvarId_86_);
return v_mvarId_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId___boxed(lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_x_87_);
lean_dec_ref(v_x_87_);
return v_res_88_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind(lean_object* v_x_89_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
}
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
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar(lean_object* v_x_95_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar___boxed(lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar(v_x_98_);
lean_dec_ref(v_x_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_unsigned_to_nat(0u);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_unsigned_to_nat(1u);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object* v_x_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(v_x_104_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(lean_object* v_x_143_){
_start:
{
switch(lean_obj_tag(v_x_143_))
{
case 0:
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(0u);
return v___x_144_;
}
case 1:
{
lean_object* v___x_145_; 
v___x_145_ = lean_unsigned_to_nat(1u);
return v___x_145_;
}
case 2:
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(2u);
return v___x_146_;
}
case 3:
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(3u);
return v___x_147_;
}
case 4:
{
lean_object* v___x_148_; 
v___x_148_ = lean_unsigned_to_nat(4u);
return v___x_148_;
}
default: 
{
lean_object* v___x_149_; 
v___x_149_ = lean_unsigned_to_nat(5u);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___boxed(lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(v_x_150_);
lean_dec(v_x_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object* v_t_152_, lean_object* v_k_153_){
_start:
{
switch(lean_obj_tag(v_t_152_))
{
case 0:
{
lean_object* v_fvar_154_; lean_object* v___x_155_; 
v_fvar_154_ = lean_ctor_get(v_t_152_, 0);
lean_inc(v_fvar_154_);
lean_dec_ref_known(v_t_152_, 1);
v___x_155_ = lean_apply_1(v_k_153_, v_fvar_154_);
return v___x_155_;
}
case 1:
{
lean_object* v_n_156_; lean_object* v___x_157_; 
v_n_156_ = lean_ctor_get(v_t_152_, 0);
lean_inc(v_n_156_);
lean_dec_ref_known(v_t_152_, 1);
v___x_157_ = lean_apply_1(v_k_153_, v_n_156_);
return v___x_157_;
}
case 2:
{
lean_object* v_e_158_; lean_object* v___x_159_; 
v_e_158_ = lean_ctor_get(v_t_152_, 0);
lean_inc_ref(v_e_158_);
lean_dec_ref_known(v_t_152_, 1);
v___x_159_ = lean_apply_1(v_k_153_, v_e_158_);
return v___x_159_;
}
case 3:
{
lean_object* v_s_160_; lean_object* v___x_161_; 
v_s_160_ = lean_ctor_get(v_t_152_, 0);
lean_inc(v_s_160_);
lean_dec_ref_known(v_t_152_, 1);
v___x_161_ = lean_apply_1(v_k_153_, v_s_160_);
return v___x_161_;
}
default: 
{
lean_dec(v_t_152_);
return v_k_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object* v_motive_162_, lean_object* v_ctorIdx_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_k_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_164_, v_k_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object* v_motive_168_, lean_object* v_ctorIdx_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_k_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(v_motive_168_, v_ctorIdx_169_, v_t_170_, v_h_171_, v_k_172_);
lean_dec(v_ctorIdx_169_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object* v_t_174_, lean_object* v_lctx_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_174_, v_lctx_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object* v_motive_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_lctx_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_178_, v_lctx_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object* v_t_182_, lean_object* v_enumDomain_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_182_, v_enumDomain_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object* v_motive_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_enumDomain_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_186_, v_enumDomain_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object* v_t_190_, lean_object* v_structureProjection_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_190_, v_structureProjection_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object* v_motive_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_structureProjection_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_194_, v_structureProjection_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object* v_t_198_, lean_object* v_andFlattened_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_198_, v_andFlattened_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object* v_motive_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_andFlattened_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_202_, v_andFlattened_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim___redArg(lean_object* v_t_206_, lean_object* v_grind_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_206_, v_grind_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim(lean_object* v_motive_209_, lean_object* v_t_210_, lean_object* v_h_211_, lean_object* v_grind_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_210_, v_grind_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_cegar_elim___redArg(lean_object* v_t_214_, lean_object* v_cegar_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_214_, v_cegar_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_cegar_elim(lean_object* v_motive_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_cegar_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_218_, v_cegar_220_);
return v___x_221_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object* v_x_226_){
_start:
{
switch(lean_obj_tag(v_x_226_))
{
case 0:
{
lean_object* v_fvar_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; 
v_fvar_227_ = lean_ctor_get(v_x_226_, 0);
v___x_228_ = 0ULL;
v___x_229_ = l_Lean_instHashableFVarId_hash(v_fvar_227_);
v___x_230_ = lean_uint64_mix_hash(v___x_228_, v___x_229_);
return v___x_230_;
}
case 1:
{
lean_object* v_n_231_; uint64_t v___x_232_; 
v_n_231_ = lean_ctor_get(v_x_226_, 0);
v___x_232_ = 1ULL;
if (lean_obj_tag(v_n_231_) == 0)
{
uint64_t v___x_233_; 
v___x_233_ = 13067028307566252276ULL;
return v___x_233_;
}
else
{
uint64_t v_hash_234_; uint64_t v___x_235_; 
v_hash_234_ = lean_ctor_get_uint64(v_n_231_, sizeof(void*)*2);
v___x_235_ = lean_uint64_mix_hash(v___x_232_, v_hash_234_);
return v___x_235_;
}
}
case 2:
{
lean_object* v_e_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; 
v_e_236_ = lean_ctor_get(v_x_226_, 0);
v___x_237_ = 2ULL;
v___x_238_ = l_Lean_Expr_hash(v_e_236_);
v___x_239_ = lean_uint64_mix_hash(v___x_237_, v___x_238_);
return v___x_239_;
}
case 3:
{
lean_object* v_s_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; 
v_s_240_ = lean_ctor_get(v_x_226_, 0);
v___x_241_ = 3ULL;
v___x_242_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_s_240_);
v___x_243_ = lean_uint64_mix_hash(v___x_241_, v___x_242_);
return v___x_243_;
}
case 4:
{
uint64_t v___x_244_; 
v___x_244_ = 4ULL;
return v___x_244_;
}
default: 
{
uint64_t v___x_245_; 
v___x_245_ = 5ULL;
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object* v_x_246_){
_start:
{
uint64_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_246_);
lean_dec(v_x_246_);
v_r_248_ = lean_box_uint64(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
switch(lean_obj_tag(v_x_251_))
{
case 0:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v_fvar_253_; lean_object* v_fvar_254_; uint8_t v___x_255_; 
v_fvar_253_ = lean_ctor_get(v_x_251_, 0);
v_fvar_254_ = lean_ctor_get(v_x_252_, 0);
v___x_255_ = l_Lean_instBEqFVarId_beq(v_fvar_253_, v_fvar_254_);
return v___x_255_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
case 1:
{
if (lean_obj_tag(v_x_252_) == 1)
{
lean_object* v_n_257_; lean_object* v_n_258_; uint8_t v___x_259_; 
v_n_257_ = lean_ctor_get(v_x_251_, 0);
v_n_258_ = lean_ctor_get(v_x_252_, 0);
v___x_259_ = lean_name_eq(v_n_257_, v_n_258_);
return v___x_259_;
}
else
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
}
case 2:
{
if (lean_obj_tag(v_x_252_) == 2)
{
lean_object* v_e_261_; lean_object* v_e_262_; uint8_t v___x_263_; 
v_e_261_ = lean_ctor_get(v_x_251_, 0);
v_e_262_ = lean_ctor_get(v_x_252_, 0);
v___x_263_ = lean_expr_eqv(v_e_261_, v_e_262_);
return v___x_263_;
}
else
{
uint8_t v___x_264_; 
v___x_264_ = 0;
return v___x_264_;
}
}
case 3:
{
if (lean_obj_tag(v_x_252_) == 3)
{
lean_object* v_s_265_; lean_object* v_s_266_; 
v_s_265_ = lean_ctor_get(v_x_251_, 0);
v_s_266_ = lean_ctor_get(v_x_252_, 0);
v_x_251_ = v_s_265_;
v_x_252_ = v_s_266_;
goto _start;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = 0;
return v___x_268_;
}
}
case 4:
{
if (lean_obj_tag(v_x_252_) == 4)
{
uint8_t v___x_269_; 
v___x_269_ = 1;
return v___x_269_;
}
else
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
}
default: 
{
if (lean_obj_tag(v_x_252_) == 5)
{
uint8_t v___x_271_; 
v___x_271_ = 1;
return v___x_271_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_273_, v_x_274_);
lean_dec(v_x_274_);
lean_dec(v_x_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object* v_s_279_){
_start:
{
if (lean_obj_tag(v_s_279_) == 3)
{
lean_object* v_s_280_; 
v_s_280_ = lean_ctor_get(v_s_279_, 0);
v_s_279_ = v_s_280_;
goto _start;
}
else
{
lean_inc(v_s_279_);
return v_s_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object* v_s_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_282_);
lean_dec(v_s_282_);
return v_res_283_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2));
v___x_289_ = l_Lean_stringToMessageData(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4));
v___x_292_ = l_Lean_stringToMessageData(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8));
v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__10));
v___x_301_ = l_Lean_stringToMessageData(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object* v_s_302_){
_start:
{
switch(lean_obj_tag(v_s_302_))
{
case 0:
{
lean_object* v_fvar_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_fvar_303_ = lean_ctor_get(v_s_302_, 0);
lean_inc(v_fvar_303_);
lean_dec_ref_known(v_s_302_, 1);
v___x_304_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1);
v___x_305_ = l_Lean_mkFVar(v_fvar_303_);
v___x_306_ = l_Lean_MessageData_ofExpr(v___x_305_);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_304_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
return v___x_307_;
}
case 1:
{
lean_object* v_n_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_n_308_ = lean_ctor_get(v_s_302_, 0);
lean_inc(v_n_308_);
lean_dec_ref_known(v_s_302_, 1);
v___x_309_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3);
v___x_310_ = l_Lean_MessageData_ofName(v_n_308_);
v___x_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
return v___x_311_;
}
case 2:
{
lean_object* v_e_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_e_312_ = lean_ctor_get(v_s_302_, 0);
lean_inc_ref(v_e_312_);
lean_dec_ref_known(v_s_302_, 1);
v___x_313_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5);
v___x_314_ = l_Lean_MessageData_ofExpr(v_e_312_);
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
return v___x_315_;
}
case 3:
{
lean_object* v_s_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_s_316_ = lean_ctor_get(v_s_302_, 0);
lean_inc(v_s_316_);
lean_dec_ref_known(v_s_302_, 1);
v___x_317_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7);
v___x_318_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_316_);
lean_dec(v_s_316_);
v___x_319_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v___x_318_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_317_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
case 4:
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9);
return v___x_321_;
}
default: 
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11);
return v___x_322_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_box(0);
v___x_329_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1));
v___x_330_ = l_Lean_Expr_const___override(v___x_329_, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default));
v___x_332_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2);
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
lean_ctor_set(v___x_334_, 2, v___x_332_);
lean_ctor_set(v___x_334_, 3, v___x_331_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp(void){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
return v___x_336_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object* v_lhs_337_, lean_object* v_rhs_338_){
_start:
{
lean_object* v_type_339_; lean_object* v_type_340_; uint8_t v___x_341_; 
v_type_339_ = lean_ctor_get(v_lhs_337_, 1);
v_type_340_ = lean_ctor_get(v_rhs_338_, 1);
v___x_341_ = lean_expr_eqv(v_type_339_, v_type_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object* v_lhs_342_, lean_object* v_rhs_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_342_, v_rhs_343_);
lean_dec_ref(v_rhs_343_);
lean_dec_ref(v_lhs_342_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object* v_hyp_348_){
_start:
{
lean_object* v_type_349_; uint64_t v___x_350_; 
v_type_349_ = lean_ctor_get(v_hyp_348_, 1);
v___x_350_ = l_Lean_Expr_hash(v_type_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object* v_hyp_351_){
_start:
{
uint64_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_351_);
lean_dec_ref(v_hyp_351_);
v_r_353_ = lean_box_uint64(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object* v_hyp_356_){
_start:
{
lean_object* v_type_357_; lean_object* v___x_358_; 
v_type_357_ = lean_ctor_get(v_hyp_356_, 1);
lean_inc_ref(v_type_357_);
lean_dec_ref(v_hyp_356_);
v___x_358_ = l_Lean_MessageData_ofExpr(v_type_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx(lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_unsigned_to_nat(0u);
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
v___x_363_ = lean_unsigned_to_nat(1u);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___boxed(lean_object* v_x_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx(v_x_364_);
lean_dec(v_x_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(lean_object* v_t_366_, lean_object* v_k_367_){
_start:
{
if (lean_obj_tag(v_t_366_) == 0)
{
lean_object* v_restrictedTypes_368_; lean_object* v___x_369_; 
v_restrictedTypes_368_ = lean_ctor_get(v_t_366_, 0);
lean_inc(v_restrictedTypes_368_);
lean_dec_ref_known(v_t_366_, 1);
v___x_369_ = lean_apply_1(v_k_367_, v_restrictedTypes_368_);
return v___x_369_;
}
else
{
return v_k_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(lean_object* v_motive_370_, lean_object* v_ctorIdx_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_k_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_372_, v_k_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___boxed(lean_object* v_motive_376_, lean_object* v_ctorIdx_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_k_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(v_motive_376_, v_ctorIdx_377_, v_t_378_, v_h_379_, v_k_380_);
lean_dec(v_ctorIdx_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim___redArg(lean_object* v_t_382_, lean_object* v_solve_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_382_, v_solve_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim(lean_object* v_motive_385_, lean_object* v_t_386_, lean_object* v_h_387_, lean_object* v_solve_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_386_, v_solve_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim___redArg(lean_object* v_t_390_, lean_object* v_push_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_390_, v_push_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim(lean_object* v_motive_393_, lean_object* v_t_394_, lean_object* v_h_395_, lean_object* v_push_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_394_, v_push_396_);
return v___x_397_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
uint8_t v___x_399_; 
v___x_399_ = 0;
return v___x_399_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = 1;
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush___boxed(lean_object* v_x_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_x_401_);
lean_dec(v_x_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
lean_object* v_restrictedTypes_405_; 
v_restrictedTypes_405_ = lean_ctor_get(v_x_404_, 0);
lean_inc(v_restrictedTypes_405_);
return v_restrictedTypes_405_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_box(0);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes___boxed(lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_x_407_);
lean_dec(v_x_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(lean_object* v_mode_409_, lean_object* v_config_410_){
_start:
{
if (lean_obj_tag(v_mode_409_) == 0)
{
return v_config_410_;
}
else
{
lean_object* v_timeout_411_; uint8_t v_trimProofs_412_; uint8_t v_binaryProofs_413_; uint8_t v_acNf_414_; uint8_t v_graphviz_415_; lean_object* v_maxSteps_416_; uint8_t v_shortCircuit_417_; uint8_t v_solverMode_418_; uint8_t v_uf_419_; lean_object* v_cegarRounds_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_428_; 
v_timeout_411_ = lean_ctor_get(v_config_410_, 0);
v_trimProofs_412_ = lean_ctor_get_uint8(v_config_410_, sizeof(void*)*3);
v_binaryProofs_413_ = lean_ctor_get_uint8(v_config_410_, sizeof(void*)*3 + 1);
v_acNf_414_ = lean_ctor_get_uint8(v_config_410_, sizeof(void*)*3 + 2);
v_graphviz_415_ = lean_ctor_get_uint8(v_config_410_, sizeof(void*)*3 + 8);
v_maxSteps_416_ = lean_ctor_get(v_config_410_, 1);
v_shortCircuit_417_ = lean_ctor_get_uint8(v_config_410_, sizeof(void*)*3 + 9);
v_solverMode_418_ = lean_ctor_get_uint8(v_config_410_, sizeof(void*)*3 + 10);
v_uf_419_ = lean_ctor_get_uint8(v_config_410_, sizeof(void*)*3 + 11);
v_cegarRounds_420_ = lean_ctor_get(v_config_410_, 2);
v_isSharedCheck_428_ = !lean_is_exclusive(v_config_410_);
if (v_isSharedCheck_428_ == 0)
{
v___x_422_ = v_config_410_;
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_cegarRounds_420_);
lean_inc(v_maxSteps_416_);
lean_inc(v_timeout_411_);
lean_dec(v_config_410_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
uint8_t v___x_424_; lean_object* v___x_426_; 
v___x_424_ = 0;
if (v_isShared_423_ == 0)
{
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_timeout_411_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_maxSteps_416_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_cegarRounds_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3, v_trimProofs_412_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 1, v_binaryProofs_413_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 2, v_acNf_414_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 8, v_graphviz_415_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 9, v_shortCircuit_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 10, v_solverMode_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*3 + 11, v_uf_419_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*3 + 3, v___x_424_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*3 + 4, v___x_424_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*3 + 5, v___x_424_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*3 + 6, v___x_424_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*3 + 7, v___x_424_);
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig___boxed(lean_object* v_mode_429_, lean_object* v_config_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_429_, v_config_430_);
lean_dec(v_mode_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object* v_mode_432_, lean_object* v_config_433_, lean_object* v_keepCaches_434_){
_start:
{
uint8_t v___y_436_; 
if (lean_obj_tag(v_keepCaches_434_) == 0)
{
uint8_t v_uf_439_; 
v_uf_439_ = lean_ctor_get_uint8(v_config_433_, sizeof(void*)*3 + 11);
if (v_uf_439_ == 0)
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_432_);
v___y_436_ = v___x_440_;
goto v___jp_435_;
}
else
{
v___y_436_ = v_uf_439_;
goto v___jp_435_;
}
}
else
{
lean_object* v_val_441_; uint8_t v___x_442_; 
v_val_441_ = lean_ctor_get(v_keepCaches_434_, 0);
v___x_442_ = lean_unbox(v_val_441_);
v___y_436_ = v___x_442_;
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_432_, v_config_433_);
v___x_438_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_mode_432_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*2, v___y_436_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new___boxed(lean_object* v_mode_443_, lean_object* v_config_444_, lean_object* v_keepCaches_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_443_, v_config_444_, v_keepCaches_445_);
lean_dec(v_keepCaches_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object* v_ctx_447_){
_start:
{
lean_object* v_config_448_; lean_object* v_restrictedTypes_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_config_448_ = lean_ctor_get(v_ctx_447_, 5);
lean_inc_ref(v_config_448_);
v_restrictedTypes_449_ = lean_ctor_get(v_ctx_447_, 6);
lean_inc(v_restrictedTypes_449_);
lean_dec_ref(v_ctx_447_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_restrictedTypes_449_);
v___x_451_ = lean_box(0);
v___x_452_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_450_, v_config_448_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx(uint8_t v_x_453_){
_start:
{
if (v_x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_unsigned_to_nat(0u);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = lean_unsigned_to_nat(1u);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___boxed(lean_object* v_x_456_){
_start:
{
uint8_t v_x_boxed_457_; lean_object* v_res_458_; 
v_x_boxed_457_ = lean_unbox(v_x_456_);
v_res_458_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx(v_x_boxed_457_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(lean_object* v_motive_462_, lean_object* v_ctorIdx_463_, uint8_t v_t_464_, lean_object* v_h_465_, lean_object* v_k_466_){
_start:
{
lean_inc(v_k_466_);
return v_k_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___boxed(lean_object* v_motive_467_, lean_object* v_ctorIdx_468_, lean_object* v_t_469_, lean_object* v_h_470_, lean_object* v_k_471_){
_start:
{
uint8_t v_t_boxed_472_; lean_object* v_res_473_; 
v_t_boxed_472_ = lean_unbox(v_t_469_);
v_res_473_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(v_motive_467_, v_ctorIdx_468_, v_t_boxed_472_, v_h_470_, v_k_471_);
lean_dec(v_k_471_);
lean_dec(v_ctorIdx_468_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_474_){
_start:
{
lean_inc(v_rewrite_474_);
return v_rewrite_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(v_rewrite_475_);
lean_dec(v_rewrite_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(lean_object* v_motive_477_, uint8_t v_t_478_, lean_object* v_h_479_, lean_object* v_rewrite_480_){
_start:
{
lean_inc(v_rewrite_480_);
return v_rewrite_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___boxed(lean_object* v_motive_481_, lean_object* v_t_482_, lean_object* v_h_483_, lean_object* v_rewrite_484_){
_start:
{
uint8_t v_t_boxed_485_; lean_object* v_res_486_; 
v_t_boxed_485_ = lean_unbox(v_t_482_);
v_res_486_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(v_motive_481_, v_t_boxed_485_, v_h_483_, v_rewrite_484_);
lean_dec(v_rewrite_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(lean_object* v_ac_487_){
_start:
{
lean_inc(v_ac_487_);
return v_ac_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg___boxed(lean_object* v_ac_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(v_ac_488_);
lean_dec(v_ac_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(lean_object* v_motive_490_, uint8_t v_t_491_, lean_object* v_h_492_, lean_object* v_ac_493_){
_start:
{
lean_inc(v_ac_493_);
return v_ac_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___boxed(lean_object* v_motive_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_ac_497_){
_start:
{
uint8_t v_t_boxed_498_; lean_object* v_res_499_; 
v_t_boxed_498_ = lean_unbox(v_t_495_);
v_res_499_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(v_motive_494_, v_t_boxed_498_, v_h_496_, v_ac_497_);
lean_dec(v_ac_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx(uint8_t v_x_500_){
_start:
{
if (v_x_500_ == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_unsigned_to_nat(0u);
return v___x_501_;
}
else
{
lean_object* v___x_502_; 
v___x_502_ = lean_unsigned_to_nat(1u);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___boxed(lean_object* v_x_503_){
_start:
{
uint8_t v_x_boxed_504_; lean_object* v_res_505_; 
v_x_boxed_504_ = lean_unbox(v_x_503_);
v_res_505_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx(v_x_boxed_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(lean_object* v_k_506_){
_start:
{
lean_inc(v_k_506_);
return v_k_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(v_k_507_);
lean_dec(v_k_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(lean_object* v_motive_509_, lean_object* v_ctorIdx_510_, uint8_t v_t_511_, lean_object* v_h_512_, lean_object* v_k_513_){
_start:
{
lean_inc(v_k_513_);
return v_k_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___boxed(lean_object* v_motive_514_, lean_object* v_ctorIdx_515_, lean_object* v_t_516_, lean_object* v_h_517_, lean_object* v_k_518_){
_start:
{
uint8_t v_t_boxed_519_; lean_object* v_res_520_; 
v_t_boxed_519_ = lean_unbox(v_t_516_);
v_res_520_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(v_motive_514_, v_ctorIdx_515_, v_t_boxed_519_, v_h_517_, v_k_518_);
lean_dec(v_k_518_);
lean_dec(v_ctorIdx_515_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_521_){
_start:
{
lean_inc(v_rewrite_521_);
return v_rewrite_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(v_rewrite_522_);
lean_dec(v_rewrite_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(lean_object* v_motive_524_, uint8_t v_t_525_, lean_object* v_h_526_, lean_object* v_rewrite_527_){
_start:
{
lean_inc(v_rewrite_527_);
return v_rewrite_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___boxed(lean_object* v_motive_528_, lean_object* v_t_529_, lean_object* v_h_530_, lean_object* v_rewrite_531_){
_start:
{
uint8_t v_t_boxed_532_; lean_object* v_res_533_; 
v_t_boxed_532_ = lean_unbox(v_t_529_);
v_res_533_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(v_motive_528_, v_t_boxed_532_, v_h_530_, v_rewrite_531_);
lean_dec(v_rewrite_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(lean_object* v_reduction_534_){
_start:
{
lean_inc(v_reduction_534_);
return v_reduction_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg___boxed(lean_object* v_reduction_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(v_reduction_535_);
lean_dec(v_reduction_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(lean_object* v_motive_537_, uint8_t v_t_538_, lean_object* v_h_539_, lean_object* v_reduction_540_){
_start:
{
lean_inc(v_reduction_540_);
return v_reduction_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___boxed(lean_object* v_motive_541_, lean_object* v_t_542_, lean_object* v_h_543_, lean_object* v_reduction_544_){
_start:
{
uint8_t v_t_boxed_545_; lean_object* v_res_546_; 
v_t_boxed_545_ = lean_unbox(v_t_542_);
v_res_546_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(v_motive_541_, v_t_boxed_545_, v_h_543_, v_reduction_544_);
lean_dec(v_reduction_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(uint8_t v_x_547_, lean_object* v_x_548_){
_start:
{
if (v_x_547_ == 0)
{
lean_object* v_rewriteSimp_549_; 
v_rewriteSimp_549_ = lean_ctor_get(v_x_548_, 1);
lean_inc_ref(v_rewriteSimp_549_);
return v_rewriteSimp_549_;
}
else
{
lean_object* v_ac_550_; 
v_ac_550_ = lean_ctor_get(v_x_548_, 3);
lean_inc_ref(v_ac_550_);
return v_ac_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get___boxed(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
uint8_t v_x_15__boxed_553_; lean_object* v_res_554_; 
v_x_15__boxed_553_ = lean_unbox(v_x_551_);
v_res_554_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_x_15__boxed_553_, v_x_552_);
lean_dec_ref(v_x_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(uint8_t v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
if (v_x_555_ == 0)
{
lean_object* v_reduction_558_; lean_object* v_rewriteDSimp_559_; lean_object* v_ac_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_reduction_558_ = lean_ctor_get(v_x_557_, 0);
v_rewriteDSimp_559_ = lean_ctor_get(v_x_557_, 2);
v_ac_560_ = lean_ctor_get(v_x_557_, 3);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_557_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_x_557_, 1);
lean_dec(v_unused_568_);
v___x_562_ = v_x_557_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_ac_560_);
lean_inc(v_rewriteDSimp_559_);
lean_inc(v_reduction_558_);
lean_dec(v_x_557_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v_x_556_);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_reduction_558_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_x_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_rewriteDSimp_559_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_ac_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_reduction_569_; lean_object* v_rewriteSimp_570_; lean_object* v_rewriteDSimp_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_reduction_569_ = lean_ctor_get(v_x_557_, 0);
v_rewriteSimp_570_ = lean_ctor_get(v_x_557_, 1);
v_rewriteDSimp_571_ = lean_ctor_get(v_x_557_, 2);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_557_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_x_557_, 3);
lean_dec(v_unused_579_);
v___x_573_ = v_x_557_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_rewriteDSimp_571_);
lean_inc(v_rewriteSimp_570_);
lean_inc(v_reduction_569_);
lean_dec(v_x_557_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 3, v_x_556_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_reduction_569_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_rewriteSimp_570_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_rewriteDSimp_571_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v_x_556_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set___boxed(lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
uint8_t v_x_28__boxed_583_; lean_object* v_res_584_; 
v_x_28__boxed_583_ = lean_unbox(v_x_580_);
v_res_584_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_x_28__boxed_583_, v_x_581_, v_x_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(uint8_t v_x_585_, lean_object* v_x_586_){
_start:
{
if (v_x_585_ == 0)
{
lean_object* v_rewriteDSimp_587_; 
v_rewriteDSimp_587_ = lean_ctor_get(v_x_586_, 2);
lean_inc_ref(v_rewriteDSimp_587_);
return v_rewriteDSimp_587_;
}
else
{
lean_object* v_reduction_588_; 
v_reduction_588_ = lean_ctor_get(v_x_586_, 0);
lean_inc_ref(v_reduction_588_);
return v_reduction_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get___boxed(lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
uint8_t v_x_15__boxed_591_; lean_object* v_res_592_; 
v_x_15__boxed_591_ = lean_unbox(v_x_589_);
v_res_592_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_x_15__boxed_591_, v_x_590_);
lean_dec_ref(v_x_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(uint8_t v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
if (v_x_593_ == 0)
{
lean_object* v_reduction_596_; lean_object* v_rewriteSimp_597_; lean_object* v_ac_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_reduction_596_ = lean_ctor_get(v_x_595_, 0);
v_rewriteSimp_597_ = lean_ctor_get(v_x_595_, 1);
v_ac_598_ = lean_ctor_get(v_x_595_, 3);
v_isSharedCheck_605_ = !lean_is_exclusive(v_x_595_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v_x_595_, 2);
lean_dec(v_unused_606_);
v___x_600_ = v_x_595_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_ac_598_);
lean_inc(v_rewriteSimp_597_);
lean_inc(v_reduction_596_);
lean_dec(v_x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 2, v_x_594_);
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_reduction_596_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_rewriteSimp_597_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_x_594_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_ac_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_rewriteSimp_607_; lean_object* v_rewriteDSimp_608_; lean_object* v_ac_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_rewriteSimp_607_ = lean_ctor_get(v_x_595_, 1);
v_rewriteDSimp_608_ = lean_ctor_get(v_x_595_, 2);
v_ac_609_ = lean_ctor_get(v_x_595_, 3);
v_isSharedCheck_616_ = !lean_is_exclusive(v_x_595_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v_x_595_, 0);
lean_dec(v_unused_617_);
v___x_611_ = v_x_595_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_ac_609_);
lean_inc(v_rewriteDSimp_608_);
lean_inc(v_rewriteSimp_607_);
lean_dec(v_x_595_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_x_594_);
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_x_594_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_rewriteSimp_607_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_rewriteDSimp_608_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_ac_609_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set___boxed(lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
uint8_t v_x_28__boxed_621_; lean_object* v_res_622_; 
v_x_28__boxed_621_ = lean_unbox(v_x_618_);
v_res_622_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_x_28__boxed_621_, v_x_619_, v_x_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object* v_hyp_628_, lean_object* v_result_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
if (lean_obj_tag(v_result_629_) == 0)
{
lean_object* v___x_636_; 
lean_dec_ref_known(v_result_629_, 0);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_hyp_628_);
return v___x_636_;
}
else
{
lean_object* v_e_x27_637_; lean_object* v_proof_638_; lean_object* v_name_639_; lean_object* v_type_640_; lean_object* v_value_641_; lean_object* v_source_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_671_; 
v_e_x27_637_ = lean_ctor_get(v_result_629_, 0);
lean_inc_ref(v_e_x27_637_);
v_proof_638_ = lean_ctor_get(v_result_629_, 1);
lean_inc_ref(v_proof_638_);
lean_dec_ref_known(v_result_629_, 2);
v_name_639_ = lean_ctor_get(v_hyp_628_, 0);
v_type_640_ = lean_ctor_get(v_hyp_628_, 1);
v_value_641_ = lean_ctor_get(v_hyp_628_, 2);
v_source_642_ = lean_ctor_get(v_hyp_628_, 3);
v_isSharedCheck_671_ = !lean_is_exclusive(v_hyp_628_);
if (v_isSharedCheck_671_ == 0)
{
v___x_644_ = v_hyp_628_;
v_isShared_645_ = v_isSharedCheck_671_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_source_642_);
lean_inc(v_value_641_);
lean_inc(v_type_640_);
lean_inc(v_name_639_);
lean_dec(v_hyp_628_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_671_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; 
lean_inc_ref(v_type_640_);
v___x_646_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_640_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_662_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_662_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_662_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_662_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_651_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2));
v___x_652_ = lean_box(0);
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v_a_647_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_mkConst(v___x_651_, v___x_653_);
lean_inc_ref(v_e_x27_637_);
v___x_655_ = l_Lean_mkApp4(v___x_654_, v_type_640_, v_e_x27_637_, v_proof_638_, v_value_641_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 2, v___x_655_);
lean_ctor_set(v___x_644_, 1, v_e_x27_637_);
v___x_657_ = v___x_644_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_name_639_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_e_x27_637_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_source_642_);
v___x_657_ = v_reuseFailAlloc_661_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_659_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_657_);
v___x_659_ = v___x_649_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_del_object(v___x_644_);
lean_dec(v_source_642_);
lean_dec_ref(v_value_641_);
lean_dec_ref(v_type_640_);
lean_dec(v_name_639_);
lean_dec_ref(v_proof_638_);
lean_dec_ref(v_e_x27_637_);
v_a_663_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_646_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_646_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object* v_hyp_672_, lean_object* v_result_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_672_, v_result_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object* v_hyp_681_, lean_object* v_result_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_681_, v_result_682_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object* v_hyp_691_, lean_object* v_result_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_691_, v_result_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object* v_hyp_701_, lean_object* v_result_702_){
_start:
{
lean_object* v_name_704_; lean_object* v_type_705_; lean_object* v_value_706_; lean_object* v_source_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_716_; 
v_name_704_ = lean_ctor_get(v_hyp_701_, 0);
v_type_705_ = lean_ctor_get(v_hyp_701_, 1);
v_value_706_ = lean_ctor_get(v_hyp_701_, 2);
v_source_707_ = lean_ctor_get(v_hyp_701_, 3);
v_isSharedCheck_716_ = !lean_is_exclusive(v_hyp_701_);
if (v_isSharedCheck_716_ == 0)
{
v___x_709_ = v_hyp_701_;
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_source_707_);
lean_inc(v_value_706_);
lean_inc(v_type_705_);
lean_inc(v_name_704_);
lean_dec(v_hyp_701_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_type_705_, v_result_702_);
lean_dec_ref(v_type_705_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 1, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_name_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_value_706_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_source_707_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object* v_hyp_717_, lean_object* v_result_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_717_, v_result_718_);
lean_dec_ref(v_result_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object* v_hyp_721_, lean_object* v_result_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_721_, v_result_722_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object* v_hyp_731_, lean_object* v_result_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_731_, v_result_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_result_732_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_741_){
_start:
{
lean_object* v_config_743_; lean_object* v___x_744_; 
v_config_743_ = lean_ctor_get(v_a_741_, 0);
lean_inc_ref(v_config_743_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_config_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_745_);
lean_dec_ref(v_a_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_config_760_; lean_object* v___x_761_; 
v_config_760_ = lean_ctor_get(v_a_748_, 0);
lean_inc_ref(v_config_760_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v_config_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(lean_object* v_a_775_){
_start:
{
lean_object* v_mode_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_mode_777_ = lean_ctor_get(v_a_775_, 1);
v___x_778_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_777_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg___boxed(lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(v_a_780_);
lean_dec_ref(v_a_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_mode_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_mode_795_ = lean_ctor_get(v_a_783_, 1);
v___x_796_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___boxed(lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(lean_object* v_a_811_){
_start:
{
lean_object* v_mode_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_mode_813_ = lean_ctor_get(v_a_811_, 1);
v___x_814_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_813_);
v___x_815_ = lean_box(v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg___boxed(lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(v_a_817_);
lean_dec_ref(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_mode_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_mode_832_ = lean_ctor_get(v_a_820_, 1);
v___x_833_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_832_);
v___x_834_ = lean_box(v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___boxed(lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_target_852_; lean_object* v___x_853_; 
v___x_851_ = lean_st_ref_get(v_a_849_);
v_target_852_ = lean_ctor_get(v___x_851_, 2);
lean_inc_ref(v_target_852_);
lean_dec(v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_target_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg___boxed(lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(v_a_854_);
lean_dec(v_a_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_869_; lean_object* v_target_870_; lean_object* v___x_871_; 
v___x_869_ = lean_st_ref_get(v_a_858_);
v_target_870_ = lean_ctor_get(v___x_869_, 2);
lean_inc_ref(v_target_870_);
lean_dec(v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_target_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___boxed(lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; lean_object* v_target_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = lean_st_ref_get(v_a_885_);
v_target_888_ = lean_ctor_get(v___x_887_, 2);
lean_inc_ref(v_target_888_);
lean_dec(v___x_887_);
v___x_889_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_888_);
lean_dec_ref(v_target_888_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg___boxed(lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(v_a_891_);
lean_dec(v_a_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; lean_object* v_target_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_906_ = lean_st_ref_get(v_a_895_);
v_target_907_ = lean_ctor_get(v___x_906_, 2);
lean_inc_ref(v_target_907_);
lean_dec(v___x_906_);
v___x_908_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_907_);
lean_dec_ref(v_target_907_);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed(lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(lean_object* v_target_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_926_; lean_object* v_caches_927_; lean_object* v_typeAnalysis_928_; lean_object* v_hypotheses_929_; uint8_t v_didChange_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_940_; 
v___x_926_ = lean_st_ref_take(v_a_924_);
v_caches_927_ = lean_ctor_get(v___x_926_, 0);
v_typeAnalysis_928_ = lean_ctor_get(v___x_926_, 1);
v_hypotheses_929_ = lean_ctor_get(v___x_926_, 3);
v_didChange_930_ = lean_ctor_get_uint8(v___x_926_, sizeof(void*)*4);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_926_, 2);
lean_dec(v_unused_941_);
v___x_932_ = v___x_926_;
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_hypotheses_929_);
lean_inc(v_typeAnalysis_928_);
lean_inc(v_caches_927_);
lean_dec(v___x_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = lean_box(0);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 2, v_target_923_);
v___x_936_ = v___x_932_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_caches_927_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_typeAnalysis_928_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_target_923_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_hypotheses_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*4, v_didChange_930_);
v___x_936_ = v_reuseFailAlloc_939_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_st_ref_put(v_a_924_, v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_934_);
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg___boxed(lean_object* v_target_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(v_target_942_, v_a_943_);
lean_dec(v_a_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(lean_object* v_target_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_caches_960_; lean_object* v_typeAnalysis_961_; lean_object* v_hypotheses_962_; uint8_t v_didChange_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_973_; 
v___x_959_ = lean_st_ref_take(v_a_948_);
v_caches_960_ = lean_ctor_get(v___x_959_, 0);
v_typeAnalysis_961_ = lean_ctor_get(v___x_959_, 1);
v_hypotheses_962_ = lean_ctor_get(v___x_959_, 3);
v_didChange_963_ = lean_ctor_get_uint8(v___x_959_, sizeof(void*)*4);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_959_, 2);
lean_dec(v_unused_974_);
v___x_965_ = v___x_959_;
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_hypotheses_962_);
lean_inc(v_typeAnalysis_961_);
lean_inc(v_caches_960_);
lean_dec(v___x_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_box(0);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v_target_946_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_caches_960_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_typeAnalysis_961_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_target_946_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_hypotheses_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*4, v_didChange_963_);
v___x_969_ = v_reuseFailAlloc_972_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_st_ref_put(v_a_948_, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_967_);
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___boxed(lean_object* v_target_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(v_target_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0(void){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_instMonadControlReaderT___redArg();
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1(void){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_990_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2(void){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_instMonadEIO___redArg();
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2);
v___x_993_ = l_StateRefT_x27_instMonad___redArg(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(lean_object* v_x_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v_target_1011_; 
v___x_1010_ = lean_st_ref_get(v_a_999_);
v_target_1011_ = lean_ctor_get(v___x_1010_, 2);
lean_inc_ref(v_target_1011_);
lean_dec(v___x_1010_);
if (lean_obj_tag(v_target_1011_) == 1)
{
lean_object* v_goal_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1140_; 
v_goal_1012_ = lean_ctor_get(v_target_1011_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_target_1011_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1014_ = v_target_1011_;
v_isShared_1015_ = v_isSharedCheck_1140_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_goal_1012_);
lean_dec(v_target_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1140_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_toApplicative_1019_; lean_object* v_toFunctor_1020_; lean_object* v_toSeq_1021_; lean_object* v_toSeqLeft_1022_; lean_object* v_toSeqRight_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v_toApplicative_1052_; lean_object* v_toFunctor_1053_; lean_object* v_toSeq_1054_; lean_object* v_toSeqLeft_1055_; lean_object* v_toSeqRight_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_toApplicative_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1138_; 
v___x_1016_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_1017_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_1018_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_1019_ = lean_ctor_get(v___x_1018_, 0);
v_toFunctor_1020_ = lean_ctor_get(v_toApplicative_1019_, 0);
v_toSeq_1021_ = lean_ctor_get(v_toApplicative_1019_, 2);
v_toSeqLeft_1022_ = lean_ctor_get(v_toApplicative_1019_, 3);
v_toSeqRight_1023_ = lean_ctor_get(v_toApplicative_1019_, 4);
v___f_1024_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_1025_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_1020_, 2);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toFunctor_1020_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toFunctor_1020_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___f_1026_);
lean_ctor_set(v___x_1028_, 1, v___f_1027_);
lean_inc(v_toSeqRight_1023_);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toSeqRight_1023_);
lean_inc(v_toSeqLeft_1022_);
v___f_1030_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1030_, 0, v_toSeqLeft_1022_);
lean_inc(v_toSeq_1021_);
v___f_1031_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1031_, 0, v_toSeq_1021_);
v___x_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1028_);
lean_ctor_set(v___x_1032_, 1, v___f_1024_);
lean_ctor_set(v___x_1032_, 2, v___f_1031_);
lean_ctor_set(v___x_1032_, 3, v___f_1030_);
lean_ctor_set(v___x_1032_, 4, v___f_1029_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___f_1025_);
v___x_1034_ = l_StateRefT_x27_instMonad___redArg(v___x_1033_);
v___x_1035_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1035_, 0, lean_box(0));
lean_closure_set(v___x_1035_, 1, lean_box(0));
lean_closure_set(v___x_1035_, 2, v___x_1034_);
v___x_1036_ = l_instMonadControlTOfPure___redArg(v___x_1035_);
lean_inc_ref(v___x_1036_);
v___f_1037_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1037_, 0, v___x_1017_);
lean_closure_set(v___f_1037_, 1, v___x_1036_);
v___f_1038_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1038_, 0, v___x_1017_);
lean_closure_set(v___f_1038_, 1, v___x_1036_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___f_1037_);
lean_ctor_set(v___x_1039_, 1, v___f_1038_);
lean_inc_ref(v___x_1039_);
v___f_1040_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1040_, 0, v___x_1016_);
lean_closure_set(v___f_1040_, 1, v___x_1039_);
v___f_1041_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1041_, 0, v___x_1016_);
lean_closure_set(v___f_1041_, 1, v___x_1039_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___f_1040_);
lean_ctor_set(v___x_1042_, 1, v___f_1041_);
lean_inc_ref(v___x_1042_);
v___f_1043_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1043_, 0, v___x_1017_);
lean_closure_set(v___f_1043_, 1, v___x_1042_);
v___f_1044_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1044_, 0, v___x_1017_);
lean_closure_set(v___f_1044_, 1, v___x_1042_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___f_1043_);
lean_ctor_set(v___x_1045_, 1, v___f_1044_);
lean_inc_ref(v___x_1045_);
v___f_1046_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1046_, 0, v___x_1016_);
lean_closure_set(v___f_1046_, 1, v___x_1045_);
v___f_1047_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1047_, 0, v___x_1016_);
lean_closure_set(v___f_1047_, 1, v___x_1045_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___f_1046_);
lean_ctor_set(v___x_1048_, 1, v___f_1047_);
lean_inc_ref(v___x_1048_);
v___f_1049_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1049_, 0, v___x_1016_);
lean_closure_set(v___f_1049_, 1, v___x_1048_);
v___f_1050_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1050_, 0, v___x_1016_);
lean_closure_set(v___f_1050_, 1, v___x_1048_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___f_1049_);
lean_ctor_set(v___x_1051_, 1, v___f_1050_);
v_toApplicative_1052_ = lean_ctor_get(v___x_1018_, 0);
v_toFunctor_1053_ = lean_ctor_get(v_toApplicative_1052_, 0);
v_toSeq_1054_ = lean_ctor_get(v_toApplicative_1052_, 2);
v_toSeqLeft_1055_ = lean_ctor_get(v_toApplicative_1052_, 3);
v_toSeqRight_1056_ = lean_ctor_get(v_toApplicative_1052_, 4);
lean_inc_ref_n(v_toFunctor_1053_, 2);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toFunctor_1053_);
v___f_1058_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1058_, 0, v_toFunctor_1053_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___f_1057_);
lean_ctor_set(v___x_1059_, 1, v___f_1058_);
lean_inc(v_toSeqRight_1056_);
v___f_1060_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1060_, 0, v_toSeqRight_1056_);
lean_inc(v_toSeqLeft_1055_);
v___f_1061_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1061_, 0, v_toSeqLeft_1055_);
lean_inc(v_toSeq_1054_);
v___f_1062_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1062_, 0, v_toSeq_1054_);
v___x_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1059_);
lean_ctor_set(v___x_1063_, 1, v___f_1024_);
lean_ctor_set(v___x_1063_, 2, v___f_1062_);
lean_ctor_set(v___x_1063_, 3, v___f_1061_);
lean_ctor_set(v___x_1063_, 4, v___f_1060_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___f_1025_);
v___x_1065_ = l_StateRefT_x27_instMonad___redArg(v___x_1064_);
v_toApplicative_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1065_, 1);
lean_dec(v_unused_1139_);
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1138_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_toApplicative_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1138_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v_toFunctor_1070_; lean_object* v_toSeq_1071_; lean_object* v_toSeqLeft_1072_; lean_object* v_toSeqRight_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1136_; 
v_toFunctor_1070_ = lean_ctor_get(v_toApplicative_1066_, 0);
v_toSeq_1071_ = lean_ctor_get(v_toApplicative_1066_, 2);
v_toSeqLeft_1072_ = lean_ctor_get(v_toApplicative_1066_, 3);
v_toSeqRight_1073_ = lean_ctor_get(v_toApplicative_1066_, 4);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_toApplicative_1066_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_toApplicative_1066_, 1);
lean_dec(v_unused_1137_);
v___x_1075_ = v_toApplicative_1066_;
v_isShared_1076_ = v_isSharedCheck_1136_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_toSeqRight_1073_);
lean_inc(v_toSeqLeft_1072_);
lean_inc(v_toSeq_1071_);
lean_inc(v_toFunctor_1070_);
lean_dec(v_toApplicative_1066_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1136_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___f_1077_; lean_object* v___f_1078_; lean_object* v___f_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___x_1086_; 
v___f_1077_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1078_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1070_);
v___f_1079_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1079_, 0, v_toFunctor_1070_);
v___f_1080_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1080_, 0, v_toFunctor_1070_);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___f_1079_);
lean_ctor_set(v___x_1081_, 1, v___f_1080_);
v___f_1082_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1082_, 0, v_toSeqRight_1073_);
v___f_1083_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1083_, 0, v_toSeqLeft_1072_);
v___f_1084_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1084_, 0, v_toSeq_1071_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 4, v___f_1082_);
lean_ctor_set(v___x_1075_, 3, v___f_1083_);
lean_ctor_set(v___x_1075_, 2, v___f_1084_);
lean_ctor_set(v___x_1075_, 1, v___f_1077_);
lean_ctor_set(v___x_1075_, 0, v___x_1081_);
v___x_1086_ = v___x_1075_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___f_1077_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v___f_1084_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v___f_1083_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v___f_1082_);
v___x_1086_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v___f_1078_);
lean_ctor_set(v___x_1068_, 0, v___x_1086_);
v___x_1088_ = v___x_1068_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___f_1078_);
v___x_1088_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_mvarId_1094_; lean_object* v___x_1095_; lean_object* v___x_5100__overap_1096_; lean_object* v___x_1097_; 
v___x_1089_ = l_StateRefT_x27_instMonad___redArg(v___x_1088_);
v___x_1090_ = l_ReaderT_instMonad___redArg(v___x_1089_);
v___x_1091_ = l_StateRefT_x27_instMonad___redArg(v___x_1090_);
v___x_1092_ = l_ReaderT_instMonad___redArg(v___x_1091_);
v___x_1093_ = l_ReaderT_instMonad___redArg(v___x_1092_);
v_mvarId_1094_ = lean_ctor_get(v_goal_1012_, 1);
lean_inc(v_mvarId_1094_);
v___x_1095_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1095_, 0, lean_box(0));
lean_closure_set(v___x_1095_, 1, v_goal_1012_);
lean_closure_set(v___x_1095_, 2, v_x_998_);
v___x_5100__overap_1096_ = l_Lean_MVarId_withContext___redArg(v___x_1051_, v___x_1093_, v_mvarId_1094_, v___x_1095_);
lean_inc(v_a_1008_);
lean_inc_ref(v_a_1007_);
lean_inc(v_a_1006_);
lean_inc_ref(v_a_1005_);
lean_inc(v_a_1004_);
lean_inc_ref(v_a_1003_);
lean_inc(v_a_1002_);
lean_inc_ref(v_a_1001_);
lean_inc(v_a_1000_);
v___x_1097_ = lean_apply_10(v___x_5100__overap_1096_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, lean_box(0));
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1125_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1125_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1125_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_fst_1102_; lean_object* v_snd_1103_; lean_object* v___x_1105_; 
v_fst_1102_ = lean_ctor_get(v_a_1098_, 0);
lean_inc(v_fst_1102_);
v_snd_1103_ = lean_ctor_get(v_a_1098_, 1);
lean_inc(v_snd_1103_);
lean_dec(v_a_1098_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v_snd_1103_);
v___x_1105_ = v___x_1014_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_snd_1103_);
v___x_1105_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v_caches_1107_; lean_object* v_typeAnalysis_1108_; lean_object* v_hypotheses_1109_; uint8_t v_didChange_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1122_; 
v___x_1106_ = lean_st_ref_take(v_a_999_);
v_caches_1107_ = lean_ctor_get(v___x_1106_, 0);
v_typeAnalysis_1108_ = lean_ctor_get(v___x_1106_, 1);
v_hypotheses_1109_ = lean_ctor_get(v___x_1106_, 3);
v_didChange_1110_ = lean_ctor_get_uint8(v___x_1106_, sizeof(void*)*4);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v___x_1106_, 2);
lean_dec(v_unused_1123_);
v___x_1112_ = v___x_1106_;
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_hypotheses_1109_);
lean_inc(v_typeAnalysis_1108_);
lean_inc(v_caches_1107_);
lean_dec(v___x_1106_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 2, v___x_1105_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_caches_1107_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_typeAnalysis_1108_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_hypotheses_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*4, v_didChange_1110_);
v___x_1115_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = lean_st_ref_put(v_a_999_, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_fst_1102_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1117_);
v___x_1119_ = v___x_1100_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
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
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_del_object(v___x_1014_);
v_a_1126_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1097_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1097_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
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
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v_target_1011_);
lean_dec_ref(v_x_998_);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___boxed(lean_object* v_x_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(v_x_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec(v_a_1144_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(lean_object* v_00_u03b1_1156_, lean_object* v_x_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v_target_1171_; 
v___x_1170_ = lean_st_ref_get(v_a_1159_);
v_target_1171_ = lean_ctor_get(v___x_1170_, 2);
lean_inc_ref(v_target_1171_);
lean_dec(v___x_1170_);
if (lean_obj_tag(v_target_1171_) == 1)
{
lean_object* v_goal_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1300_; 
v_goal_1172_ = lean_ctor_get(v_target_1171_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_target_1171_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1174_ = v_target_1171_;
v_isShared_1175_ = v_isSharedCheck_1300_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_goal_1172_);
lean_dec(v_target_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1300_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_toApplicative_1179_; lean_object* v_toFunctor_1180_; lean_object* v_toSeq_1181_; lean_object* v_toSeqLeft_1182_; lean_object* v_toSeqRight_1183_; lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v_toApplicative_1212_; lean_object* v_toFunctor_1213_; lean_object* v_toSeq_1214_; lean_object* v_toSeqLeft_1215_; lean_object* v_toSeqRight_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_toApplicative_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1298_; 
v___x_1176_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_1177_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_1178_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_1179_ = lean_ctor_get(v___x_1178_, 0);
v_toFunctor_1180_ = lean_ctor_get(v_toApplicative_1179_, 0);
v_toSeq_1181_ = lean_ctor_get(v_toApplicative_1179_, 2);
v_toSeqLeft_1182_ = lean_ctor_get(v_toApplicative_1179_, 3);
v_toSeqRight_1183_ = lean_ctor_get(v_toApplicative_1179_, 4);
v___f_1184_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_1185_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_1180_, 2);
v___f_1186_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1186_, 0, v_toFunctor_1180_);
v___f_1187_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1187_, 0, v_toFunctor_1180_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___f_1186_);
lean_ctor_set(v___x_1188_, 1, v___f_1187_);
lean_inc(v_toSeqRight_1183_);
v___f_1189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1189_, 0, v_toSeqRight_1183_);
lean_inc(v_toSeqLeft_1182_);
v___f_1190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1190_, 0, v_toSeqLeft_1182_);
lean_inc(v_toSeq_1181_);
v___f_1191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1191_, 0, v_toSeq_1181_);
v___x_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1188_);
lean_ctor_set(v___x_1192_, 1, v___f_1184_);
lean_ctor_set(v___x_1192_, 2, v___f_1191_);
lean_ctor_set(v___x_1192_, 3, v___f_1190_);
lean_ctor_set(v___x_1192_, 4, v___f_1189_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___f_1185_);
v___x_1194_ = l_StateRefT_x27_instMonad___redArg(v___x_1193_);
v___x_1195_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1195_, 0, lean_box(0));
lean_closure_set(v___x_1195_, 1, lean_box(0));
lean_closure_set(v___x_1195_, 2, v___x_1194_);
v___x_1196_ = l_instMonadControlTOfPure___redArg(v___x_1195_);
lean_inc_ref(v___x_1196_);
v___f_1197_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1197_, 0, v___x_1177_);
lean_closure_set(v___f_1197_, 1, v___x_1196_);
v___f_1198_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1198_, 0, v___x_1177_);
lean_closure_set(v___f_1198_, 1, v___x_1196_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___f_1197_);
lean_ctor_set(v___x_1199_, 1, v___f_1198_);
lean_inc_ref(v___x_1199_);
v___f_1200_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1200_, 0, v___x_1176_);
lean_closure_set(v___f_1200_, 1, v___x_1199_);
v___f_1201_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1201_, 0, v___x_1176_);
lean_closure_set(v___f_1201_, 1, v___x_1199_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___f_1200_);
lean_ctor_set(v___x_1202_, 1, v___f_1201_);
lean_inc_ref(v___x_1202_);
v___f_1203_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1203_, 0, v___x_1177_);
lean_closure_set(v___f_1203_, 1, v___x_1202_);
v___f_1204_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1204_, 0, v___x_1177_);
lean_closure_set(v___f_1204_, 1, v___x_1202_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___f_1203_);
lean_ctor_set(v___x_1205_, 1, v___f_1204_);
lean_inc_ref(v___x_1205_);
v___f_1206_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1206_, 0, v___x_1176_);
lean_closure_set(v___f_1206_, 1, v___x_1205_);
v___f_1207_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1207_, 0, v___x_1176_);
lean_closure_set(v___f_1207_, 1, v___x_1205_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___f_1206_);
lean_ctor_set(v___x_1208_, 1, v___f_1207_);
lean_inc_ref(v___x_1208_);
v___f_1209_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1209_, 0, v___x_1176_);
lean_closure_set(v___f_1209_, 1, v___x_1208_);
v___f_1210_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1210_, 0, v___x_1176_);
lean_closure_set(v___f_1210_, 1, v___x_1208_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___f_1209_);
lean_ctor_set(v___x_1211_, 1, v___f_1210_);
v_toApplicative_1212_ = lean_ctor_get(v___x_1178_, 0);
v_toFunctor_1213_ = lean_ctor_get(v_toApplicative_1212_, 0);
v_toSeq_1214_ = lean_ctor_get(v_toApplicative_1212_, 2);
v_toSeqLeft_1215_ = lean_ctor_get(v_toApplicative_1212_, 3);
v_toSeqRight_1216_ = lean_ctor_get(v_toApplicative_1212_, 4);
lean_inc_ref_n(v_toFunctor_1213_, 2);
v___f_1217_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1217_, 0, v_toFunctor_1213_);
v___f_1218_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1218_, 0, v_toFunctor_1213_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___f_1217_);
lean_ctor_set(v___x_1219_, 1, v___f_1218_);
lean_inc(v_toSeqRight_1216_);
v___f_1220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1220_, 0, v_toSeqRight_1216_);
lean_inc(v_toSeqLeft_1215_);
v___f_1221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1221_, 0, v_toSeqLeft_1215_);
lean_inc(v_toSeq_1214_);
v___f_1222_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1222_, 0, v_toSeq_1214_);
v___x_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1219_);
lean_ctor_set(v___x_1223_, 1, v___f_1184_);
lean_ctor_set(v___x_1223_, 2, v___f_1222_);
lean_ctor_set(v___x_1223_, 3, v___f_1221_);
lean_ctor_set(v___x_1223_, 4, v___f_1220_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v___f_1185_);
v___x_1225_ = l_StateRefT_x27_instMonad___redArg(v___x_1224_);
v_toApplicative_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v___x_1225_, 1);
lean_dec(v_unused_1299_);
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1298_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_toApplicative_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1298_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_toFunctor_1230_; lean_object* v_toSeq_1231_; lean_object* v_toSeqLeft_1232_; lean_object* v_toSeqRight_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1296_; 
v_toFunctor_1230_ = lean_ctor_get(v_toApplicative_1226_, 0);
v_toSeq_1231_ = lean_ctor_get(v_toApplicative_1226_, 2);
v_toSeqLeft_1232_ = lean_ctor_get(v_toApplicative_1226_, 3);
v_toSeqRight_1233_ = lean_ctor_get(v_toApplicative_1226_, 4);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_toApplicative_1226_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v_toApplicative_1226_, 1);
lean_dec(v_unused_1297_);
v___x_1235_ = v_toApplicative_1226_;
v_isShared_1236_ = v_isSharedCheck_1296_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_toSeqRight_1233_);
lean_inc(v_toSeqLeft_1232_);
lean_inc(v_toSeq_1231_);
lean_inc(v_toFunctor_1230_);
lean_dec(v_toApplicative_1226_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1296_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v___f_1244_; lean_object* v___x_1246_; 
v___f_1237_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1238_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1230_);
v___f_1239_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1239_, 0, v_toFunctor_1230_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toFunctor_1230_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___f_1239_);
lean_ctor_set(v___x_1241_, 1, v___f_1240_);
v___f_1242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1242_, 0, v_toSeqRight_1233_);
v___f_1243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1243_, 0, v_toSeqLeft_1232_);
v___f_1244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1244_, 0, v_toSeq_1231_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v___f_1242_);
lean_ctor_set(v___x_1235_, 3, v___f_1243_);
lean_ctor_set(v___x_1235_, 2, v___f_1244_);
lean_ctor_set(v___x_1235_, 1, v___f_1237_);
lean_ctor_set(v___x_1235_, 0, v___x_1241_);
v___x_1246_ = v___x_1235_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___f_1237_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v___f_1244_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v___f_1243_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v___f_1242_);
v___x_1246_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1248_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___f_1238_);
lean_ctor_set(v___x_1228_, 0, v___x_1246_);
v___x_1248_ = v___x_1228_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___f_1238_);
v___x_1248_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_mvarId_1254_; lean_object* v___x_1255_; lean_object* v___x_5171__overap_1256_; lean_object* v___x_1257_; 
v___x_1249_ = l_StateRefT_x27_instMonad___redArg(v___x_1248_);
v___x_1250_ = l_ReaderT_instMonad___redArg(v___x_1249_);
v___x_1251_ = l_StateRefT_x27_instMonad___redArg(v___x_1250_);
v___x_1252_ = l_ReaderT_instMonad___redArg(v___x_1251_);
v___x_1253_ = l_ReaderT_instMonad___redArg(v___x_1252_);
v_mvarId_1254_ = lean_ctor_get(v_goal_1172_, 1);
lean_inc(v_mvarId_1254_);
v___x_1255_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1255_, 0, lean_box(0));
lean_closure_set(v___x_1255_, 1, v_goal_1172_);
lean_closure_set(v___x_1255_, 2, v_x_1157_);
v___x_5171__overap_1256_ = l_Lean_MVarId_withContext___redArg(v___x_1211_, v___x_1253_, v_mvarId_1254_, v___x_1255_);
lean_inc(v_a_1168_);
lean_inc_ref(v_a_1167_);
lean_inc(v_a_1166_);
lean_inc_ref(v_a_1165_);
lean_inc(v_a_1164_);
lean_inc_ref(v_a_1163_);
lean_inc(v_a_1162_);
lean_inc_ref(v_a_1161_);
lean_inc(v_a_1160_);
v___x_1257_ = lean_apply_10(v___x_5171__overap_1256_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, lean_box(0));
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1285_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1285_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1285_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v___x_1265_; 
v_fst_1262_ = lean_ctor_get(v_a_1258_, 0);
lean_inc(v_fst_1262_);
v_snd_1263_ = lean_ctor_get(v_a_1258_, 1);
lean_inc(v_snd_1263_);
lean_dec(v_a_1258_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v_snd_1263_);
v___x_1265_ = v___x_1174_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_snd_1263_);
v___x_1265_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; lean_object* v_caches_1267_; lean_object* v_typeAnalysis_1268_; lean_object* v_hypotheses_1269_; uint8_t v_didChange_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1282_; 
v___x_1266_ = lean_st_ref_take(v_a_1159_);
v_caches_1267_ = lean_ctor_get(v___x_1266_, 0);
v_typeAnalysis_1268_ = lean_ctor_get(v___x_1266_, 1);
v_hypotheses_1269_ = lean_ctor_get(v___x_1266_, 3);
v_didChange_1270_ = lean_ctor_get_uint8(v___x_1266_, sizeof(void*)*4);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v___x_1266_, 2);
lean_dec(v_unused_1283_);
v___x_1272_ = v___x_1266_;
v_isShared_1273_ = v_isSharedCheck_1282_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_hypotheses_1269_);
lean_inc(v_typeAnalysis_1268_);
lean_inc(v_caches_1267_);
lean_dec(v___x_1266_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1282_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 2, v___x_1265_);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_caches_1267_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_typeAnalysis_1268_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_hypotheses_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1281_, sizeof(void*)*4, v_didChange_1270_);
v___x_1275_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1276_ = lean_st_ref_put(v_a_1159_, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_fst_1262_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1277_);
v___x_1279_ = v___x_1260_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_del_object(v___x_1174_);
v_a_1286_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1257_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1257_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
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
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec_ref(v_target_1171_);
lean_dec_ref(v_x_1157_);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_x_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(v_00_u03b1_1303_, v_x_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(lean_object* v_x_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
v___x_1329_ = lean_apply_10(v_x_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, lean_box(0));
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed(lean_object* v_x_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(v_x_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(lean_object* v_mvarId_1342_, lean_object* v_x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___f_1354_; lean_object* v___x_1355_; 
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1354_, 0, v_x_1343_);
lean_closure_set(v___f_1354_, 1, v___y_1344_);
lean_closure_set(v___f_1354_, 2, v___y_1345_);
lean_closure_set(v___f_1354_, 3, v___y_1346_);
lean_closure_set(v___f_1354_, 4, v___y_1347_);
lean_closure_set(v___f_1354_, 5, v___y_1348_);
v___x_1355_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1342_, v___f_1354_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1355_) == 0)
{
return v___x_1355_;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___boxed(lean_object* v_mvarId_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1364_, v_x_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(lean_object* v_00_u03b1_1377_, lean_object* v_mvarId_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1378_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_mvarId_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(v_00_u03b1_1391_, v_mvarId_1392_, v_x_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(lean_object* v_goal_1405_, lean_object* v_falseProof_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_st_mk_ref(v_goal_1405_);
v___x_1418_ = l_Lean_Meta_Grind_closeGoal(v_falseProof_1406_, v___x_1417_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1428_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = lean_st_ref_get(v___x_1417_);
lean_dec(v___x_1417_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_a_1419_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1424_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v___x_1417_);
v_a_1429_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1418_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1418_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed(lean_object* v_goal_1437_, lean_object* v_falseProof_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(v_goal_1437_, v_falseProof_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object* v_falseProof_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; lean_object* v_target_1463_; 
v___x_1462_ = lean_st_ref_get(v_a_1451_);
v_target_1463_ = lean_ctor_get(v___x_1462_, 2);
lean_inc_ref(v_target_1463_);
lean_dec(v___x_1462_);
if (lean_obj_tag(v_target_1463_) == 0)
{
lean_object* v_mvar_1464_; lean_object* v___x_1465_; 
v_mvar_1464_ = lean_ctor_get(v_target_1463_, 0);
lean_inc(v_mvar_1464_);
lean_dec_ref_known(v_target_1463_, 1);
v___x_1465_ = l_Lean_MVarId_assignFalseProof(v_mvar_1464_, v_falseProof_1450_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
return v___x_1465_;
}
else
{
lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1517_; 
v_isSharedCheck_1517_ = !lean_is_exclusive(v_target_1463_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_target_1463_, 0);
lean_dec(v_unused_1518_);
v___x_1467_ = v_target_1463_;
v_isShared_1468_ = v_isSharedCheck_1517_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v_target_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1517_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_target_1471_; 
v___x_1469_ = lean_box(0);
v___x_1470_ = lean_st_ref_get(v_a_1451_);
v_target_1471_ = lean_ctor_get(v___x_1470_, 2);
lean_inc_ref(v_target_1471_);
lean_dec(v___x_1470_);
if (lean_obj_tag(v_target_1471_) == 1)
{
lean_object* v_goal_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1513_; 
lean_del_object(v___x_1467_);
v_goal_1472_ = lean_ctor_get(v_target_1471_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_target_1471_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1474_ = v_target_1471_;
v_isShared_1475_ = v_isSharedCheck_1513_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_goal_1472_);
lean_dec(v_target_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1513_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_mvarId_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; 
v_mvarId_1476_ = lean_ctor_get(v_goal_1472_, 1);
lean_inc(v_mvarId_1476_);
v___f_1477_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1477_, 0, v_goal_1472_);
lean_closure_set(v___f_1477_, 1, v_falseProof_1450_);
v___x_1478_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1476_, v___f_1477_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1504_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1504_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1504_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_snd_1483_; lean_object* v___x_1485_; 
v_snd_1483_ = lean_ctor_get(v_a_1479_, 1);
lean_inc(v_snd_1483_);
lean_dec(v_a_1479_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v_snd_1483_);
v___x_1485_ = v___x_1474_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_snd_1483_);
v___x_1485_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v_caches_1487_; lean_object* v_typeAnalysis_1488_; lean_object* v_hypotheses_1489_; uint8_t v_didChange_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1501_; 
v___x_1486_ = lean_st_ref_take(v_a_1451_);
v_caches_1487_ = lean_ctor_get(v___x_1486_, 0);
v_typeAnalysis_1488_ = lean_ctor_get(v___x_1486_, 1);
v_hypotheses_1489_ = lean_ctor_get(v___x_1486_, 3);
v_didChange_1490_ = lean_ctor_get_uint8(v___x_1486_, sizeof(void*)*4);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v___x_1486_, 2);
lean_dec(v_unused_1502_);
v___x_1492_ = v___x_1486_;
v_isShared_1493_ = v_isSharedCheck_1501_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_hypotheses_1489_);
lean_inc(v_typeAnalysis_1488_);
lean_inc(v_caches_1487_);
lean_dec(v___x_1486_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1501_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 2, v___x_1485_);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_caches_1487_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_typeAnalysis_1488_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_hypotheses_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*4, v_didChange_1490_);
v___x_1495_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_st_ref_put(v_a_1451_, v___x_1495_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1469_);
v___x_1498_ = v___x_1481_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1469_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_del_object(v___x_1474_);
v_a_1505_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1478_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1478_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
lean_object* v___x_1515_; 
lean_dec_ref(v_target_1471_);
lean_dec_ref(v_falseProof_1450_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1469_);
v___x_1515_ = v___x_1467_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1469_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___boxed(lean_object* v_falseProof_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec(v_a_1520_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(lean_object* v_falseProof_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1532_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed(lean_object* v_falseProof_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(v_falseProof_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object* v_a_1560_){
_start:
{
lean_object* v___x_1562_; uint8_t v_didChange_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_st_ref_get(v_a_1560_);
v_didChange_1563_ = lean_ctor_get_uint8(v___x_1562_, sizeof(void*)*4);
lean_dec(v___x_1562_);
v___x_1564_ = lean_box(v_didChange_1563_);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_1566_);
lean_dec(v_a_1566_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; uint8_t v_didChange_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1581_ = lean_st_ref_get(v_a_1570_);
v_didChange_1582_ = lean_ctor_get_uint8(v___x_1581_, sizeof(void*)*4);
lean_dec(v___x_1581_);
v___x_1583_ = lean_box(v_didChange_1582_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v_caches_1601_; lean_object* v_typeAnalysis_1602_; lean_object* v_target_1603_; lean_object* v_hypotheses_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1615_; 
v___x_1600_ = lean_st_ref_take(v_a_1598_);
v_caches_1601_ = lean_ctor_get(v___x_1600_, 0);
v_typeAnalysis_1602_ = lean_ctor_get(v___x_1600_, 1);
v_target_1603_ = lean_ctor_get(v___x_1600_, 2);
v_hypotheses_1604_ = lean_ctor_get(v___x_1600_, 3);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1606_ = v___x_1600_;
v_isShared_1607_ = v_isSharedCheck_1615_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_hypotheses_1604_);
lean_inc(v_target_1603_);
lean_inc(v_typeAnalysis_1602_);
lean_inc(v_caches_1601_);
lean_dec(v___x_1600_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1615_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1611_; 
v___x_1608_ = lean_box(0);
v___x_1609_ = 0;
if (v_isShared_1607_ == 0)
{
v___x_1611_ = v___x_1606_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_caches_1601_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_typeAnalysis_1602_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_target_1603_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_hypotheses_1604_);
v___x_1611_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*4, v___x_1609_);
v___x_1612_ = lean_st_ref_put(v_a_1598_, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1608_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_1616_);
lean_dec(v_a_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v_caches_1632_; lean_object* v_typeAnalysis_1633_; lean_object* v_target_1634_; lean_object* v_hypotheses_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1646_; 
v___x_1631_ = lean_st_ref_take(v_a_1620_);
v_caches_1632_ = lean_ctor_get(v___x_1631_, 0);
v_typeAnalysis_1633_ = lean_ctor_get(v___x_1631_, 1);
v_target_1634_ = lean_ctor_get(v___x_1631_, 2);
v_hypotheses_1635_ = lean_ctor_get(v___x_1631_, 3);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1637_ = v___x_1631_;
v_isShared_1638_ = v_isSharedCheck_1646_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_hypotheses_1635_);
lean_inc(v_target_1634_);
lean_inc(v_typeAnalysis_1633_);
lean_inc(v_caches_1632_);
lean_dec(v___x_1631_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1646_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; uint8_t v___x_1640_; lean_object* v___x_1642_; 
v___x_1639_ = lean_box(0);
v___x_1640_ = 0;
if (v_isShared_1638_ == 0)
{
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_caches_1632_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_typeAnalysis_1633_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_target_1634_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_hypotheses_1635_);
v___x_1642_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*4, v___x_1640_);
v___x_1643_ = lean_st_ref_put(v_a_1620_, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1639_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; lean_object* v_caches_1663_; lean_object* v_typeAnalysis_1664_; lean_object* v_target_1665_; lean_object* v_hypotheses_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1677_; 
v___x_1662_ = lean_st_ref_take(v_a_1660_);
v_caches_1663_ = lean_ctor_get(v___x_1662_, 0);
v_typeAnalysis_1664_ = lean_ctor_get(v___x_1662_, 1);
v_target_1665_ = lean_ctor_get(v___x_1662_, 2);
v_hypotheses_1666_ = lean_ctor_get(v___x_1662_, 3);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1668_ = v___x_1662_;
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_hypotheses_1666_);
lean_inc(v_target_1665_);
lean_inc(v_typeAnalysis_1664_);
lean_inc(v_caches_1663_);
lean_dec(v___x_1662_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1673_; 
v___x_1670_ = lean_box(0);
v___x_1671_ = 1;
if (v_isShared_1669_ == 0)
{
v___x_1673_ = v___x_1668_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_caches_1663_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_typeAnalysis_1664_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_target_1665_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_hypotheses_1666_);
v___x_1673_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*4, v___x_1671_);
v___x_1674_ = lean_st_ref_put(v_a_1660_, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1670_);
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_1678_);
lean_dec(v_a_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v___x_1693_; lean_object* v_caches_1694_; lean_object* v_typeAnalysis_1695_; lean_object* v_target_1696_; lean_object* v_hypotheses_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1708_; 
v___x_1693_ = lean_st_ref_take(v_a_1682_);
v_caches_1694_ = lean_ctor_get(v___x_1693_, 0);
v_typeAnalysis_1695_ = lean_ctor_get(v___x_1693_, 1);
v_target_1696_ = lean_ctor_get(v___x_1693_, 2);
v_hypotheses_1697_ = lean_ctor_get(v___x_1693_, 3);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1699_ = v___x_1693_;
v_isShared_1700_ = v_isSharedCheck_1708_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_hypotheses_1697_);
lean_inc(v_target_1696_);
lean_inc(v_typeAnalysis_1695_);
lean_inc(v_caches_1694_);
lean_dec(v___x_1693_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1708_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1704_; 
v___x_1701_ = lean_box(0);
v___x_1702_ = 1;
if (v_isShared_1700_ == 0)
{
v___x_1704_ = v___x_1699_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_caches_1694_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_typeAnalysis_1695_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_target_1696_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_hypotheses_1697_);
v___x_1704_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*4, v___x_1702_);
v___x_1705_ = lean_st_ref_put(v_a_1682_, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1701_);
return v___x_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1724_; lean_object* v_caches_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_st_ref_get(v_a_1722_);
v_caches_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc_ref(v_caches_1725_);
lean_dec(v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_caches_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg___boxed(lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(v_a_1727_);
lean_dec(v_a_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v_caches_1743_; lean_object* v___x_1744_; 
v___x_1742_ = lean_st_ref_get(v_a_1731_);
v_caches_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc_ref(v_caches_1743_);
lean_dec(v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_caches_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___boxed(lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(lean_object* v_caches_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1761_; lean_object* v_typeAnalysis_1762_; lean_object* v_target_1763_; lean_object* v_hypotheses_1764_; uint8_t v_didChange_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1775_; 
v___x_1761_ = lean_st_ref_take(v_a_1759_);
v_typeAnalysis_1762_ = lean_ctor_get(v___x_1761_, 1);
v_target_1763_ = lean_ctor_get(v___x_1761_, 2);
v_hypotheses_1764_ = lean_ctor_get(v___x_1761_, 3);
v_didChange_1765_ = lean_ctor_get_uint8(v___x_1761_, sizeof(void*)*4);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v___x_1761_, 0);
lean_dec(v_unused_1776_);
v___x_1767_ = v___x_1761_;
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_hypotheses_1764_);
lean_inc(v_target_1763_);
lean_inc(v_typeAnalysis_1762_);
lean_dec(v___x_1761_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_box(0);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v_caches_1758_);
v___x_1771_ = v___x_1767_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_caches_1758_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_typeAnalysis_1762_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_target_1763_);
lean_ctor_set(v_reuseFailAlloc_1774_, 3, v_hypotheses_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1774_, sizeof(void*)*4, v_didChange_1765_);
v___x_1771_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_st_ref_put(v_a_1759_, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1769_);
return v___x_1773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg___boxed(lean_object* v_caches_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(v_caches_1777_, v_a_1778_);
lean_dec(v_a_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(lean_object* v_caches_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; lean_object* v_typeAnalysis_1795_; lean_object* v_target_1796_; lean_object* v_hypotheses_1797_; uint8_t v_didChange_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1808_; 
v___x_1794_ = lean_st_ref_take(v_a_1783_);
v_typeAnalysis_1795_ = lean_ctor_get(v___x_1794_, 1);
v_target_1796_ = lean_ctor_get(v___x_1794_, 2);
v_hypotheses_1797_ = lean_ctor_get(v___x_1794_, 3);
v_didChange_1798_ = lean_ctor_get_uint8(v___x_1794_, sizeof(void*)*4);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1794_, 0);
lean_dec(v_unused_1809_);
v___x_1800_ = v___x_1794_;
v_isShared_1801_ = v_isSharedCheck_1808_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_hypotheses_1797_);
lean_inc(v_target_1796_);
lean_inc(v_typeAnalysis_1795_);
lean_dec(v___x_1794_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1808_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v_caches_1781_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_caches_1781_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_typeAnalysis_1795_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_target_1796_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_hypotheses_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1807_, sizeof(void*)*4, v_didChange_1798_);
v___x_1804_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_st_ref_put(v_a_1783_, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1802_);
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___boxed(lean_object* v_caches_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(v_caches_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1823_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1824_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_1828_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
lean_ctor_set(v___x_1828_, 2, v___x_1827_);
lean_ctor_set(v___x_1828_, 3, v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
uint8_t v_keepCaches_1832_; 
v_keepCaches_1832_ = lean_ctor_get_uint8(v_a_1829_, sizeof(void*)*2);
if (v_keepCaches_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_typeAnalysis_1835_; lean_object* v_target_1836_; lean_object* v_hypotheses_1837_; uint8_t v_didChange_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1848_; 
v___x_1833_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_1834_ = lean_st_ref_take(v_a_1830_);
v_typeAnalysis_1835_ = lean_ctor_get(v___x_1834_, 1);
v_target_1836_ = lean_ctor_get(v___x_1834_, 2);
v_hypotheses_1837_ = lean_ctor_get(v___x_1834_, 3);
v_didChange_1838_ = lean_ctor_get_uint8(v___x_1834_, sizeof(void*)*4);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1834_, 0);
lean_dec(v_unused_1849_);
v___x_1840_ = v___x_1834_;
v_isShared_1841_ = v_isSharedCheck_1848_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_hypotheses_1837_);
lean_inc(v_target_1836_);
lean_inc(v_typeAnalysis_1835_);
lean_dec(v___x_1834_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1848_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_box(0);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1833_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_typeAnalysis_1835_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_target_1836_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_hypotheses_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1847_, sizeof(void*)*4, v_didChange_1838_);
v___x_1844_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_st_ref_put(v_a_1830_, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1842_);
return v___x_1846_;
}
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___boxed(lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1852_, v_a_1853_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1856_, v_a_1857_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___boxed(lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_1882_){
_start:
{
lean_object* v___x_1884_; lean_object* v_typeAnalysis_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_st_ref_get(v_a_1882_);
v_typeAnalysis_1885_ = lean_ctor_get(v___x_1884_, 1);
lean_inc_ref(v_typeAnalysis_1885_);
lean_dec(v___x_1884_);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v_typeAnalysis_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1887_);
lean_dec(v_a_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v___x_1902_; lean_object* v_typeAnalysis_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_st_ref_get(v_a_1891_);
v_typeAnalysis_1903_ = lean_ctor_get(v___x_1902_, 1);
lean_inc_ref(v_typeAnalysis_1903_);
lean_dec(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_typeAnalysis_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v_typeAnalysis_1929_; lean_object* v_interestingStructures_1930_; lean_object* v_uninteresting_1931_; uint8_t v___x_1932_; 
v___x_1926_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1928_ = lean_st_ref_get(v_a_1924_);
v_typeAnalysis_1929_ = lean_ctor_get(v___x_1928_, 1);
lean_inc_ref(v_typeAnalysis_1929_);
lean_dec(v___x_1928_);
v_interestingStructures_1930_ = lean_ctor_get(v_typeAnalysis_1929_, 0);
lean_inc_ref(v_interestingStructures_1930_);
v_uninteresting_1931_ = lean_ctor_get(v_typeAnalysis_1929_, 3);
lean_inc_ref(v_uninteresting_1931_);
lean_dec_ref(v_typeAnalysis_1929_);
lean_inc(v_n_1923_);
v___x_1932_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1926_, v___x_1927_, v_uninteresting_1931_, v_n_1923_);
lean_dec_ref(v_uninteresting_1931_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; 
v___x_1933_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1926_, v___x_1927_, v_interestingStructures_1930_, v_n_1923_);
lean_dec_ref(v_interestingStructures_1930_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_box(0);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = lean_box(v___x_1933_);
v___x_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
return v___x_1938_;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec_ref(v_interestingStructures_1930_);
lean_dec(v_n_1923_);
v___x_1939_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1941_, v_a_1942_);
lean_dec(v_a_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v_typeAnalysis_1961_; lean_object* v_interestingStructures_1962_; lean_object* v_uninteresting_1963_; uint8_t v___x_1964_; 
v___x_1958_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1959_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1960_ = lean_st_ref_get(v_a_1947_);
v_typeAnalysis_1961_ = lean_ctor_get(v___x_1960_, 1);
lean_inc_ref(v_typeAnalysis_1961_);
lean_dec(v___x_1960_);
v_interestingStructures_1962_ = lean_ctor_get(v_typeAnalysis_1961_, 0);
lean_inc_ref(v_interestingStructures_1962_);
v_uninteresting_1963_ = lean_ctor_get(v_typeAnalysis_1961_, 3);
lean_inc_ref(v_uninteresting_1963_);
lean_dec_ref(v_typeAnalysis_1961_);
lean_inc(v_n_1945_);
v___x_1964_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1958_, v___x_1959_, v_uninteresting_1963_, v_n_1945_);
lean_dec_ref(v_uninteresting_1963_);
if (v___x_1964_ == 0)
{
uint8_t v___x_1965_; 
v___x_1965_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1958_, v___x_1959_, v_interestingStructures_1962_, v_n_1945_);
lean_dec_ref(v_interestingStructures_1962_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = lean_box(v___x_1965_);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_dec_ref(v_interestingStructures_1962_);
lean_dec(v_n_1945_);
v___x_1971_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v_caches_1991_; lean_object* v_typeAnalysis_1992_; lean_object* v_target_1993_; lean_object* v_hypotheses_1994_; uint8_t v_didChange_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2006_; 
v___x_1990_ = lean_st_ref_take(v_a_1988_);
v_caches_1991_ = lean_ctor_get(v___x_1990_, 0);
v_typeAnalysis_1992_ = lean_ctor_get(v___x_1990_, 1);
v_target_1993_ = lean_ctor_get(v___x_1990_, 2);
v_hypotheses_1994_ = lean_ctor_get(v___x_1990_, 3);
v_didChange_1995_ = lean_ctor_get_uint8(v___x_1990_, sizeof(void*)*4);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1997_ = v___x_1990_;
v_isShared_1998_ = v_isSharedCheck_2006_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_hypotheses_1994_);
lean_inc(v_target_1993_);
lean_inc(v_typeAnalysis_1992_);
lean_inc(v_caches_1991_);
lean_dec(v___x_1990_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2006_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1999_ = lean_box(0);
v___x_2000_ = lean_apply_1(v_f_1987_, v_typeAnalysis_1992_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2000_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_caches_1991_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_target_1993_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_hypotheses_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*4, v_didChange_1995_);
v___x_2002_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_st_ref_put(v_a_1988_, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_1999_);
return v___x_2004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_2007_, v_a_2008_);
lean_dec(v_a_2008_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v_caches_2025_; lean_object* v_typeAnalysis_2026_; lean_object* v_target_2027_; lean_object* v_hypotheses_2028_; uint8_t v_didChange_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2040_; 
v___x_2024_ = lean_st_ref_take(v_a_2013_);
v_caches_2025_ = lean_ctor_get(v___x_2024_, 0);
v_typeAnalysis_2026_ = lean_ctor_get(v___x_2024_, 1);
v_target_2027_ = lean_ctor_get(v___x_2024_, 2);
v_hypotheses_2028_ = lean_ctor_get(v___x_2024_, 3);
v_didChange_2029_ = lean_ctor_get_uint8(v___x_2024_, sizeof(void*)*4);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2031_ = v___x_2024_;
v_isShared_2032_ = v_isSharedCheck_2040_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_hypotheses_2028_);
lean_inc(v_target_2027_);
lean_inc(v_typeAnalysis_2026_);
lean_inc(v_caches_2025_);
lean_dec(v___x_2024_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2040_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2033_ = lean_box(0);
v___x_2034_ = lean_apply_1(v_f_2011_, v_typeAnalysis_2026_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v___x_2034_);
v___x_2036_ = v___x_2031_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_caches_2025_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_target_2027_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v_hypotheses_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2039_, sizeof(void*)*4, v_didChange_2029_);
v___x_2036_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_st_ref_put(v_a_2013_, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2033_);
return v___x_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v_typeAnalysis_2061_; lean_object* v_caches_2062_; lean_object* v_target_2063_; lean_object* v_hypotheses_2064_; uint8_t v_didChange_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2087_; 
v___x_2058_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2059_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2060_ = lean_st_ref_take(v_a_2056_);
v_typeAnalysis_2061_ = lean_ctor_get(v___x_2060_, 1);
v_caches_2062_ = lean_ctor_get(v___x_2060_, 0);
v_target_2063_ = lean_ctor_get(v___x_2060_, 2);
v_hypotheses_2064_ = lean_ctor_get(v___x_2060_, 3);
v_didChange_2065_ = lean_ctor_get_uint8(v___x_2060_, sizeof(void*)*4);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2067_ = v___x_2060_;
v_isShared_2068_ = v_isSharedCheck_2087_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_hypotheses_2064_);
lean_inc(v_target_2063_);
lean_inc(v_typeAnalysis_2061_);
lean_inc(v_caches_2062_);
lean_dec(v___x_2060_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2087_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_interestingStructures_2069_; lean_object* v_interestingEnums_2070_; lean_object* v_interestingMatchers_2071_; lean_object* v_uninteresting_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2086_; 
v_interestingStructures_2069_ = lean_ctor_get(v_typeAnalysis_2061_, 0);
v_interestingEnums_2070_ = lean_ctor_get(v_typeAnalysis_2061_, 1);
v_interestingMatchers_2071_ = lean_ctor_get(v_typeAnalysis_2061_, 2);
v_uninteresting_2072_ = lean_ctor_get(v_typeAnalysis_2061_, 3);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_typeAnalysis_2061_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2074_ = v_typeAnalysis_2061_;
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_uninteresting_2072_);
lean_inc(v_interestingMatchers_2071_);
lean_inc(v_interestingEnums_2070_);
lean_inc(v_interestingStructures_2069_);
lean_dec(v_typeAnalysis_2061_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2076_ = lean_box(0);
v___x_2077_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2058_, v___x_2059_, v_interestingStructures_2069_, v_n_2055_, v___x_2076_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2077_);
v___x_2079_ = v___x_2074_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_interestingEnums_2070_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_interestingMatchers_2071_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_uninteresting_2072_);
v___x_2079_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2079_);
v___x_2081_ = v___x_2067_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_caches_2062_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_target_2063_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_hypotheses_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*4, v_didChange_2065_);
v___x_2081_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_st_ref_put(v_a_2056_, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2076_);
return v___x_2083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_2088_, v_a_2089_);
lean_dec(v_a_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v_typeAnalysis_2108_; lean_object* v_caches_2109_; lean_object* v_target_2110_; lean_object* v_hypotheses_2111_; uint8_t v_didChange_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2134_; 
v___x_2105_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2106_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2107_ = lean_st_ref_take(v_a_2094_);
v_typeAnalysis_2108_ = lean_ctor_get(v___x_2107_, 1);
v_caches_2109_ = lean_ctor_get(v___x_2107_, 0);
v_target_2110_ = lean_ctor_get(v___x_2107_, 2);
v_hypotheses_2111_ = lean_ctor_get(v___x_2107_, 3);
v_didChange_2112_ = lean_ctor_get_uint8(v___x_2107_, sizeof(void*)*4);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2114_ = v___x_2107_;
v_isShared_2115_ = v_isSharedCheck_2134_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_hypotheses_2111_);
lean_inc(v_target_2110_);
lean_inc(v_typeAnalysis_2108_);
lean_inc(v_caches_2109_);
lean_dec(v___x_2107_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2134_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_interestingStructures_2116_; lean_object* v_interestingEnums_2117_; lean_object* v_interestingMatchers_2118_; lean_object* v_uninteresting_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2133_; 
v_interestingStructures_2116_ = lean_ctor_get(v_typeAnalysis_2108_, 0);
v_interestingEnums_2117_ = lean_ctor_get(v_typeAnalysis_2108_, 1);
v_interestingMatchers_2118_ = lean_ctor_get(v_typeAnalysis_2108_, 2);
v_uninteresting_2119_ = lean_ctor_get(v_typeAnalysis_2108_, 3);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_typeAnalysis_2108_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2121_ = v_typeAnalysis_2108_;
v_isShared_2122_ = v_isSharedCheck_2133_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_uninteresting_2119_);
lean_inc(v_interestingMatchers_2118_);
lean_inc(v_interestingEnums_2117_);
lean_inc(v_interestingStructures_2116_);
lean_dec(v_typeAnalysis_2108_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2133_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_box(0);
v___x_2124_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2105_, v___x_2106_, v_interestingStructures_2116_, v_n_2092_, v___x_2123_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_interestingEnums_2117_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_interestingMatchers_2118_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_uninteresting_2119_);
v___x_2126_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v___x_2126_);
v___x_2128_ = v___x_2114_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_caches_2109_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_target_2110_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_hypotheses_2111_);
lean_ctor_set_uint8(v_reuseFailAlloc_2131_, sizeof(void*)*4, v_didChange_2112_);
v___x_2128_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_st_ref_put(v_a_2094_, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2123_);
return v___x_2130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_typeAnalysis_2155_; lean_object* v_caches_2156_; lean_object* v_target_2157_; lean_object* v_hypotheses_2158_; uint8_t v_didChange_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2181_; 
v___x_2152_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2153_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2154_ = lean_st_ref_take(v_a_2150_);
v_typeAnalysis_2155_ = lean_ctor_get(v___x_2154_, 1);
v_caches_2156_ = lean_ctor_get(v___x_2154_, 0);
v_target_2157_ = lean_ctor_get(v___x_2154_, 2);
v_hypotheses_2158_ = lean_ctor_get(v___x_2154_, 3);
v_didChange_2159_ = lean_ctor_get_uint8(v___x_2154_, sizeof(void*)*4);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2161_ = v___x_2154_;
v_isShared_2162_ = v_isSharedCheck_2181_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_hypotheses_2158_);
lean_inc(v_target_2157_);
lean_inc(v_typeAnalysis_2155_);
lean_inc(v_caches_2156_);
lean_dec(v___x_2154_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2181_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_interestingStructures_2163_; lean_object* v_interestingEnums_2164_; lean_object* v_interestingMatchers_2165_; lean_object* v_uninteresting_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2180_; 
v_interestingStructures_2163_ = lean_ctor_get(v_typeAnalysis_2155_, 0);
v_interestingEnums_2164_ = lean_ctor_get(v_typeAnalysis_2155_, 1);
v_interestingMatchers_2165_ = lean_ctor_get(v_typeAnalysis_2155_, 2);
v_uninteresting_2166_ = lean_ctor_get(v_typeAnalysis_2155_, 3);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_typeAnalysis_2155_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2168_ = v_typeAnalysis_2155_;
v_isShared_2169_ = v_isSharedCheck_2180_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_uninteresting_2166_);
lean_inc(v_interestingMatchers_2165_);
lean_inc(v_interestingEnums_2164_);
lean_inc(v_interestingStructures_2163_);
lean_dec(v_typeAnalysis_2155_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2180_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = lean_box(0);
v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2152_, v___x_2153_, v_interestingEnums_2164_, v_n_2149_, v___x_2170_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v___x_2171_);
v___x_2173_ = v___x_2168_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_interestingStructures_2163_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_interestingMatchers_2165_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_uninteresting_2166_);
v___x_2173_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2173_);
v___x_2175_ = v___x_2161_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_caches_2156_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_target_2157_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_hypotheses_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*4, v_didChange_2159_);
v___x_2175_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_st_ref_put(v_a_2150_, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2170_);
return v___x_2177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_2182_, v_a_2183_);
lean_dec(v_a_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v_typeAnalysis_2202_; lean_object* v_caches_2203_; lean_object* v_target_2204_; lean_object* v_hypotheses_2205_; uint8_t v_didChange_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2228_; 
v___x_2199_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2200_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2201_ = lean_st_ref_take(v_a_2188_);
v_typeAnalysis_2202_ = lean_ctor_get(v___x_2201_, 1);
v_caches_2203_ = lean_ctor_get(v___x_2201_, 0);
v_target_2204_ = lean_ctor_get(v___x_2201_, 2);
v_hypotheses_2205_ = lean_ctor_get(v___x_2201_, 3);
v_didChange_2206_ = lean_ctor_get_uint8(v___x_2201_, sizeof(void*)*4);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2208_ = v___x_2201_;
v_isShared_2209_ = v_isSharedCheck_2228_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_hypotheses_2205_);
lean_inc(v_target_2204_);
lean_inc(v_typeAnalysis_2202_);
lean_inc(v_caches_2203_);
lean_dec(v___x_2201_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2228_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_interestingStructures_2210_; lean_object* v_interestingEnums_2211_; lean_object* v_interestingMatchers_2212_; lean_object* v_uninteresting_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2227_; 
v_interestingStructures_2210_ = lean_ctor_get(v_typeAnalysis_2202_, 0);
v_interestingEnums_2211_ = lean_ctor_get(v_typeAnalysis_2202_, 1);
v_interestingMatchers_2212_ = lean_ctor_get(v_typeAnalysis_2202_, 2);
v_uninteresting_2213_ = lean_ctor_get(v_typeAnalysis_2202_, 3);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_typeAnalysis_2202_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2215_ = v_typeAnalysis_2202_;
v_isShared_2216_ = v_isSharedCheck_2227_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_uninteresting_2213_);
lean_inc(v_interestingMatchers_2212_);
lean_inc(v_interestingEnums_2211_);
lean_inc(v_interestingStructures_2210_);
lean_dec(v_typeAnalysis_2202_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2227_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2199_, v___x_2200_, v_interestingEnums_2211_, v_n_2186_, v___x_2217_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v___x_2218_);
v___x_2220_ = v___x_2215_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_interestingStructures_2210_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_interestingMatchers_2212_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_uninteresting_2213_);
v___x_2220_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2222_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v___x_2220_);
v___x_2222_ = v___x_2208_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_caches_2203_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_target_2204_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_hypotheses_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*4, v_didChange_2206_);
v___x_2222_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_st_ref_put(v_a_2188_, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2217_);
return v___x_2224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_2243_, lean_object* v_k_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_typeAnalysis_2250_; lean_object* v_caches_2251_; lean_object* v_target_2252_; lean_object* v_hypotheses_2253_; uint8_t v_didChange_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2276_; 
v___x_2247_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2248_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2249_ = lean_st_ref_take(v_a_2245_);
v_typeAnalysis_2250_ = lean_ctor_get(v___x_2249_, 1);
v_caches_2251_ = lean_ctor_get(v___x_2249_, 0);
v_target_2252_ = lean_ctor_get(v___x_2249_, 2);
v_hypotheses_2253_ = lean_ctor_get(v___x_2249_, 3);
v_didChange_2254_ = lean_ctor_get_uint8(v___x_2249_, sizeof(void*)*4);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2256_ = v___x_2249_;
v_isShared_2257_ = v_isSharedCheck_2276_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_hypotheses_2253_);
lean_inc(v_target_2252_);
lean_inc(v_typeAnalysis_2250_);
lean_inc(v_caches_2251_);
lean_dec(v___x_2249_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2276_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_interestingStructures_2258_; lean_object* v_interestingEnums_2259_; lean_object* v_interestingMatchers_2260_; lean_object* v_uninteresting_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2275_; 
v_interestingStructures_2258_ = lean_ctor_get(v_typeAnalysis_2250_, 0);
v_interestingEnums_2259_ = lean_ctor_get(v_typeAnalysis_2250_, 1);
v_interestingMatchers_2260_ = lean_ctor_get(v_typeAnalysis_2250_, 2);
v_uninteresting_2261_ = lean_ctor_get(v_typeAnalysis_2250_, 3);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_typeAnalysis_2250_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2263_ = v_typeAnalysis_2250_;
v_isShared_2264_ = v_isSharedCheck_2275_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_uninteresting_2261_);
lean_inc(v_interestingMatchers_2260_);
lean_inc(v_interestingEnums_2259_);
lean_inc(v_interestingStructures_2258_);
lean_dec(v_typeAnalysis_2250_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2275_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2265_ = lean_box(0);
v___x_2266_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2247_, v___x_2248_, v_interestingMatchers_2260_, v_n_2243_, v_k_2244_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 2, v___x_2266_);
v___x_2268_ = v___x_2263_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_interestingStructures_2258_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_interestingEnums_2259_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_uninteresting_2261_);
v___x_2268_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_2268_);
v___x_2270_ = v___x_2256_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_caches_2251_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_target_2252_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v_hypotheses_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2273_, sizeof(void*)*4, v_didChange_2254_);
v___x_2270_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_st_ref_put(v_a_2245_, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2265_);
return v___x_2272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_2277_, lean_object* v_k_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_2277_, v_k_2278_, v_a_2279_);
lean_dec(v_a_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_2282_, lean_object* v_k_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_typeAnalysis_2299_; lean_object* v_caches_2300_; lean_object* v_target_2301_; lean_object* v_hypotheses_2302_; uint8_t v_didChange_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2325_; 
v___x_2296_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2298_ = lean_st_ref_take(v_a_2285_);
v_typeAnalysis_2299_ = lean_ctor_get(v___x_2298_, 1);
v_caches_2300_ = lean_ctor_get(v___x_2298_, 0);
v_target_2301_ = lean_ctor_get(v___x_2298_, 2);
v_hypotheses_2302_ = lean_ctor_get(v___x_2298_, 3);
v_didChange_2303_ = lean_ctor_get_uint8(v___x_2298_, sizeof(void*)*4);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2305_ = v___x_2298_;
v_isShared_2306_ = v_isSharedCheck_2325_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_hypotheses_2302_);
lean_inc(v_target_2301_);
lean_inc(v_typeAnalysis_2299_);
lean_inc(v_caches_2300_);
lean_dec(v___x_2298_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2325_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_interestingStructures_2307_; lean_object* v_interestingEnums_2308_; lean_object* v_interestingMatchers_2309_; lean_object* v_uninteresting_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2324_; 
v_interestingStructures_2307_ = lean_ctor_get(v_typeAnalysis_2299_, 0);
v_interestingEnums_2308_ = lean_ctor_get(v_typeAnalysis_2299_, 1);
v_interestingMatchers_2309_ = lean_ctor_get(v_typeAnalysis_2299_, 2);
v_uninteresting_2310_ = lean_ctor_get(v_typeAnalysis_2299_, 3);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_typeAnalysis_2299_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2312_ = v_typeAnalysis_2299_;
v_isShared_2313_ = v_isSharedCheck_2324_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_uninteresting_2310_);
lean_inc(v_interestingMatchers_2309_);
lean_inc(v_interestingEnums_2308_);
lean_inc(v_interestingStructures_2307_);
lean_dec(v_typeAnalysis_2299_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2324_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2314_ = lean_box(0);
v___x_2315_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2296_, v___x_2297_, v_interestingMatchers_2309_, v_n_2282_, v_k_2283_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 2, v___x_2315_);
v___x_2317_ = v___x_2312_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_interestingStructures_2307_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_interestingEnums_2308_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v___x_2315_);
lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_uninteresting_2310_);
v___x_2317_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2319_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___x_2317_);
v___x_2319_ = v___x_2305_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_caches_2300_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_target_2301_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_hypotheses_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2322_, sizeof(void*)*4, v_didChange_2303_);
v___x_2319_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_st_ref_put(v_a_2285_, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2314_);
return v___x_2321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_2326_, lean_object* v_k_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_2326_, v_k_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v_typeAnalysis_2347_; lean_object* v_caches_2348_; lean_object* v_target_2349_; lean_object* v_hypotheses_2350_; uint8_t v_didChange_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2373_; 
v___x_2344_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2345_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2346_ = lean_st_ref_take(v_a_2342_);
v_typeAnalysis_2347_ = lean_ctor_get(v___x_2346_, 1);
v_caches_2348_ = lean_ctor_get(v___x_2346_, 0);
v_target_2349_ = lean_ctor_get(v___x_2346_, 2);
v_hypotheses_2350_ = lean_ctor_get(v___x_2346_, 3);
v_didChange_2351_ = lean_ctor_get_uint8(v___x_2346_, sizeof(void*)*4);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2353_ = v___x_2346_;
v_isShared_2354_ = v_isSharedCheck_2373_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_hypotheses_2350_);
lean_inc(v_target_2349_);
lean_inc(v_typeAnalysis_2347_);
lean_inc(v_caches_2348_);
lean_dec(v___x_2346_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2373_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_interestingStructures_2355_; lean_object* v_interestingEnums_2356_; lean_object* v_interestingMatchers_2357_; lean_object* v_uninteresting_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2372_; 
v_interestingStructures_2355_ = lean_ctor_get(v_typeAnalysis_2347_, 0);
v_interestingEnums_2356_ = lean_ctor_get(v_typeAnalysis_2347_, 1);
v_interestingMatchers_2357_ = lean_ctor_get(v_typeAnalysis_2347_, 2);
v_uninteresting_2358_ = lean_ctor_get(v_typeAnalysis_2347_, 3);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_typeAnalysis_2347_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2360_ = v_typeAnalysis_2347_;
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_uninteresting_2358_);
lean_inc(v_interestingMatchers_2357_);
lean_inc(v_interestingEnums_2356_);
lean_inc(v_interestingStructures_2355_);
lean_dec(v_typeAnalysis_2347_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2362_ = lean_box(0);
v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2344_, v___x_2345_, v_uninteresting_2358_, v_n_2341_, v___x_2362_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 3, v___x_2363_);
v___x_2365_ = v___x_2360_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_interestingStructures_2355_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_interestingEnums_2356_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_interestingMatchers_2357_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v___x_2365_);
v___x_2367_ = v___x_2353_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_caches_2348_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_target_2349_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_hypotheses_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2370_, sizeof(void*)*4, v_didChange_2351_);
v___x_2367_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_st_ref_put(v_a_2342_, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2362_);
return v___x_2369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_2374_, v_a_2375_);
lean_dec(v_a_2375_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v_typeAnalysis_2394_; lean_object* v_caches_2395_; lean_object* v_target_2396_; lean_object* v_hypotheses_2397_; uint8_t v_didChange_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2420_; 
v___x_2391_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2392_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2393_ = lean_st_ref_take(v_a_2380_);
v_typeAnalysis_2394_ = lean_ctor_get(v___x_2393_, 1);
v_caches_2395_ = lean_ctor_get(v___x_2393_, 0);
v_target_2396_ = lean_ctor_get(v___x_2393_, 2);
v_hypotheses_2397_ = lean_ctor_get(v___x_2393_, 3);
v_didChange_2398_ = lean_ctor_get_uint8(v___x_2393_, sizeof(void*)*4);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2400_ = v___x_2393_;
v_isShared_2401_ = v_isSharedCheck_2420_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_hypotheses_2397_);
lean_inc(v_target_2396_);
lean_inc(v_typeAnalysis_2394_);
lean_inc(v_caches_2395_);
lean_dec(v___x_2393_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2420_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v_interestingStructures_2402_; lean_object* v_interestingEnums_2403_; lean_object* v_interestingMatchers_2404_; lean_object* v_uninteresting_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2419_; 
v_interestingStructures_2402_ = lean_ctor_get(v_typeAnalysis_2394_, 0);
v_interestingEnums_2403_ = lean_ctor_get(v_typeAnalysis_2394_, 1);
v_interestingMatchers_2404_ = lean_ctor_get(v_typeAnalysis_2394_, 2);
v_uninteresting_2405_ = lean_ctor_get(v_typeAnalysis_2394_, 3);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_typeAnalysis_2394_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2407_ = v_typeAnalysis_2394_;
v_isShared_2408_ = v_isSharedCheck_2419_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_uninteresting_2405_);
lean_inc(v_interestingMatchers_2404_);
lean_inc(v_interestingEnums_2403_);
lean_inc(v_interestingStructures_2402_);
lean_dec(v_typeAnalysis_2394_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2419_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2409_ = lean_box(0);
v___x_2410_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2391_, v___x_2392_, v_uninteresting_2405_, v_n_2378_, v___x_2409_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 3, v___x_2410_);
v___x_2412_ = v___x_2407_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_interestingStructures_2402_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_interestingEnums_2403_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_interestingMatchers_2404_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2414_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 1, v___x_2412_);
v___x_2414_ = v___x_2400_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_caches_2395_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_target_2396_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_hypotheses_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2417_, sizeof(void*)*4, v_didChange_2398_);
v___x_2414_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_st_ref_put(v_a_2380_, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2409_);
return v___x_2416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
return v_res_2434_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_unsigned_to_nat(16u);
v___x_2437_ = lean_mk_array(v___x_2436_, v___x_2435_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v___x_2438_);
return v___x_2440_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_2442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
lean_ctor_set(v___x_2442_, 2, v___x_2441_);
lean_ctor_set(v___x_2442_, 3, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_ctx_2445_, lean_object* v_target_2446_, lean_object* v_x_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2458_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2459_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2460_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2461_ = 0;
v___x_2462_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2462_, 0, v___x_2458_);
lean_ctor_set(v___x_2462_, 1, v___x_2459_);
lean_ctor_set(v___x_2462_, 2, v_target_2446_);
lean_ctor_set(v___x_2462_, 3, v___x_2460_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*4, v___x_2461_);
v___x_2463_ = lean_st_mk_ref(v___x_2462_);
lean_inc(v_a_2456_);
lean_inc_ref(v_a_2455_);
lean_inc(v_a_2454_);
lean_inc_ref(v_a_2453_);
lean_inc(v_a_2452_);
lean_inc_ref(v_a_2451_);
lean_inc(v_a_2450_);
lean_inc_ref(v_a_2449_);
lean_inc(v_a_2448_);
lean_inc(v___x_2463_);
v___x_2464_ = lean_apply_12(v_x_2447_, v_ctx_2445_, v___x_2463_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, lean_box(0));
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2474_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2474_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2474_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2469_ = lean_st_ref_get(v___x_2463_);
lean_dec(v___x_2463_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2465_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2470_);
v___x_2472_ = v___x_2467_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v___x_2463_);
v_a_2475_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2464_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2464_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_ctx_2483_, lean_object* v_target_2484_, lean_object* v_x_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_ctx_2483_, v_target_2484_, v_x_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_2497_, lean_object* v_ctx_2498_, lean_object* v_target_2499_, lean_object* v_x_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2511_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2512_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2513_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2514_ = 0;
v___x_2515_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2515_, 0, v___x_2511_);
lean_ctor_set(v___x_2515_, 1, v___x_2512_);
lean_ctor_set(v___x_2515_, 2, v_target_2499_);
lean_ctor_set(v___x_2515_, 3, v___x_2513_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*4, v___x_2514_);
v___x_2516_ = lean_st_mk_ref(v___x_2515_);
lean_inc(v_a_2509_);
lean_inc_ref(v_a_2508_);
lean_inc(v_a_2507_);
lean_inc_ref(v_a_2506_);
lean_inc(v_a_2505_);
lean_inc_ref(v_a_2504_);
lean_inc(v_a_2503_);
lean_inc_ref(v_a_2502_);
lean_inc(v_a_2501_);
lean_inc(v___x_2516_);
v___x_2517_ = lean_apply_12(v_x_2500_, v_ctx_2498_, v___x_2516_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, lean_box(0));
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2527_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2527_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2527_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2522_ = lean_st_ref_get(v___x_2516_);
lean_dec(v___x_2516_);
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_a_2518_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2523_);
v___x_2525_ = v___x_2520_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v___x_2516_);
v_a_2528_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2517_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2517_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_2536_, lean_object* v_ctx_2537_, lean_object* v_target_2538_, lean_object* v_x_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_2536_, v_ctx_2537_, v_target_2538_, v_x_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_ctx_2551_, lean_object* v_target_2552_, lean_object* v_x_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2564_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2565_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2566_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2567_ = 0;
v___x_2568_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2568_, 0, v___x_2564_);
lean_ctor_set(v___x_2568_, 1, v___x_2565_);
lean_ctor_set(v___x_2568_, 2, v_target_2552_);
lean_ctor_set(v___x_2568_, 3, v___x_2566_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*4, v___x_2567_);
v___x_2569_ = lean_st_mk_ref(v___x_2568_);
lean_inc(v_a_2562_);
lean_inc_ref(v_a_2561_);
lean_inc(v_a_2560_);
lean_inc_ref(v_a_2559_);
lean_inc(v_a_2558_);
lean_inc_ref(v_a_2557_);
lean_inc(v_a_2556_);
lean_inc_ref(v_a_2555_);
lean_inc(v_a_2554_);
lean_inc(v___x_2569_);
v___x_2570_ = lean_apply_12(v_x_2553_, v_ctx_2551_, v___x_2569_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, lean_box(0));
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2579_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_st_ref_get(v___x_2569_);
lean_dec(v___x_2569_);
lean_dec(v___x_2575_);
if (v_isShared_2574_ == 0)
{
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2571_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_dec(v___x_2569_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_ctx_2580_, lean_object* v_target_2581_, lean_object* v_x_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_ctx_2580_, v_target_2581_, v_x_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_2594_, lean_object* v_ctx_2595_, lean_object* v_target_2596_, lean_object* v_x_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2608_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2609_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2610_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2611_ = 0;
v___x_2612_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2612_, 0, v___x_2608_);
lean_ctor_set(v___x_2612_, 1, v___x_2609_);
lean_ctor_set(v___x_2612_, 2, v_target_2596_);
lean_ctor_set(v___x_2612_, 3, v___x_2610_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*4, v___x_2611_);
v___x_2613_ = lean_st_mk_ref(v___x_2612_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
lean_inc(v_a_2600_);
lean_inc_ref(v_a_2599_);
lean_inc(v_a_2598_);
lean_inc(v___x_2613_);
v___x_2614_ = lean_apply_12(v_x_2597_, v_ctx_2595_, v___x_2613_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2623_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2619_ = lean_st_ref_get(v___x_2613_);
lean_dec(v___x_2613_);
lean_dec(v___x_2619_);
if (v_isShared_2618_ == 0)
{
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2615_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
else
{
lean_dec(v___x_2613_);
return v___x_2614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_2624_, lean_object* v_ctx_2625_, lean_object* v_target_2626_, lean_object* v_x_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_2624_, v_ctx_2625_, v_target_2626_, v_x_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
return v_res_2638_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2642_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2643_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___f_2645_; lean_object* v___x_2646_; 
v___x_2644_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2);
v___f_2645_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2646_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2645_, v___x_2644_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3);
v___x_2648_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2649_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2648_, v___x_2647_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___f_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4);
v___f_2651_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2652_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2651_, v___x_2650_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5);
v___x_2654_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2655_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2654_, v___x_2653_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; 
v___x_2656_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6);
v___f_2657_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2658_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2657_, v___x_2656_);
return v___x_2658_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___f_2660_; lean_object* v___x_2661_; 
v___x_2659_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7);
v___f_2660_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2661_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2660_, v___x_2659_);
return v___x_2661_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___x_2663_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2664_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2663_, v___x_2662_);
return v___x_2664_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; 
v___x_2665_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___f_2666_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2667_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2666_, v___x_2665_);
return v___x_2667_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2670_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2671_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2672_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2673_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2672_, v___x_2671_, v___x_2670_);
return v___x_2673_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___f_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; 
v___x_2674_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___f_2675_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2676_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2677_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2676_, v___f_2675_, v___x_2674_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2678_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14);
v___x_2679_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2680_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2681_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2680_, v___x_2679_, v___x_2678_);
return v___x_2681_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___f_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; 
v___x_2682_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15);
v___f_2683_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2684_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2685_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2684_, v___f_2683_, v___x_2682_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2686_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16);
v___x_2687_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2688_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2689_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2688_, v___x_2687_, v___x_2686_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; lean_object* v___x_2693_; 
v___x_2690_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___f_2691_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2692_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2693_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2692_, v___f_2691_, v___x_2690_);
return v___x_2693_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; 
v___x_2694_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18);
v___f_2695_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2696_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2697_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2696_, v___f_2695_, v___x_2694_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2698_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19);
v___x_2699_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2700_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2701_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2700_, v___x_2699_, v___x_2698_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___f_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; 
v___x_2702_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___f_2703_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2704_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2705_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2704_, v___f_2703_, v___x_2702_);
return v___x_2705_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v_cls_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_cls_2716_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2717_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_2718_ = l_Lean_Name_append(v___x_2717_, v_cls_2716_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___f_2721_; 
v___x_2719_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2720_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2721_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2721_, 0, v___x_2720_);
lean_closure_set(v___f_2721_, 1, v___x_2719_);
return v___f_2721_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___f_2722_; lean_object* v___f_2723_; lean_object* v___f_2724_; 
v___f_2722_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2723_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___f_2724_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2724_, 0, v___f_2723_);
lean_closure_set(v___f_2724_, 1, v___f_2722_);
return v___f_2724_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___f_2726_; lean_object* v___f_2727_; 
v___x_2725_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2726_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_2727_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2727_, 0, v___f_2726_);
lean_closure_set(v___f_2727_, 1, v___x_2725_);
return v___f_2727_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___f_2728_; lean_object* v___f_2729_; lean_object* v___f_2730_; 
v___f_2728_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2729_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_2730_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2730_, 0, v___f_2729_);
lean_closure_set(v___f_2730_, 1, v___f_2728_);
return v___f_2730_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33(void){
_start:
{
lean_object* v___f_2731_; lean_object* v___f_2732_; lean_object* v___f_2733_; 
v___f_2731_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2732_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___f_2733_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2733_, 0, v___f_2732_);
lean_closure_set(v___f_2733_, 1, v___f_2731_);
return v___f_2733_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___f_2735_; lean_object* v___f_2736_; 
v___x_2734_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2735_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33);
v___f_2736_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2736_, 0, v___f_2735_);
lean_closure_set(v___f_2736_, 1, v___x_2734_);
return v___f_2736_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35(void){
_start:
{
lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___f_2739_; 
v___f_2737_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2738_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v___f_2739_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2739_, 0, v___f_2738_);
lean_closure_set(v___f_2739_, 1, v___f_2737_);
return v___f_2739_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36));
v___x_2742_ = l_Lean_stringToMessageData(v___x_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v___y_2757_; lean_object* v___x_2775_; lean_object* v_toApplicative_2776_; lean_object* v_toFunctor_2777_; lean_object* v_toSeq_2778_; lean_object* v_toSeqLeft_2779_; lean_object* v_toSeqRight_2780_; lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v___f_2783_; lean_object* v___f_2784_; lean_object* v___x_2785_; lean_object* v___f_2786_; lean_object* v___f_2787_; lean_object* v___f_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v_toApplicative_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2843_; 
v___x_2775_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2776_ = lean_ctor_get(v___x_2775_, 0);
v_toFunctor_2777_ = lean_ctor_get(v_toApplicative_2776_, 0);
v_toSeq_2778_ = lean_ctor_get(v_toApplicative_2776_, 2);
v_toSeqLeft_2779_ = lean_ctor_get(v_toApplicative_2776_, 3);
v_toSeqRight_2780_ = lean_ctor_get(v_toApplicative_2776_, 4);
v___f_2781_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2782_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2777_, 2);
v___f_2783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2783_, 0, v_toFunctor_2777_);
v___f_2784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2784_, 0, v_toFunctor_2777_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___f_2783_);
lean_ctor_set(v___x_2785_, 1, v___f_2784_);
lean_inc(v_toSeqRight_2780_);
v___f_2786_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2786_, 0, v_toSeqRight_2780_);
lean_inc(v_toSeqLeft_2779_);
v___f_2787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2787_, 0, v_toSeqLeft_2779_);
lean_inc(v_toSeq_2778_);
v___f_2788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2788_, 0, v_toSeq_2778_);
v___x_2789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2785_);
lean_ctor_set(v___x_2789_, 1, v___f_2781_);
lean_ctor_set(v___x_2789_, 2, v___f_2788_);
lean_ctor_set(v___x_2789_, 3, v___f_2787_);
lean_ctor_set(v___x_2789_, 4, v___f_2786_);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v___f_2782_);
v___x_2791_ = l_StateRefT_x27_instMonad___redArg(v___x_2790_);
v_toApplicative_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2791_, 1);
lean_dec(v_unused_2844_);
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2843_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_toApplicative_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2843_;
goto v_resetjp_2793_;
}
v___jp_2756_:
{
lean_object* v___x_2758_; lean_object* v_caches_2759_; lean_object* v_typeAnalysis_2760_; lean_object* v_target_2761_; lean_object* v_hypotheses_2762_; uint8_t v_didChange_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2774_; 
v___x_2758_ = lean_st_ref_take(v___y_2757_);
v_caches_2759_ = lean_ctor_get(v___x_2758_, 0);
v_typeAnalysis_2760_ = lean_ctor_get(v___x_2758_, 1);
v_target_2761_ = lean_ctor_get(v___x_2758_, 2);
v_hypotheses_2762_ = lean_ctor_get(v___x_2758_, 3);
v_didChange_2763_ = lean_ctor_get_uint8(v___x_2758_, sizeof(void*)*4);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2765_ = v___x_2758_;
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_hypotheses_2762_);
lean_inc(v_target_2761_);
lean_inc(v_typeAnalysis_2760_);
lean_inc(v_caches_2759_);
lean_dec(v___x_2758_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = lean_array_push(v_hypotheses_2762_, v_hyp_2743_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 3, v___x_2768_);
v___x_2770_ = v___x_2765_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_caches_2759_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_typeAnalysis_2760_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_target_2761_);
lean_ctor_set(v_reuseFailAlloc_2773_, 3, v___x_2768_);
lean_ctor_set_uint8(v_reuseFailAlloc_2773_, sizeof(void*)*4, v_didChange_2763_);
v___x_2770_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_st_ref_put(v___y_2757_, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2767_);
return v___x_2772_;
}
}
}
v_resetjp_2793_:
{
lean_object* v_toFunctor_2796_; lean_object* v_toSeq_2797_; lean_object* v_toSeqLeft_2798_; lean_object* v_toSeqRight_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2841_; 
v_toFunctor_2796_ = lean_ctor_get(v_toApplicative_2792_, 0);
v_toSeq_2797_ = lean_ctor_get(v_toApplicative_2792_, 2);
v_toSeqLeft_2798_ = lean_ctor_get(v_toApplicative_2792_, 3);
v_toSeqRight_2799_ = lean_ctor_get(v_toApplicative_2792_, 4);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_toApplicative_2792_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v_toApplicative_2792_, 1);
lean_dec(v_unused_2842_);
v___x_2801_ = v_toApplicative_2792_;
v_isShared_2802_ = v_isSharedCheck_2841_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_toSeqRight_2799_);
lean_inc(v_toSeqLeft_2798_);
lean_inc(v_toSeq_2797_);
lean_inc(v_toFunctor_2796_);
lean_dec(v_toApplicative_2792_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2841_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___f_2803_; lean_object* v___f_2804_; lean_object* v___f_2805_; lean_object* v___f_2806_; lean_object* v___x_2807_; lean_object* v___f_2808_; lean_object* v___f_2809_; lean_object* v___f_2810_; lean_object* v___x_2812_; 
v___f_2803_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2804_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2796_);
v___f_2805_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2805_, 0, v_toFunctor_2796_);
v___f_2806_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2806_, 0, v_toFunctor_2796_);
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___f_2805_);
lean_ctor_set(v___x_2807_, 1, v___f_2806_);
v___f_2808_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2808_, 0, v_toSeqRight_2799_);
v___f_2809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2809_, 0, v_toSeqLeft_2798_);
v___f_2810_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2810_, 0, v_toSeq_2797_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 4, v___f_2808_);
lean_ctor_set(v___x_2801_, 3, v___f_2809_);
lean_ctor_set(v___x_2801_, 2, v___f_2810_);
lean_ctor_set(v___x_2801_, 1, v___f_2803_);
lean_ctor_set(v___x_2801_, 0, v___x_2807_);
v___x_2812_ = v___x_2801_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___f_2803_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v___f_2810_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v___f_2809_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v___f_2808_);
v___x_2812_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2814_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 1, v___f_2804_);
lean_ctor_set(v___x_2794_, 0, v___x_2812_);
v___x_2814_ = v___x_2794_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___f_2804_);
v___x_2814_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v_toCold_2824_; lean_object* v_options_2825_; uint8_t v_hasTrace_2826_; 
v___x_2815_ = l_StateRefT_x27_instMonad___redArg(v___x_2814_);
v___x_2816_ = l_ReaderT_instMonad___redArg(v___x_2815_);
v___x_2817_ = l_StateRefT_x27_instMonad___redArg(v___x_2816_);
v___x_2818_ = l_ReaderT_instMonad___redArg(v___x_2817_);
v___x_2819_ = l_ReaderT_instMonad___redArg(v___x_2818_);
v___x_2820_ = l_StateRefT_x27_instMonad___redArg(v___x_2819_);
v___x_2821_ = l_ReaderT_instMonad___redArg(v___x_2820_);
v___x_2822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2823_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toCold_2824_ = lean_ctor_get(v_a_2753_, 0);
v_options_2825_ = lean_ctor_get(v_toCold_2824_, 2);
v_hasTrace_2826_ = lean_ctor_get_uint8(v_options_2825_, sizeof(void*)*1);
if (v_hasTrace_2826_ == 0)
{
lean_dec_ref(v___x_2821_);
v___y_2757_ = v_a_2745_;
goto v___jp_2756_;
}
else
{
lean_object* v_toMonadRef_2827_; lean_object* v_inheritedTraceOptions_2828_; lean_object* v_cls_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v_toMonadRef_2827_ = lean_ctor_get(v___x_2823_, 0);
v_inheritedTraceOptions_2828_ = lean_ctor_get(v_toCold_2824_, 11);
v_cls_2829_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2830_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2828_, v_options_2825_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_dec_ref(v___x_2821_);
v___y_2757_ = v_a_2745_;
goto v___jp_2756_;
}
else
{
lean_object* v_type_2832_; lean_object* v___f_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_5398__overap_2837_; lean_object* v___x_2838_; 
v_type_2832_ = lean_ctor_get(v_hyp_2743_, 1);
v___f_2833_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_2834_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_2832_);
v___x_2835_ = l_Lean_MessageData_ofExpr(v_type_2832_);
v___x_2836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
lean_inc_ref(v_toMonadRef_2827_);
v___x_5398__overap_2837_ = l_Lean_addTrace___redArg(v___x_2821_, v___x_2822_, v_toMonadRef_2827_, v___f_2833_, v_cls_2829_, v___x_2836_);
lean_inc(v_a_2754_);
lean_inc_ref(v_a_2753_);
lean_inc(v_a_2752_);
lean_inc_ref(v_a_2751_);
lean_inc(v_a_2750_);
lean_inc_ref(v_a_2749_);
lean_inc(v_a_2748_);
lean_inc_ref(v_a_2747_);
lean_inc(v_a_2746_);
lean_inc(v_a_2745_);
lean_inc_ref(v_a_2744_);
v___x_2838_ = lean_apply_12(v___x_5398__overap_2837_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, lean_box(0));
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_dec_ref_known(v___x_2838_, 1);
v___y_2757_ = v_a_2745_;
goto v___jp_2756_;
}
else
{
lean_dec_ref(v_hyp_2743_);
return v___x_2838_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2859_, lean_object* v___x_2860_, lean_object* v_toMonadRef_2861_, lean_object* v___f_2862_, lean_object* v_x_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_toCold_2880_; lean_object* v_options_2881_; uint8_t v_hasTrace_2882_; 
v_toCold_2880_ = lean_ctor_get(v___y_2874_, 0);
v_options_2881_ = lean_ctor_get(v_toCold_2880_, 2);
v_hasTrace_2882_ = lean_ctor_get_uint8(v_options_2881_, sizeof(void*)*1);
if (v_hasTrace_2882_ == 0)
{
lean_dec_ref(v___y_2864_);
lean_dec(v___f_2862_);
lean_dec_ref(v_toMonadRef_2861_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2859_);
goto v___jp_2877_;
}
else
{
lean_object* v_inheritedTraceOptions_2883_; lean_object* v_cls_2884_; lean_object* v___x_2885_; uint8_t v___x_2886_; 
v_inheritedTraceOptions_2883_ = lean_ctor_get(v_toCold_2880_, 11);
v_cls_2884_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2885_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2886_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2883_, v_options_2881_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_dec_ref(v___y_2864_);
lean_dec(v___f_2862_);
lean_dec_ref(v_toMonadRef_2861_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2859_);
goto v___jp_2877_;
}
else
{
lean_object* v_type_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_6389__overap_2891_; lean_object* v___x_2892_; 
v_type_2887_ = lean_ctor_get(v___y_2864_, 1);
lean_inc_ref(v_type_2887_);
lean_dec_ref(v___y_2864_);
v___x_2888_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2889_ = l_Lean_MessageData_ofExpr(v_type_2887_);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_6389__overap_2891_ = l_Lean_addTrace___redArg(v___x_2859_, v___x_2860_, v_toMonadRef_2861_, v___f_2862_, v_cls_2884_, v___x_2890_);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
lean_inc(v___y_2871_);
lean_inc_ref(v___y_2870_);
lean_inc(v___y_2869_);
lean_inc_ref(v___y_2868_);
lean_inc(v___y_2867_);
lean_inc(v___y_2866_);
lean_inc_ref(v___y_2865_);
v___x_2892_ = lean_apply_12(v___x_6389__overap_2891_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, lean_box(0));
return v___x_2892_;
}
}
v___jp_2877_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2893_ = _args[0];
lean_object* v___x_2894_ = _args[1];
lean_object* v_toMonadRef_2895_ = _args[2];
lean_object* v___f_2896_ = _args[3];
lean_object* v_x_2897_ = _args[4];
lean_object* v___y_2898_ = _args[5];
lean_object* v___y_2899_ = _args[6];
lean_object* v___y_2900_ = _args[7];
lean_object* v___y_2901_ = _args[8];
lean_object* v___y_2902_ = _args[9];
lean_object* v___y_2903_ = _args[10];
lean_object* v___y_2904_ = _args[11];
lean_object* v___y_2905_ = _args[12];
lean_object* v___y_2906_ = _args[13];
lean_object* v___y_2907_ = _args[14];
lean_object* v___y_2908_ = _args[15];
lean_object* v___y_2909_ = _args[16];
lean_object* v___y_2910_ = _args[17];
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2893_, v___x_2894_, v_toMonadRef_2895_, v___f_2896_, v_x_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___y_2944_; lean_object* v___x_2945_; lean_object* v_toApplicative_2946_; lean_object* v_toFunctor_2947_; lean_object* v_toSeq_2948_; lean_object* v_toSeqLeft_2949_; lean_object* v_toSeqRight_2950_; lean_object* v___f_2951_; lean_object* v___f_2952_; lean_object* v___f_2953_; lean_object* v___f_2954_; lean_object* v___x_2955_; lean_object* v___f_2956_; lean_object* v___f_2957_; lean_object* v___f_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v_toApplicative_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_3014_; 
v___x_2945_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2946_ = lean_ctor_get(v___x_2945_, 0);
v_toFunctor_2947_ = lean_ctor_get(v_toApplicative_2946_, 0);
v_toSeq_2948_ = lean_ctor_get(v_toApplicative_2946_, 2);
v_toSeqLeft_2949_ = lean_ctor_get(v_toApplicative_2946_, 3);
v_toSeqRight_2950_ = lean_ctor_get(v_toApplicative_2946_, 4);
v___f_2951_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2952_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2947_, 2);
v___f_2953_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2953_, 0, v_toFunctor_2947_);
v___f_2954_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2954_, 0, v_toFunctor_2947_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___f_2953_);
lean_ctor_set(v___x_2955_, 1, v___f_2954_);
lean_inc(v_toSeqRight_2950_);
v___f_2956_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2956_, 0, v_toSeqRight_2950_);
lean_inc(v_toSeqLeft_2949_);
v___f_2957_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2957_, 0, v_toSeqLeft_2949_);
lean_inc(v_toSeq_2948_);
v___f_2958_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2958_, 0, v_toSeq_2948_);
v___x_2959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2955_);
lean_ctor_set(v___x_2959_, 1, v___f_2951_);
lean_ctor_set(v___x_2959_, 2, v___f_2958_);
lean_ctor_set(v___x_2959_, 3, v___f_2957_);
lean_ctor_set(v___x_2959_, 4, v___f_2956_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v___f_2952_);
v___x_2961_ = l_StateRefT_x27_instMonad___redArg(v___x_2960_);
v_toApplicative_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v___x_2961_, 1);
lean_dec(v_unused_3015_);
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_3014_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_toApplicative_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_3014_;
goto v_resetjp_2963_;
}
v___jp_2925_:
{
lean_object* v___x_2926_; lean_object* v_caches_2927_; lean_object* v_typeAnalysis_2928_; lean_object* v_target_2929_; lean_object* v_hypotheses_2930_; uint8_t v_didChange_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2942_; 
v___x_2926_ = lean_st_ref_take(v_a_2914_);
v_caches_2927_ = lean_ctor_get(v___x_2926_, 0);
v_typeAnalysis_2928_ = lean_ctor_get(v___x_2926_, 1);
v_target_2929_ = lean_ctor_get(v___x_2926_, 2);
v_hypotheses_2930_ = lean_ctor_get(v___x_2926_, 3);
v_didChange_2931_ = lean_ctor_get_uint8(v___x_2926_, sizeof(void*)*4);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2933_ = v___x_2926_;
v_isShared_2934_ = v_isSharedCheck_2942_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_hypotheses_2930_);
lean_inc(v_target_2929_);
lean_inc(v_typeAnalysis_2928_);
lean_inc(v_caches_2927_);
lean_dec(v___x_2926_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2942_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2935_ = lean_box(0);
v___x_2936_ = l_Array_append___redArg(v_hypotheses_2930_, v_hyps_2912_);
lean_dec_ref(v_hyps_2912_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 3, v___x_2936_);
v___x_2938_ = v___x_2933_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_caches_2927_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_typeAnalysis_2928_);
lean_ctor_set(v_reuseFailAlloc_2941_, 2, v_target_2929_);
lean_ctor_set(v_reuseFailAlloc_2941_, 3, v___x_2936_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*4, v_didChange_2931_);
v___x_2938_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_st_ref_put(v_a_2914_, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2935_);
return v___x_2940_;
}
}
}
v___jp_2943_:
{
if (lean_obj_tag(v___y_2944_) == 0)
{
lean_dec_ref_known(v___y_2944_, 1);
goto v___jp_2925_;
}
else
{
lean_dec_ref(v_hyps_2912_);
return v___y_2944_;
}
}
v_resetjp_2963_:
{
lean_object* v_toFunctor_2966_; lean_object* v_toSeq_2967_; lean_object* v_toSeqLeft_2968_; lean_object* v_toSeqRight_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_3012_; 
v_toFunctor_2966_ = lean_ctor_get(v_toApplicative_2962_, 0);
v_toSeq_2967_ = lean_ctor_get(v_toApplicative_2962_, 2);
v_toSeqLeft_2968_ = lean_ctor_get(v_toApplicative_2962_, 3);
v_toSeqRight_2969_ = lean_ctor_get(v_toApplicative_2962_, 4);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_toApplicative_2962_);
if (v_isSharedCheck_3012_ == 0)
{
lean_object* v_unused_3013_; 
v_unused_3013_ = lean_ctor_get(v_toApplicative_2962_, 1);
lean_dec(v_unused_3013_);
v___x_2971_ = v_toApplicative_2962_;
v_isShared_2972_ = v_isSharedCheck_3012_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_toSeqRight_2969_);
lean_inc(v_toSeqLeft_2968_);
lean_inc(v_toSeq_2967_);
lean_inc(v_toFunctor_2966_);
lean_dec(v_toApplicative_2962_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_3012_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___f_2980_; lean_object* v___x_2982_; 
v___f_2973_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2974_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2966_);
v___f_2975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2975_, 0, v_toFunctor_2966_);
v___f_2976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2976_, 0, v_toFunctor_2966_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___f_2975_);
lean_ctor_set(v___x_2977_, 1, v___f_2976_);
v___f_2978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2978_, 0, v_toSeqRight_2969_);
v___f_2979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2979_, 0, v_toSeqLeft_2968_);
v___f_2980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2980_, 0, v_toSeq_2967_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 4, v___f_2978_);
lean_ctor_set(v___x_2971_, 3, v___f_2979_);
lean_ctor_set(v___x_2971_, 2, v___f_2980_);
lean_ctor_set(v___x_2971_, 1, v___f_2973_);
lean_ctor_set(v___x_2971_, 0, v___x_2977_);
v___x_2982_ = v___x_2971_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___f_2973_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v___f_2980_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v___f_2979_);
lean_ctor_set(v_reuseFailAlloc_3011_, 4, v___f_2978_);
v___x_2982_ = v_reuseFailAlloc_3011_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2984_; 
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 1, v___f_2974_);
lean_ctor_set(v___x_2964_, 0, v___x_2982_);
v___x_2984_ = v___x_2964_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___f_2974_);
v___x_2984_ = v_reuseFailAlloc_3010_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v_toMonadRef_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2985_ = l_StateRefT_x27_instMonad___redArg(v___x_2984_);
v___x_2986_ = l_ReaderT_instMonad___redArg(v___x_2985_);
v___x_2987_ = l_StateRefT_x27_instMonad___redArg(v___x_2986_);
v___x_2988_ = l_ReaderT_instMonad___redArg(v___x_2987_);
v___x_2989_ = l_ReaderT_instMonad___redArg(v___x_2988_);
v___x_2990_ = l_StateRefT_x27_instMonad___redArg(v___x_2989_);
v___x_2991_ = l_ReaderT_instMonad___redArg(v___x_2990_);
v___x_2992_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2993_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_2994_ = lean_ctor_get(v___x_2993_, 0);
v___x_2995_ = lean_unsigned_to_nat(0u);
v___x_2996_ = lean_array_get_size(v_hyps_2912_);
v___x_2997_ = lean_nat_dec_lt(v___x_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_dec_ref(v___x_2991_);
goto v___jp_2925_;
}
else
{
lean_object* v___f_2998_; lean_object* v___f_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___f_2998_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
lean_inc_ref(v_toMonadRef_2994_);
lean_inc_ref(v___x_2991_);
v___f_2999_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 18, 4);
lean_closure_set(v___f_2999_, 0, v___x_2991_);
lean_closure_set(v___f_2999_, 1, v___x_2992_);
lean_closure_set(v___f_2999_, 2, v_toMonadRef_2994_);
lean_closure_set(v___f_2999_, 3, v___f_2998_);
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_nat_dec_le(v___x_2996_, v___x_2996_);
if (v___x_3001_ == 0)
{
if (v___x_2997_ == 0)
{
lean_dec_ref(v___f_2999_);
lean_dec_ref(v___x_2991_);
goto v___jp_2925_;
}
else
{
size_t v___x_3002_; size_t v___x_3003_; lean_object* v___x_6041__overap_3004_; lean_object* v___x_3005_; 
v___x_3002_ = ((size_t)0ULL);
v___x_3003_ = lean_usize_of_nat(v___x_2996_);
lean_inc_ref(v_hyps_2912_);
v___x_6041__overap_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2991_, v___f_2999_, v_hyps_2912_, v___x_3002_, v___x_3003_, v___x_3000_);
lean_inc(v_a_2923_);
lean_inc_ref(v_a_2922_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
lean_inc(v_a_2919_);
lean_inc_ref(v_a_2918_);
lean_inc(v_a_2917_);
lean_inc_ref(v_a_2916_);
lean_inc(v_a_2915_);
lean_inc(v_a_2914_);
lean_inc_ref(v_a_2913_);
v___x_3005_ = lean_apply_12(v___x_6041__overap_3004_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, lean_box(0));
v___y_2944_ = v___x_3005_;
goto v___jp_2943_;
}
}
else
{
size_t v___x_3006_; size_t v___x_3007_; lean_object* v___x_6044__overap_3008_; lean_object* v___x_3009_; 
v___x_3006_ = ((size_t)0ULL);
v___x_3007_ = lean_usize_of_nat(v___x_2996_);
lean_inc_ref(v_hyps_2912_);
v___x_6044__overap_3008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2991_, v___f_2999_, v_hyps_2912_, v___x_3006_, v___x_3007_, v___x_3000_);
lean_inc(v_a_2923_);
lean_inc_ref(v_a_2922_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
lean_inc(v_a_2919_);
lean_inc_ref(v_a_2918_);
lean_inc(v_a_2917_);
lean_inc_ref(v_a_2916_);
lean_inc(v_a_2915_);
lean_inc(v_a_2914_);
lean_inc_ref(v_a_2913_);
v___x_3009_ = lean_apply_12(v___x_6044__overap_3008_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, lean_box(0));
v___y_2944_ = v___x_3009_;
goto v___jp_2943_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_3030_){
_start:
{
lean_object* v___x_3032_; lean_object* v_hypotheses_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_st_ref_get(v_a_3030_);
v_hypotheses_3033_ = lean_ctor_get(v___x_3032_, 3);
lean_inc_ref(v_hypotheses_3033_);
lean_dec(v___x_3032_);
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_hypotheses_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_3035_);
lean_dec(v_a_3035_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v_hypotheses_3051_; lean_object* v___x_3052_; 
v___x_3050_ = lean_st_ref_get(v_a_3039_);
v_hypotheses_3051_ = lean_ctor_get(v___x_3050_, 3);
lean_inc_ref(v_hypotheses_3051_);
lean_dec(v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_hypotheses_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; lean_object* v_caches_3080_; lean_object* v_typeAnalysis_3081_; lean_object* v_target_3082_; uint8_t v_didChange_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3093_; 
v___x_3079_ = lean_st_ref_take(v___y_3068_);
v_caches_3080_ = lean_ctor_get(v___x_3079_, 0);
v_typeAnalysis_3081_ = lean_ctor_get(v___x_3079_, 1);
v_target_3082_ = lean_ctor_get(v___x_3079_, 2);
v_didChange_3083_ = lean_ctor_get_uint8(v___x_3079_, sizeof(void*)*4);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; 
v_unused_3094_ = lean_ctor_get(v___x_3079_, 3);
lean_dec(v_unused_3094_);
v___x_3085_ = v___x_3079_;
v_isShared_3086_ = v_isSharedCheck_3093_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_target_3082_);
lean_inc(v_typeAnalysis_3081_);
lean_inc(v_caches_3080_);
lean_dec(v___x_3079_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3093_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3087_ = lean_box(0);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 3, v_hyps_3066_);
v___x_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_caches_3080_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_typeAnalysis_3081_);
lean_ctor_set(v_reuseFailAlloc_3092_, 2, v_target_3082_);
lean_ctor_set(v_reuseFailAlloc_3092_, 3, v_hyps_3066_);
lean_ctor_set_uint8(v_reuseFailAlloc_3092_, sizeof(void*)*4, v_didChange_3083_);
v___x_3089_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_st_ref_put(v___y_3068_, v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3087_);
return v___x_3091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3109_, lean_object* v_hyps_3110_){
_start:
{
lean_object* v___f_3111_; lean_object* v___x_3112_; 
v___f_3111_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3111_, 0, v_hyps_3110_);
v___x_3112_ = lean_apply_2(v_inst_3109_, lean_box(0), v___f_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; lean_object* v_caches_3126_; lean_object* v_typeAnalysis_3127_; lean_object* v_target_3128_; uint8_t v_didChange_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3140_; 
v___x_3125_ = lean_st_ref_take(v___y_3114_);
v_caches_3126_ = lean_ctor_get(v___x_3125_, 0);
v_typeAnalysis_3127_ = lean_ctor_get(v___x_3125_, 1);
v_target_3128_ = lean_ctor_get(v___x_3125_, 2);
v_didChange_3129_ = lean_ctor_get_uint8(v___x_3125_, sizeof(void*)*4);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_3125_, 3);
lean_dec(v_unused_3141_);
v___x_3131_ = v___x_3125_;
v_isShared_3132_ = v_isSharedCheck_3140_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_target_3128_);
lean_inc(v_typeAnalysis_3127_);
lean_inc(v_caches_3126_);
lean_dec(v___x_3125_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3140_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3133_ = lean_box(0);
v___x_3134_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 3, v___x_3134_);
v___x_3136_ = v___x_3131_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_caches_3126_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_typeAnalysis_3127_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_target_3128_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v___x_3134_);
lean_ctor_set_uint8(v_reuseFailAlloc_3139_, sizeof(void*)*4, v_didChange_3129_);
v___x_3136_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_st_ref_put(v___y_3114_, v___x_3136_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3133_);
return v___x_3138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3155_, lean_object* v_cls_3156_, lean_object* v_____do__lift_3157_, lean_object* v_____do__lift_3158_){
_start:
{
uint8_t v_hasTrace_3159_; 
v_hasTrace_3159_ = lean_ctor_get_uint8(v_____do__lift_3158_, sizeof(void*)*1);
if (v_hasTrace_3159_ == 0)
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_dec(v_cls_3156_);
v___x_3160_ = lean_box(v_hasTrace_3159_);
v___x_3161_ = lean_apply_2(v_toPure_3155_, lean_box(0), v___x_3160_);
return v___x_3161_;
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3162_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3163_ = l_Lean_Name_append(v___x_3162_, v_cls_3156_);
v___x_3164_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3157_, v_____do__lift_3158_, v___x_3163_);
lean_dec(v___x_3163_);
v___x_3165_ = lean_box(v___x_3164_);
v___x_3166_ = lean_apply_2(v_toPure_3155_, lean_box(0), v___x_3165_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3167_, lean_object* v_cls_3168_, lean_object* v_____do__lift_3169_, lean_object* v_____do__lift_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3167_, v_cls_3168_, v_____do__lift_3169_, v_____do__lift_3170_);
lean_dec_ref(v_____do__lift_3170_);
lean_dec_ref(v_____do__lift_3169_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_inst_3172_, lean_object* v_toPure_3173_, lean_object* v_cls_3174_, lean_object* v_toBind_3175_, lean_object* v_____do__lift_3176_){
_start:
{
lean_object* v_getOptionsUnrestricted_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; 
v_getOptionsUnrestricted_3177_ = lean_ctor_get(v_inst_3172_, 1);
lean_inc(v_getOptionsUnrestricted_3177_);
lean_dec_ref(v_inst_3172_);
v___f_3178_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3178_, 0, v_toPure_3173_);
lean_closure_set(v___f_3178_, 1, v_cls_3174_);
lean_closure_set(v___f_3178_, 2, v_____do__lift_3176_);
v___x_3179_ = lean_apply_4(v_toBind_3175_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3177_, v___f_3178_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3182_ = l_Lean_stringToMessageData(v___x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3183_, lean_object* v_a_3184_, lean_object* v___y_3185_, lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_inst_3189_, lean_object* v_cls_3190_, uint8_t v_____do__lift_3191_){
_start:
{
if (v_____do__lift_3191_ == 0)
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_dec(v_cls_3190_);
lean_dec(v_inst_3189_);
lean_dec_ref(v_inst_3188_);
lean_dec_ref(v_inst_3187_);
lean_dec_ref(v_inst_3186_);
lean_dec_ref(v___y_3185_);
lean_dec_ref(v_a_3184_);
v___x_3192_ = lean_box(0);
v___x_3193_ = lean_apply_2(v_toPure_3183_, lean_box(0), v___x_3192_);
return v___x_3193_;
}
else
{
lean_object* v_type_3194_; lean_object* v_type_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_dec(v_toPure_3183_);
v_type_3194_ = lean_ctor_get(v_a_3184_, 1);
lean_inc_ref(v_type_3194_);
lean_dec_ref(v_a_3184_);
v_type_3195_ = lean_ctor_get(v___y_3185_, 1);
lean_inc_ref(v_type_3195_);
lean_dec_ref(v___y_3185_);
v___x_3196_ = l_Lean_MessageData_ofExpr(v_type_3194_);
v___x_3197_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = l_Lean_MessageData_ofExpr(v_type_3195_);
v___x_3200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3198_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Lean_addTrace___redArg(v_inst_3186_, v_inst_3187_, v_inst_3188_, v_inst_3189_, v_cls_3190_, v___x_3200_);
return v___x_3201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3202_, lean_object* v_a_3203_, lean_object* v___y_3204_, lean_object* v_inst_3205_, lean_object* v_inst_3206_, lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_cls_3209_, lean_object* v_____do__lift_3210_){
_start:
{
uint8_t v_____do__lift_3040__boxed_3211_; lean_object* v_res_3212_; 
v_____do__lift_3040__boxed_3211_ = lean_unbox(v_____do__lift_3210_);
v_res_3212_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3202_, v_a_3203_, v___y_3204_, v_inst_3205_, v_inst_3206_, v_inst_3207_, v_inst_3208_, v_cls_3209_, v_____do__lift_3040__boxed_3211_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_toPure_3215_, lean_object* v_toBind_3216_, lean_object* v_a_3217_, lean_object* v_inst_3218_, lean_object* v_inst_3219_, lean_object* v_inst_3220_, lean_object* v_x_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_getInheritedTraceOptions_3223_; lean_object* v_cls_3224_; lean_object* v___f_3225_; lean_object* v___f_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_getInheritedTraceOptions_3223_ = lean_ctor_get(v_inst_3213_, 2);
lean_inc(v_getInheritedTraceOptions_3223_);
v_cls_3224_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3216_, 2);
lean_inc(v_toPure_3215_);
v___f_3225_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3225_, 0, v_inst_3214_);
lean_closure_set(v___f_3225_, 1, v_toPure_3215_);
lean_closure_set(v___f_3225_, 2, v_cls_3224_);
lean_closure_set(v___f_3225_, 3, v_toBind_3216_);
v___f_3226_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3226_, 0, v_toPure_3215_);
lean_closure_set(v___f_3226_, 1, v_a_3217_);
lean_closure_set(v___f_3226_, 2, v___y_3222_);
lean_closure_set(v___f_3226_, 3, v_inst_3218_);
lean_closure_set(v___f_3226_, 4, v_inst_3213_);
lean_closure_set(v___f_3226_, 5, v_inst_3219_);
lean_closure_set(v___f_3226_, 6, v_inst_3220_);
lean_closure_set(v___f_3226_, 7, v_cls_3224_);
v___x_3227_ = lean_apply_4(v_toBind_3216_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3223_, v___f_3225_);
v___x_3228_ = lean_apply_4(v_toBind_3216_, lean_box(0), lean_box(0), v___x_3227_, v___f_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3229_, lean_object* v_res_3230_, lean_object* v_____r_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_apply_2(v_toPure_3229_, lean_box(0), v_res_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3233_, lean_object* v_toBind_3234_, lean_object* v___f_3235_, lean_object* v_____r_3236_){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3238_ = lean_apply_2(v_inst_3233_, lean_box(0), v___x_3237_);
v___x_3239_ = lean_apply_4(v_toBind_3234_, lean_box(0), lean_box(0), v___x_3238_, v___f_3235_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3240_, lean_object* v_____r_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_apply_1(v___f_3240_, v_____r_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3243_, lean_object* v_type_3244_, lean_object* v_type_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_cls_3250_, lean_object* v_toBind_3251_, lean_object* v___f_3252_, uint8_t v_____do__lift_3253_){
_start:
{
if (v_____do__lift_3253_ == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
lean_dec(v___f_3252_);
lean_dec(v_toBind_3251_);
lean_dec(v_cls_3250_);
lean_dec(v_inst_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec_ref(v_inst_3247_);
lean_dec_ref(v_inst_3246_);
lean_dec_ref(v_type_3245_);
lean_dec_ref(v_type_3244_);
v___x_3254_ = lean_box(0);
v___x_3255_ = lean_apply_1(v___f_3243_, v___x_3254_);
return v___x_3255_;
}
else
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec(v___f_3243_);
v___x_3256_ = l_Lean_MessageData_ofExpr(v_type_3244_);
v___x_3257_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = l_Lean_MessageData_ofExpr(v_type_3245_);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = l_Lean_addTrace___redArg(v_inst_3246_, v_inst_3247_, v_inst_3248_, v_inst_3249_, v_cls_3250_, v___x_3260_);
v___x_3262_ = lean_apply_4(v_toBind_3251_, lean_box(0), lean_box(0), v___x_3261_, v___f_3252_);
return v___x_3262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3263_, lean_object* v_type_3264_, lean_object* v_type_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_cls_3270_, lean_object* v_toBind_3271_, lean_object* v___f_3272_, lean_object* v_____do__lift_3273_){
_start:
{
uint8_t v_____do__lift_3140__boxed_3274_; lean_object* v_res_3275_; 
v_____do__lift_3140__boxed_3274_ = lean_unbox(v_____do__lift_3273_);
v_res_3275_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3263_, v_type_3264_, v_type_3265_, v_inst_3266_, v_inst_3267_, v_inst_3268_, v_inst_3269_, v_cls_3270_, v_toBind_3271_, v___f_3272_, v_____do__lift_3140__boxed_3274_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3276_, lean_object* v_inst_3277_, lean_object* v_toBind_3278_, lean_object* v_inst_3279_, lean_object* v___f_3280_, lean_object* v_a_3281_, lean_object* v_inst_3282_, lean_object* v_inst_3283_, lean_object* v_inst_3284_, lean_object* v_inst_3285_, lean_object* v___f_3286_, lean_object* v_res_3287_){
_start:
{
lean_object* v___x_3288_; lean_object* v_zero_3289_; uint8_t v_isZero_3290_; 
v___x_3288_ = lean_array_get_size(v_res_3287_);
v_zero_3289_ = lean_unsigned_to_nat(0u);
v_isZero_3290_ = lean_nat_dec_eq(v___x_3288_, v_zero_3289_);
if (v_isZero_3290_ == 1)
{
lean_object* v___f_3291_; lean_object* v___f_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
lean_dec(v___f_3286_);
lean_dec(v_inst_3285_);
lean_dec_ref(v_inst_3284_);
lean_dec_ref(v_inst_3283_);
lean_dec_ref(v_inst_3282_);
lean_dec_ref(v_a_3281_);
lean_inc_ref(v_res_3287_);
lean_inc(v_toPure_3276_);
v___f_3291_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3291_, 0, v_toPure_3276_);
lean_closure_set(v___f_3291_, 1, v_res_3287_);
lean_inc(v_toBind_3278_);
v___f_3292_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3292_, 0, v_inst_3277_);
lean_closure_set(v___f_3292_, 1, v_toBind_3278_);
lean_closure_set(v___f_3292_, 2, v___f_3291_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_nat_dec_lt(v_zero_3289_, v___x_3288_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_dec_ref(v_res_3287_);
lean_dec(v___f_3280_);
lean_dec_ref(v_inst_3279_);
v___x_3295_ = lean_apply_2(v_toPure_3276_, lean_box(0), v___x_3293_);
v___x_3296_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3295_, v___f_3292_);
return v___x_3296_;
}
else
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_nat_dec_le(v___x_3288_, v___x_3288_);
if (v___x_3297_ == 0)
{
if (v___x_3294_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec_ref(v_res_3287_);
lean_dec(v___f_3280_);
lean_dec_ref(v_inst_3279_);
v___x_3298_ = lean_apply_2(v_toPure_3276_, lean_box(0), v___x_3293_);
v___x_3299_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3298_, v___f_3292_);
return v___x_3299_;
}
else
{
size_t v___x_3300_; size_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec(v_toPure_3276_);
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = lean_usize_of_nat(v___x_3288_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3279_, v___f_3280_, v_res_3287_, v___x_3300_, v___x_3301_, v___x_3293_);
v___x_3303_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3302_, v___f_3292_);
return v___x_3303_;
}
}
else
{
size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec(v_toPure_3276_);
v___x_3304_ = ((size_t)0ULL);
v___x_3305_ = lean_usize_of_nat(v___x_3288_);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3279_, v___f_3280_, v_res_3287_, v___x_3304_, v___x_3305_, v___x_3293_);
v___x_3307_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3306_, v___f_3292_);
return v___x_3307_;
}
}
}
else
{
lean_object* v_one_3308_; lean_object* v_n_3309_; uint8_t v_isZero_3310_; 
lean_dec(v___f_3280_);
v_one_3308_ = lean_unsigned_to_nat(1u);
v_n_3309_ = lean_nat_sub(v___x_3288_, v_one_3308_);
v_isZero_3310_ = lean_nat_dec_eq(v_n_3309_, v_zero_3289_);
lean_dec(v_n_3309_);
if (v_isZero_3310_ == 1)
{
lean_object* v_newHyp_3311_; lean_object* v_type_3312_; lean_object* v_type_3313_; uint8_t v___x_3314_; 
lean_dec(v___f_3286_);
v_newHyp_3311_ = lean_array_fget_borrowed(v_res_3287_, v_zero_3289_);
v_type_3312_ = lean_ctor_get(v_newHyp_3311_, 1);
v_type_3313_ = lean_ctor_get(v_a_3281_, 1);
lean_inc_ref(v_type_3313_);
lean_dec_ref(v_a_3281_);
v___x_3314_ = lean_expr_eqv(v_type_3312_, v_type_3313_);
if (v___x_3314_ == 0)
{
lean_object* v_getInheritedTraceOptions_3315_; lean_object* v___f_3316_; lean_object* v___f_3317_; lean_object* v___f_3318_; lean_object* v_cls_3319_; lean_object* v___f_3320_; lean_object* v___f_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_inc_ref(v_type_3312_);
v_getInheritedTraceOptions_3315_ = lean_ctor_get(v_inst_3282_, 2);
lean_inc(v_getInheritedTraceOptions_3315_);
lean_inc(v_toPure_3276_);
v___f_3316_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3316_, 0, v_toPure_3276_);
lean_closure_set(v___f_3316_, 1, v_res_3287_);
lean_inc_n(v_toBind_3278_, 4);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3317_, 0, v_inst_3277_);
lean_closure_set(v___f_3317_, 1, v_toBind_3278_);
lean_closure_set(v___f_3317_, 2, v___f_3316_);
lean_inc_ref(v___f_3317_);
v___f_3318_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3318_, 0, v___f_3317_);
v_cls_3319_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3320_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3320_, 0, v_inst_3283_);
lean_closure_set(v___f_3320_, 1, v_toPure_3276_);
lean_closure_set(v___f_3320_, 2, v_cls_3319_);
lean_closure_set(v___f_3320_, 3, v_toBind_3278_);
v___f_3321_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3321_, 0, v___f_3317_);
lean_closure_set(v___f_3321_, 1, v_type_3313_);
lean_closure_set(v___f_3321_, 2, v_type_3312_);
lean_closure_set(v___f_3321_, 3, v_inst_3279_);
lean_closure_set(v___f_3321_, 4, v_inst_3282_);
lean_closure_set(v___f_3321_, 5, v_inst_3284_);
lean_closure_set(v___f_3321_, 6, v_inst_3285_);
lean_closure_set(v___f_3321_, 7, v_cls_3319_);
lean_closure_set(v___f_3321_, 8, v_toBind_3278_);
lean_closure_set(v___f_3321_, 9, v___f_3318_);
v___x_3322_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3315_, v___f_3320_);
v___x_3323_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3322_, v___f_3321_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; 
lean_dec_ref(v_type_3313_);
lean_dec(v_inst_3285_);
lean_dec_ref(v_inst_3284_);
lean_dec_ref(v_inst_3283_);
lean_dec_ref(v_inst_3282_);
lean_dec_ref(v_inst_3279_);
lean_dec(v_toBind_3278_);
lean_dec(v_inst_3277_);
v___x_3324_ = lean_apply_2(v_toPure_3276_, lean_box(0), v_res_3287_);
return v___x_3324_;
}
}
else
{
lean_object* v___f_3325_; lean_object* v___f_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
lean_dec(v_inst_3285_);
lean_dec_ref(v_inst_3284_);
lean_dec_ref(v_inst_3283_);
lean_dec_ref(v_inst_3282_);
lean_dec_ref(v_a_3281_);
lean_inc_ref(v_res_3287_);
lean_inc(v_toPure_3276_);
v___f_3325_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3325_, 0, v_toPure_3276_);
lean_closure_set(v___f_3325_, 1, v_res_3287_);
lean_inc(v_toBind_3278_);
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3326_, 0, v_inst_3277_);
lean_closure_set(v___f_3326_, 1, v_toBind_3278_);
lean_closure_set(v___f_3326_, 2, v___f_3325_);
v___x_3327_ = lean_box(0);
v___x_3328_ = lean_nat_dec_lt(v_zero_3289_, v___x_3288_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec_ref(v_res_3287_);
lean_dec(v___f_3286_);
lean_dec_ref(v_inst_3279_);
v___x_3329_ = lean_apply_2(v_toPure_3276_, lean_box(0), v___x_3327_);
v___x_3330_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3329_, v___f_3326_);
return v___x_3330_;
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_nat_dec_le(v___x_3288_, v___x_3288_);
if (v___x_3331_ == 0)
{
if (v___x_3328_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec_ref(v_res_3287_);
lean_dec(v___f_3286_);
lean_dec_ref(v_inst_3279_);
v___x_3332_ = lean_apply_2(v_toPure_3276_, lean_box(0), v___x_3327_);
v___x_3333_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3332_, v___f_3326_);
return v___x_3333_;
}
else
{
size_t v___x_3334_; size_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
lean_dec(v_toPure_3276_);
v___x_3334_ = ((size_t)0ULL);
v___x_3335_ = lean_usize_of_nat(v___x_3288_);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3279_, v___f_3286_, v_res_3287_, v___x_3334_, v___x_3335_, v___x_3327_);
v___x_3337_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3336_, v___f_3326_);
return v___x_3337_;
}
}
else
{
size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec(v_toPure_3276_);
v___x_3338_ = ((size_t)0ULL);
v___x_3339_ = lean_usize_of_nat(v___x_3288_);
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3279_, v___f_3286_, v_res_3287_, v___x_3338_, v___x_3339_, v___x_3327_);
v___x_3341_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3340_, v___f_3326_);
return v___x_3341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3342_, lean_object* v_toPure_3343_, lean_object* v_____do__lift_3344_){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = l_Array_append___redArg(v_bs_3342_, v_____do__lift_3344_);
v___x_3346_ = lean_apply_2(v_toPure_3343_, lean_box(0), v___x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3347_, lean_object* v_toPure_3348_, lean_object* v_____do__lift_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3347_, v_toPure_3348_, v_____do__lift_3349_);
lean_dec_ref(v_____do__lift_3349_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_toPure_3353_, lean_object* v_toBind_3354_, lean_object* v_inst_3355_, lean_object* v_inst_3356_, lean_object* v_inst_3357_, lean_object* v_inst_3358_, lean_object* v_f_3359_, lean_object* v_bs_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v___f_3362_; lean_object* v___f_3363_; lean_object* v___f_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_inc(v_inst_3357_);
lean_inc_ref(v_inst_3356_);
lean_inc_ref(v_inst_3355_);
lean_inc_ref_n(v_a_3361_, 2);
lean_inc_n(v_toBind_3354_, 3);
lean_inc_n(v_toPure_3353_, 2);
lean_inc_ref(v_inst_3352_);
lean_inc_ref(v_inst_3351_);
v___f_3362_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3362_, 0, v_inst_3351_);
lean_closure_set(v___f_3362_, 1, v_inst_3352_);
lean_closure_set(v___f_3362_, 2, v_toPure_3353_);
lean_closure_set(v___f_3362_, 3, v_toBind_3354_);
lean_closure_set(v___f_3362_, 4, v_a_3361_);
lean_closure_set(v___f_3362_, 5, v_inst_3355_);
lean_closure_set(v___f_3362_, 6, v_inst_3356_);
lean_closure_set(v___f_3362_, 7, v_inst_3357_);
lean_inc_ref(v___f_3362_);
v___f_3363_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3363_, 0, v_toPure_3353_);
lean_closure_set(v___f_3363_, 1, v_inst_3358_);
lean_closure_set(v___f_3363_, 2, v_toBind_3354_);
lean_closure_set(v___f_3363_, 3, v_inst_3355_);
lean_closure_set(v___f_3363_, 4, v___f_3362_);
lean_closure_set(v___f_3363_, 5, v_a_3361_);
lean_closure_set(v___f_3363_, 6, v_inst_3351_);
lean_closure_set(v___f_3363_, 7, v_inst_3352_);
lean_closure_set(v___f_3363_, 8, v_inst_3356_);
lean_closure_set(v___f_3363_, 9, v_inst_3357_);
lean_closure_set(v___f_3363_, 10, v___f_3362_);
v___f_3364_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3364_, 0, v_bs_3360_);
lean_closure_set(v___f_3364_, 1, v_toPure_3353_);
v___x_3365_ = lean_apply_1(v_f_3359_, v_a_3361_);
v___x_3366_ = lean_apply_4(v_toBind_3354_, lean_box(0), lean_box(0), v___x_3365_, v___f_3363_);
v___x_3367_ = lean_apply_4(v_toBind_3354_, lean_box(0), lean_box(0), v___x_3366_, v___f_3364_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3370_, lean_object* v_toPure_3371_, lean_object* v_toBind_3372_, lean_object* v___f_3373_, lean_object* v_inst_3374_, lean_object* v___f_3375_, lean_object* v_____r_3376_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3379_ = lean_array_get_size(v_hyps_3370_);
v___x_3380_ = lean_nat_dec_lt(v___x_3377_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_dec(v___f_3375_);
lean_dec_ref(v_inst_3374_);
lean_dec_ref(v_hyps_3370_);
v___x_3381_ = lean_apply_2(v_toPure_3371_, lean_box(0), v___x_3378_);
v___x_3382_ = lean_apply_4(v_toBind_3372_, lean_box(0), lean_box(0), v___x_3381_, v___f_3373_);
return v___x_3382_;
}
else
{
size_t v___x_3383_; size_t v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec(v_toPure_3371_);
v___x_3383_ = ((size_t)0ULL);
v___x_3384_ = lean_usize_of_nat(v___x_3379_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3374_, v___f_3375_, v_hyps_3370_, v___x_3383_, v___x_3384_, v___x_3378_);
v___x_3386_ = lean_apply_4(v_toBind_3372_, lean_box(0), lean_box(0), v___x_3385_, v___f_3373_);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3387_, lean_object* v_toBind_3388_, lean_object* v___f_3389_, lean_object* v_inst_3390_, lean_object* v___f_3391_, lean_object* v_inst_3392_, lean_object* v___f_3393_, lean_object* v_hyps_3394_){
_start:
{
lean_object* v___f_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_inc(v_toBind_3388_);
v___f_3395_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3395_, 0, v_hyps_3394_);
lean_closure_set(v___f_3395_, 1, v_toPure_3387_);
lean_closure_set(v___f_3395_, 2, v_toBind_3388_);
lean_closure_set(v___f_3395_, 3, v___f_3389_);
lean_closure_set(v___f_3395_, 4, v_inst_3390_);
lean_closure_set(v___f_3395_, 5, v___f_3391_);
v___x_3396_ = lean_apply_2(v_inst_3392_, lean_box(0), v___f_3393_);
v___x_3397_ = lean_apply_4(v_toBind_3388_, lean_box(0), lean_box(0), v___x_3396_, v___f_3395_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3399_, lean_object* v_inst_3400_, lean_object* v_inst_3401_, lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_f_3405_){
_start:
{
lean_object* v_toApplicative_3406_; lean_object* v_toBind_3407_; lean_object* v_toPure_3408_; lean_object* v___f_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___f_3413_; lean_object* v___f_3414_; lean_object* v___x_3415_; 
v_toApplicative_3406_ = lean_ctor_get(v_inst_3399_, 0);
v_toBind_3407_ = lean_ctor_get(v_inst_3399_, 1);
lean_inc_n(v_toBind_3407_, 3);
v_toPure_3408_ = lean_ctor_get(v_toApplicative_3406_, 1);
lean_inc_n(v_toPure_3408_, 2);
lean_inc_n(v_inst_3404_, 3);
v___f_3409_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3409_, 0, v_inst_3404_);
v___f_3410_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3411_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3412_ = lean_apply_2(v_inst_3404_, lean_box(0), v___x_3411_);
lean_inc_ref(v_inst_3399_);
v___f_3413_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3413_, 0, v_inst_3400_);
lean_closure_set(v___f_3413_, 1, v_inst_3401_);
lean_closure_set(v___f_3413_, 2, v_toPure_3408_);
lean_closure_set(v___f_3413_, 3, v_toBind_3407_);
lean_closure_set(v___f_3413_, 4, v_inst_3399_);
lean_closure_set(v___f_3413_, 5, v_inst_3403_);
lean_closure_set(v___f_3413_, 6, v_inst_3402_);
lean_closure_set(v___f_3413_, 7, v_inst_3404_);
lean_closure_set(v___f_3413_, 8, v_f_3405_);
v___f_3414_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3414_, 0, v_toPure_3408_);
lean_closure_set(v___f_3414_, 1, v_toBind_3407_);
lean_closure_set(v___f_3414_, 2, v___f_3409_);
lean_closure_set(v___f_3414_, 3, v_inst_3399_);
lean_closure_set(v___f_3414_, 4, v___f_3413_);
lean_closure_set(v___f_3414_, 5, v_inst_3404_);
lean_closure_set(v___f_3414_, 6, v___f_3410_);
v___x_3415_ = lean_apply_4(v_toBind_3407_, lean_box(0), lean_box(0), v___x_3412_, v___f_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3416_, lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_f_3423_){
_start:
{
lean_object* v_toApplicative_3424_; lean_object* v_toBind_3425_; lean_object* v_toPure_3426_; lean_object* v___f_3427_; lean_object* v___f_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___f_3431_; lean_object* v___f_3432_; lean_object* v___x_3433_; 
v_toApplicative_3424_ = lean_ctor_get(v_inst_3417_, 0);
v_toBind_3425_ = lean_ctor_get(v_inst_3417_, 1);
lean_inc_n(v_toBind_3425_, 3);
v_toPure_3426_ = lean_ctor_get(v_toApplicative_3424_, 1);
lean_inc_n(v_toPure_3426_, 2);
lean_inc_n(v_inst_3422_, 3);
v___f_3427_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3427_, 0, v_inst_3422_);
v___f_3428_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3429_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3430_ = lean_apply_2(v_inst_3422_, lean_box(0), v___x_3429_);
lean_inc_ref(v_inst_3417_);
v___f_3431_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3431_, 0, v_inst_3418_);
lean_closure_set(v___f_3431_, 1, v_inst_3419_);
lean_closure_set(v___f_3431_, 2, v_toPure_3426_);
lean_closure_set(v___f_3431_, 3, v_toBind_3425_);
lean_closure_set(v___f_3431_, 4, v_inst_3417_);
lean_closure_set(v___f_3431_, 5, v_inst_3421_);
lean_closure_set(v___f_3431_, 6, v_inst_3420_);
lean_closure_set(v___f_3431_, 7, v_inst_3422_);
lean_closure_set(v___f_3431_, 8, v_f_3423_);
v___f_3432_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3432_, 0, v_toPure_3426_);
lean_closure_set(v___f_3432_, 1, v_toBind_3425_);
lean_closure_set(v___f_3432_, 2, v___f_3427_);
lean_closure_set(v___f_3432_, 3, v_inst_3417_);
lean_closure_set(v___f_3432_, 4, v___f_3431_);
lean_closure_set(v___f_3432_, 5, v_inst_3422_);
lean_closure_set(v___f_3432_, 6, v___f_3428_);
v___x_3433_ = lean_apply_4(v_toBind_3425_, lean_box(0), lean_box(0), v___x_3430_, v___f_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3434_, lean_object* v_____r_3435_){
_start:
{
uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = 0;
v___x_3437_ = lean_box(v___x_3436_);
v___x_3438_ = lean_apply_2(v_toPure_3434_, lean_box(0), v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_snd_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v_caches_3453_; lean_object* v_typeAnalysis_3454_; lean_object* v_target_3455_; uint8_t v_didChange_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3466_; 
v___x_3452_ = lean_st_ref_take(v___y_3441_);
v_caches_3453_ = lean_ctor_get(v___x_3452_, 0);
v_typeAnalysis_3454_ = lean_ctor_get(v___x_3452_, 1);
v_target_3455_ = lean_ctor_get(v___x_3452_, 2);
v_didChange_3456_ = lean_ctor_get_uint8(v___x_3452_, sizeof(void*)*4);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; 
v_unused_3467_ = lean_ctor_get(v___x_3452_, 3);
lean_dec(v_unused_3467_);
v___x_3458_ = v___x_3452_;
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_target_3455_);
lean_inc(v_typeAnalysis_3454_);
lean_inc(v_caches_3453_);
lean_dec(v___x_3452_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = lean_box(0);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 3, v_snd_3439_);
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_caches_3453_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_typeAnalysis_3454_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v_target_3455_);
lean_ctor_set(v_reuseFailAlloc_3465_, 3, v_snd_3439_);
lean_ctor_set_uint8(v_reuseFailAlloc_3465_, sizeof(void*)*4, v_didChange_3456_);
v___x_3462_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_st_ref_put(v___y_3441_, v___x_3462_);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3460_);
return v___x_3464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed(lean_object* v_snd_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(v_snd_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_inst_3482_, lean_object* v_toBind_3483_, lean_object* v___f_3484_, lean_object* v_toPure_3485_, lean_object* v_____s_3486_){
_start:
{
lean_object* v_fst_3487_; 
v_fst_3487_ = lean_ctor_get(v_____s_3486_, 0);
if (lean_obj_tag(v_fst_3487_) == 0)
{
lean_object* v_snd_3488_; lean_object* v___f_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_dec(v_toPure_3485_);
v_snd_3488_ = lean_ctor_get(v_____s_3486_, 1);
lean_inc(v_snd_3488_);
lean_dec_ref(v_____s_3486_);
v___f_3489_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_3489_, 0, v_snd_3488_);
v___x_3490_ = lean_apply_2(v_inst_3482_, lean_box(0), v___f_3489_);
v___x_3491_ = lean_apply_4(v_toBind_3483_, lean_box(0), lean_box(0), v___x_3490_, v___f_3484_);
return v___x_3491_;
}
else
{
lean_object* v_val_3492_; lean_object* v___x_3493_; 
lean_inc_ref(v_fst_3487_);
lean_dec_ref(v_____s_3486_);
lean_dec(v___f_3484_);
lean_dec(v_toBind_3483_);
lean_dec(v_inst_3482_);
v_val_3492_ = lean_ctor_get(v_fst_3487_, 0);
lean_inc(v_val_3492_);
lean_dec_ref_known(v_fst_3487_, 1);
v___x_3493_ = lean_apply_2(v_toPure_3485_, lean_box(0), v_val_3492_);
return v___x_3493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_toPure_3494_, lean_object* v_____do__lift_3495_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_apply_2(v_toPure_3494_, lean_box(0), v_____do__lift_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3497_, lean_object* v_next_3498_, lean_object* v_G_3499_, lean_object* v_____do__lift_3500_){
_start:
{
if (lean_obj_tag(v_____do__lift_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; 
lean_dec(v_G_3499_);
v_a_3501_ = lean_ctor_get(v_____do__lift_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v_____do__lift_3500_, 1);
v___x_3502_ = lean_apply_2(v_toPure_3497_, lean_box(0), v_a_3501_);
return v___x_3502_;
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_dec(v_toPure_3497_);
v_a_3503_ = lean_ctor_get(v_____do__lift_3500_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v_____do__lift_3500_, 1);
v___x_3504_ = lean_unsigned_to_nat(1u);
v___x_3505_ = lean_nat_add(v_next_3498_, v___x_3504_);
v___x_3506_ = lean_apply_4(v_G_3499_, v___x_3505_, v_a_3503_, lean_box(0), lean_box(0));
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3507_, lean_object* v_next_3508_, lean_object* v_G_3509_, lean_object* v_____do__lift_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3507_, v_next_3508_, v_G_3509_, v_____do__lift_3510_);
lean_dec(v_next_3508_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(uint8_t v___x_3512_, lean_object* v_snd_3513_, lean_object* v_toPure_3514_, lean_object* v_____r_3515_){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3516_ = lean_box(v___x_3512_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v_snd_3513_);
v___x_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
v___x_3520_ = lean_apply_2(v_toPure_3514_, lean_box(0), v___x_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed(lean_object* v___x_3521_, lean_object* v_snd_3522_, lean_object* v_toPure_3523_, lean_object* v_____r_3524_){
_start:
{
uint8_t v___x_1675__boxed_3525_; lean_object* v_res_3526_; 
v___x_1675__boxed_3525_ = lean_unbox(v___x_3521_);
v_res_3526_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_1675__boxed_3525_, v_snd_3522_, v_toPure_3523_, v_____r_3524_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_snd_3527_, lean_object* v_newHyp_3528_, lean_object* v___x_3529_, lean_object* v_toPure_3530_, lean_object* v_____r_3531_){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3532_ = lean_array_push(v_snd_3527_, v_newHyp_3528_);
v___x_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3529_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
v___x_3535_ = lean_apply_2(v_toPure_3530_, lean_box(0), v___x_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_toPure_3536_, lean_object* v___x_3537_, lean_object* v_____do__lift_3538_, lean_object* v_____do__lift_3539_){
_start:
{
uint8_t v_hasTrace_3540_; 
v_hasTrace_3540_ = lean_ctor_get_uint8(v_____do__lift_3539_, sizeof(void*)*1);
if (v_hasTrace_3540_ == 0)
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_dec(v___x_3537_);
v___x_3541_ = lean_box(v_hasTrace_3540_);
v___x_3542_ = lean_apply_2(v_toPure_3536_, lean_box(0), v___x_3541_);
return v___x_3542_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3543_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3544_ = l_Lean_Name_append(v___x_3543_, v___x_3537_);
v___x_3545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3538_, v_____do__lift_3539_, v___x_3544_);
lean_dec(v___x_3544_);
v___x_3546_ = lean_box(v___x_3545_);
v___x_3547_ = lean_apply_2(v_toPure_3536_, lean_box(0), v___x_3546_);
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed(lean_object* v_toPure_3548_, lean_object* v___x_3549_, lean_object* v_____do__lift_3550_, lean_object* v_____do__lift_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(v_toPure_3548_, v___x_3549_, v_____do__lift_3550_, v_____do__lift_3551_);
lean_dec_ref(v_____do__lift_3551_);
lean_dec_ref(v_____do__lift_3550_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v_inst_3553_, lean_object* v_toPure_3554_, lean_object* v___x_3555_, lean_object* v_toBind_3556_, lean_object* v_____do__lift_3557_){
_start:
{
lean_object* v_getOptionsUnrestricted_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; 
v_getOptionsUnrestricted_3558_ = lean_ctor_get(v_inst_3553_, 1);
lean_inc(v_getOptionsUnrestricted_3558_);
lean_dec_ref(v_inst_3553_);
v___f_3559_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_3559_, 0, v_toPure_3554_);
lean_closure_set(v___f_3559_, 1, v___x_3555_);
lean_closure_set(v___f_3559_, 2, v_____do__lift_3557_);
v___x_3560_ = lean_apply_4(v_toBind_3556_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3558_, v___f_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object* v___f_3561_, lean_object* v___x_3562_, lean_object* v_type_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_toMonadRef_3566_, lean_object* v_inst_3567_, lean_object* v___x_3568_, lean_object* v_toBind_3569_, lean_object* v___f_3570_, uint8_t v_____do__lift_3571_){
_start:
{
if (v_____do__lift_3571_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v___f_3570_);
lean_dec(v_toBind_3569_);
lean_dec(v___x_3568_);
lean_dec(v_inst_3567_);
lean_dec_ref(v_toMonadRef_3566_);
lean_dec_ref(v_inst_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec_ref(v_type_3563_);
lean_dec_ref(v___x_3562_);
v___x_3572_ = lean_box(0);
v___x_3573_ = lean_apply_1(v___f_3561_, v___x_3572_);
return v___x_3573_;
}
else
{
lean_object* v_type_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec(v___f_3561_);
v_type_3574_ = lean_ctor_get(v___x_3562_, 1);
lean_inc_ref(v_type_3574_);
lean_dec_ref(v___x_3562_);
v___x_3575_ = l_Lean_MessageData_ofExpr(v_type_3574_);
v___x_3576_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = l_Lean_MessageData_ofExpr(v_type_3563_);
v___x_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3577_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = l_Lean_addTrace___redArg(v_inst_3564_, v_inst_3565_, v_toMonadRef_3566_, v_inst_3567_, v___x_3568_, v___x_3579_);
v___x_3581_ = lean_apply_4(v_toBind_3569_, lean_box(0), lean_box(0), v___x_3580_, v___f_3570_);
return v___x_3581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___f_3582_, lean_object* v___x_3583_, lean_object* v_type_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_toMonadRef_3587_, lean_object* v_inst_3588_, lean_object* v___x_3589_, lean_object* v_toBind_3590_, lean_object* v___f_3591_, lean_object* v_____do__lift_3592_){
_start:
{
uint8_t v_____do__lift_1750__boxed_3593_; lean_object* v_res_3594_; 
v_____do__lift_1750__boxed_3593_ = lean_unbox(v_____do__lift_3592_);
v_res_3594_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3582_, v___x_3583_, v_type_3584_, v_inst_3585_, v_inst_3586_, v_toMonadRef_3587_, v_inst_3588_, v___x_3589_, v_toBind_3590_, v___f_3591_, v_____do__lift_1750__boxed_3593_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v___x_3595_, lean_object* v_snd_3596_, lean_object* v___x_3597_, lean_object* v_toPure_3598_, lean_object* v_inst_3599_, lean_object* v_toBind_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_, lean_object* v_toMonadRef_3604_, lean_object* v_inst_3605_, lean_object* v___f_3606_, lean_object* v_newHyp_3607_){
_start:
{
lean_object* v_type_3608_; lean_object* v_value_3609_; uint8_t v___x_3610_; 
v_type_3608_ = lean_ctor_get(v_newHyp_3607_, 1);
v_value_3609_ = lean_ctor_get(v_newHyp_3607_, 2);
lean_inc_ref(v_type_3608_);
v___x_3610_ = l_Lean_Expr_isFalse(v_type_3608_);
if (v___x_3610_ == 0)
{
lean_object* v_type_3611_; lean_object* v___f_3612_; lean_object* v___f_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; uint8_t v___x_3623_; 
lean_dec(v___f_3606_);
v_type_3611_ = lean_ctor_get(v___x_3595_, 1);
lean_inc(v_toPure_3598_);
lean_inc(v___x_3597_);
lean_inc_ref(v_newHyp_3607_);
lean_inc(v_snd_3596_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3612_, 0, v_snd_3596_);
lean_closure_set(v___f_3612_, 1, v_newHyp_3607_);
lean_closure_set(v___f_3612_, 2, v___x_3597_);
lean_closure_set(v___f_3612_, 3, v_toPure_3598_);
v___f_3613_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3613_, 0, v___f_3612_);
lean_inc(v_toBind_3600_);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3614_, 0, v_inst_3599_);
lean_closure_set(v___f_3614_, 1, v_toBind_3600_);
lean_closure_set(v___f_3614_, 2, v___f_3613_);
lean_inc_ref(v___f_3614_);
v___f_3615_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3615_, 0, v___f_3614_);
v___x_3623_ = lean_expr_eqv(v_type_3611_, v_type_3608_);
if (v___x_3623_ == 0)
{
lean_inc_ref(v_type_3608_);
lean_dec_ref(v_newHyp_3607_);
lean_dec(v___x_3597_);
lean_dec(v_snd_3596_);
goto v___jp_3616_;
}
else
{
if (v___x_3610_ == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
lean_dec_ref(v___f_3615_);
lean_dec_ref(v___f_3614_);
lean_dec(v_inst_3605_);
lean_dec_ref(v_toMonadRef_3604_);
lean_dec_ref(v_inst_3603_);
lean_dec_ref(v_inst_3602_);
lean_dec_ref(v_inst_3601_);
lean_dec(v_toBind_3600_);
lean_dec_ref(v___x_3595_);
v___x_3624_ = lean_box(0);
v___x_3625_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3596_, v_newHyp_3607_, v___x_3597_, v_toPure_3598_, v___x_3624_);
return v___x_3625_;
}
else
{
lean_inc_ref(v_type_3608_);
lean_dec_ref(v_newHyp_3607_);
lean_dec(v___x_3597_);
lean_dec(v_snd_3596_);
goto v___jp_3616_;
}
}
v___jp_3616_:
{
lean_object* v_getInheritedTraceOptions_3617_; lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_getInheritedTraceOptions_3617_ = lean_ctor_get(v_inst_3601_, 2);
lean_inc(v_getInheritedTraceOptions_3617_);
v___x_3618_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3600_, 3);
v___f_3619_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3619_, 0, v_inst_3602_);
lean_closure_set(v___f_3619_, 1, v_toPure_3598_);
lean_closure_set(v___f_3619_, 2, v___x_3618_);
lean_closure_set(v___f_3619_, 3, v_toBind_3600_);
v___f_3620_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3620_, 0, v___f_3614_);
lean_closure_set(v___f_3620_, 1, v___x_3595_);
lean_closure_set(v___f_3620_, 2, v_type_3608_);
lean_closure_set(v___f_3620_, 3, v_inst_3603_);
lean_closure_set(v___f_3620_, 4, v_inst_3601_);
lean_closure_set(v___f_3620_, 5, v_toMonadRef_3604_);
lean_closure_set(v___f_3620_, 6, v_inst_3605_);
lean_closure_set(v___f_3620_, 7, v___x_3618_);
lean_closure_set(v___f_3620_, 8, v_toBind_3600_);
lean_closure_set(v___f_3620_, 9, v___f_3615_);
v___x_3621_ = lean_apply_4(v_toBind_3600_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3617_, v___f_3619_);
v___x_3622_ = lean_apply_4(v_toBind_3600_, lean_box(0), lean_box(0), v___x_3621_, v___f_3620_);
return v___x_3622_;
}
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
lean_inc_ref(v_value_3609_);
lean_dec_ref(v_newHyp_3607_);
lean_dec(v_inst_3605_);
lean_dec_ref(v_toMonadRef_3604_);
lean_dec_ref(v_inst_3603_);
lean_dec_ref(v_inst_3602_);
lean_dec_ref(v_inst_3601_);
lean_dec(v_toPure_3598_);
lean_dec(v___x_3597_);
lean_dec(v_snd_3596_);
lean_dec_ref(v___x_3595_);
v___x_3626_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3626_, 0, v_value_3609_);
v___x_3627_ = lean_apply_2(v_inst_3599_, lean_box(0), v___x_3626_);
v___x_3628_ = lean_apply_4(v_toBind_3600_, lean_box(0), lean_box(0), v___x_3627_, v___f_3606_);
return v___x_3628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3629_, lean_object* v_toPure_3630_, lean_object* v_hyps_3631_, lean_object* v___x_3632_, lean_object* v_inst_3633_, lean_object* v_toBind_3634_, lean_object* v_inst_3635_, lean_object* v_inst_3636_, lean_object* v_inst_3637_, lean_object* v_toMonadRef_3638_, lean_object* v_inst_3639_, lean_object* v_f_3640_, lean_object* v___f_3641_, lean_object* v_next_3642_, lean_object* v_acc_3643_, lean_object* v_h_3644_, lean_object* v_G_3645_){
_start:
{
uint8_t v___x_3646_; 
v___x_3646_ = lean_nat_dec_lt(v_next_3642_, v___x_3629_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; 
lean_dec(v_G_3645_);
lean_dec(v_next_3642_);
lean_dec(v___f_3641_);
lean_dec(v_f_3640_);
lean_dec(v_inst_3639_);
lean_dec_ref(v_toMonadRef_3638_);
lean_dec_ref(v_inst_3637_);
lean_dec_ref(v_inst_3636_);
lean_dec_ref(v_inst_3635_);
lean_dec(v_toBind_3634_);
lean_dec(v_inst_3633_);
lean_dec(v___x_3632_);
v___x_3647_ = lean_apply_2(v_toPure_3630_, lean_box(0), v_acc_3643_);
return v___x_3647_;
}
else
{
lean_object* v_snd_3648_; lean_object* v___f_3649_; lean_object* v___x_3650_; lean_object* v___f_3651_; lean_object* v___x_3652_; lean_object* v___f_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_snd_3648_ = lean_ctor_get(v_acc_3643_, 1);
lean_inc_n(v_snd_3648_, 2);
lean_dec_ref(v_acc_3643_);
lean_inc(v_next_3642_);
lean_inc_n(v_toPure_3630_, 2);
v___f_3649_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3649_, 0, v_toPure_3630_);
lean_closure_set(v___f_3649_, 1, v_next_3642_);
lean_closure_set(v___f_3649_, 2, v_G_3645_);
v___x_3650_ = lean_box(v___x_3646_);
v___f_3651_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3651_, 0, v___x_3650_);
lean_closure_set(v___f_3651_, 1, v_snd_3648_);
lean_closure_set(v___f_3651_, 2, v_toPure_3630_);
v___x_3652_ = lean_array_fget_borrowed(v_hyps_3631_, v_next_3642_);
lean_inc_n(v_toBind_3634_, 3);
lean_inc_n(v___x_3652_, 2);
v___f_3653_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9), 13, 12);
lean_closure_set(v___f_3653_, 0, v___x_3652_);
lean_closure_set(v___f_3653_, 1, v_snd_3648_);
lean_closure_set(v___f_3653_, 2, v___x_3632_);
lean_closure_set(v___f_3653_, 3, v_toPure_3630_);
lean_closure_set(v___f_3653_, 4, v_inst_3633_);
lean_closure_set(v___f_3653_, 5, v_toBind_3634_);
lean_closure_set(v___f_3653_, 6, v_inst_3635_);
lean_closure_set(v___f_3653_, 7, v_inst_3636_);
lean_closure_set(v___f_3653_, 8, v_inst_3637_);
lean_closure_set(v___f_3653_, 9, v_toMonadRef_3638_);
lean_closure_set(v___f_3653_, 10, v_inst_3639_);
lean_closure_set(v___f_3653_, 11, v___f_3651_);
v___x_3654_ = lean_apply_2(v_f_3640_, v_next_3642_, v___x_3652_);
v___x_3655_ = lean_apply_4(v_toBind_3634_, lean_box(0), lean_box(0), v___x_3654_, v___f_3653_);
v___x_3656_ = lean_apply_4(v_toBind_3634_, lean_box(0), lean_box(0), v___x_3655_, v___f_3641_);
v___x_3657_ = lean_apply_4(v_toBind_3634_, lean_box(0), lean_box(0), v___x_3656_, v___f_3649_);
return v___x_3657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3658_ = _args[0];
lean_object* v_toPure_3659_ = _args[1];
lean_object* v_hyps_3660_ = _args[2];
lean_object* v___x_3661_ = _args[3];
lean_object* v_inst_3662_ = _args[4];
lean_object* v_toBind_3663_ = _args[5];
lean_object* v_inst_3664_ = _args[6];
lean_object* v_inst_3665_ = _args[7];
lean_object* v_inst_3666_ = _args[8];
lean_object* v_toMonadRef_3667_ = _args[9];
lean_object* v_inst_3668_ = _args[10];
lean_object* v_f_3669_ = _args[11];
lean_object* v___f_3670_ = _args[12];
lean_object* v_next_3671_ = _args[13];
lean_object* v_acc_3672_ = _args[14];
lean_object* v_h_3673_ = _args[15];
lean_object* v_G_3674_ = _args[16];
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3658_, v_toPure_3659_, v_hyps_3660_, v___x_3661_, v_inst_3662_, v_toBind_3663_, v_inst_3664_, v_inst_3665_, v_inst_3666_, v_toMonadRef_3667_, v_inst_3668_, v_f_3669_, v___f_3670_, v_next_3671_, v_acc_3672_, v_h_3673_, v_G_3674_);
lean_dec_ref(v_hyps_3660_);
lean_dec(v___x_3658_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3676_, lean_object* v_inst_3677_, lean_object* v_toBind_3678_, lean_object* v_inst_3679_, lean_object* v_inst_3680_, lean_object* v_inst_3681_, lean_object* v_toMonadRef_3682_, lean_object* v_inst_3683_, lean_object* v_f_3684_, lean_object* v___f_3685_, lean_object* v___f_3686_, lean_object* v_hyps_3687_){
_start:
{
lean_object* v___x_3688_; lean_object* v_newHyps_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___f_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3688_ = lean_array_get_size(v_hyps_3687_);
v_newHyps_3689_ = lean_mk_empty_array_with_capacity(v___x_3688_);
v___x_3690_ = lean_unsigned_to_nat(0u);
v___x_3691_ = lean_box(0);
lean_inc(v_toBind_3678_);
v___f_3692_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3692_, 0, v___x_3688_);
lean_closure_set(v___f_3692_, 1, v_toPure_3676_);
lean_closure_set(v___f_3692_, 2, v_hyps_3687_);
lean_closure_set(v___f_3692_, 3, v___x_3691_);
lean_closure_set(v___f_3692_, 4, v_inst_3677_);
lean_closure_set(v___f_3692_, 5, v_toBind_3678_);
lean_closure_set(v___f_3692_, 6, v_inst_3679_);
lean_closure_set(v___f_3692_, 7, v_inst_3680_);
lean_closure_set(v___f_3692_, 8, v_inst_3681_);
lean_closure_set(v___f_3692_, 9, v_toMonadRef_3682_);
lean_closure_set(v___f_3692_, 10, v_inst_3683_);
lean_closure_set(v___f_3692_, 11, v_f_3684_);
lean_closure_set(v___f_3692_, 12, v___f_3685_);
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3691_);
lean_ctor_set(v___x_3693_, 1, v_newHyps_3689_);
v___x_3694_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3692_, v___x_3690_, v___x_3693_, lean_box(0));
v___x_3695_ = lean_apply_4(v_toBind_3678_, lean_box(0), lean_box(0), v___x_3694_, v___f_3686_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3696_, lean_object* v_inst_3697_, lean_object* v_inst_3698_, lean_object* v_inst_3699_, lean_object* v_inst_3700_, lean_object* v_inst_3701_, lean_object* v_f_3702_){
_start:
{
lean_object* v_toApplicative_3703_; lean_object* v_toBind_3704_; lean_object* v_toPure_3705_; lean_object* v_toMonadRef_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___f_3709_; lean_object* v___f_3710_; lean_object* v___f_3711_; lean_object* v___f_3712_; lean_object* v___x_3713_; 
v_toApplicative_3703_ = lean_ctor_get(v_inst_3696_, 0);
v_toBind_3704_ = lean_ctor_get(v_inst_3696_, 1);
lean_inc_n(v_toBind_3704_, 3);
v_toPure_3705_ = lean_ctor_get(v_toApplicative_3703_, 1);
lean_inc_n(v_toPure_3705_, 4);
v_toMonadRef_3706_ = lean_ctor_get(v_inst_3698_, 1);
lean_inc_ref(v_toMonadRef_3706_);
lean_dec_ref(v_inst_3698_);
v___x_3707_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3697_, 2);
v___x_3708_ = lean_apply_2(v_inst_3697_, lean_box(0), v___x_3707_);
v___f_3709_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3709_, 0, v_toPure_3705_);
v___f_3710_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3710_, 0, v_inst_3697_);
lean_closure_set(v___f_3710_, 1, v_toBind_3704_);
lean_closure_set(v___f_3710_, 2, v___f_3709_);
lean_closure_set(v___f_3710_, 3, v_toPure_3705_);
v___f_3711_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3711_, 0, v_toPure_3705_);
v___f_3712_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3712_, 0, v_toPure_3705_);
lean_closure_set(v___f_3712_, 1, v_inst_3697_);
lean_closure_set(v___f_3712_, 2, v_toBind_3704_);
lean_closure_set(v___f_3712_, 3, v_inst_3699_);
lean_closure_set(v___f_3712_, 4, v_inst_3700_);
lean_closure_set(v___f_3712_, 5, v_inst_3696_);
lean_closure_set(v___f_3712_, 6, v_toMonadRef_3706_);
lean_closure_set(v___f_3712_, 7, v_inst_3701_);
lean_closure_set(v___f_3712_, 8, v_f_3702_);
lean_closure_set(v___f_3712_, 9, v___f_3711_);
lean_closure_set(v___f_3712_, 10, v___f_3710_);
v___x_3713_ = lean_apply_4(v_toBind_3704_, lean_box(0), lean_box(0), v___x_3708_, v___f_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3714_, lean_object* v_inst_3715_, lean_object* v_inst_3716_, lean_object* v_inst_3717_, lean_object* v_inst_3718_, lean_object* v_inst_3719_, lean_object* v_inst_3720_, lean_object* v_inst_3721_, lean_object* v_inst_3722_, lean_object* v_f_3723_){
_start:
{
lean_object* v_toApplicative_3724_; lean_object* v_toBind_3725_; lean_object* v_toPure_3726_; lean_object* v_toMonadRef_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___f_3730_; lean_object* v___f_3731_; lean_object* v___f_3732_; lean_object* v___f_3733_; lean_object* v___x_3734_; 
v_toApplicative_3724_ = lean_ctor_get(v_inst_3715_, 0);
v_toBind_3725_ = lean_ctor_get(v_inst_3715_, 1);
lean_inc_n(v_toBind_3725_, 3);
v_toPure_3726_ = lean_ctor_get(v_toApplicative_3724_, 1);
lean_inc_n(v_toPure_3726_, 4);
v_toMonadRef_3727_ = lean_ctor_get(v_inst_3717_, 1);
lean_inc_ref(v_toMonadRef_3727_);
lean_dec_ref(v_inst_3717_);
v___x_3728_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3716_, 2);
v___x_3729_ = lean_apply_2(v_inst_3716_, lean_box(0), v___x_3728_);
v___f_3730_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3730_, 0, v_toPure_3726_);
v___f_3731_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3731_, 0, v_inst_3716_);
lean_closure_set(v___f_3731_, 1, v_toBind_3725_);
lean_closure_set(v___f_3731_, 2, v___f_3730_);
lean_closure_set(v___f_3731_, 3, v_toPure_3726_);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3732_, 0, v_toPure_3726_);
v___f_3733_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3733_, 0, v_toPure_3726_);
lean_closure_set(v___f_3733_, 1, v_inst_3716_);
lean_closure_set(v___f_3733_, 2, v_toBind_3725_);
lean_closure_set(v___f_3733_, 3, v_inst_3719_);
lean_closure_set(v___f_3733_, 4, v_inst_3720_);
lean_closure_set(v___f_3733_, 5, v_inst_3715_);
lean_closure_set(v___f_3733_, 6, v_toMonadRef_3727_);
lean_closure_set(v___f_3733_, 7, v_inst_3721_);
lean_closure_set(v___f_3733_, 8, v_f_3723_);
lean_closure_set(v___f_3733_, 9, v___f_3732_);
lean_closure_set(v___f_3733_, 10, v___f_3731_);
v___x_3734_ = lean_apply_4(v_toBind_3725_, lean_box(0), lean_box(0), v___x_3729_, v___f_3733_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3735_, lean_object* v_inst_3736_, lean_object* v_inst_3737_, lean_object* v_inst_3738_, lean_object* v_inst_3739_, lean_object* v_inst_3740_, lean_object* v_inst_3741_, lean_object* v_inst_3742_, lean_object* v_inst_3743_, lean_object* v_f_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3735_, v_inst_3736_, v_inst_3737_, v_inst_3738_, v_inst_3739_, v_inst_3740_, v_inst_3741_, v_inst_3742_, v_inst_3743_, v_f_3744_);
lean_dec_ref(v_inst_3743_);
lean_dec_ref(v_inst_3739_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3746_, lean_object* v_snd_3747_, lean_object* v___x_3748_, lean_object* v_toPure_3749_, lean_object* v_inst_3750_, lean_object* v_toBind_3751_, lean_object* v_inst_3752_, lean_object* v_inst_3753_, lean_object* v_toMonadRef_3754_, lean_object* v_inst_3755_, lean_object* v_inst_3756_, lean_object* v___f_3757_, lean_object* v_newHyp_3758_){
_start:
{
lean_object* v_type_3759_; lean_object* v_value_3760_; uint8_t v___x_3761_; 
v_type_3759_ = lean_ctor_get(v_newHyp_3758_, 1);
v_value_3760_ = lean_ctor_get(v_newHyp_3758_, 2);
lean_inc_ref(v_type_3759_);
v___x_3761_ = l_Lean_Expr_isFalse(v_type_3759_);
if (v___x_3761_ == 0)
{
lean_object* v_type_3762_; lean_object* v___f_3763_; lean_object* v___f_3764_; lean_object* v___f_3765_; lean_object* v___f_3766_; uint8_t v___x_3774_; 
lean_dec(v___f_3757_);
v_type_3762_ = lean_ctor_get(v___x_3746_, 1);
lean_inc(v_toPure_3749_);
lean_inc(v___x_3748_);
lean_inc_ref(v_newHyp_3758_);
lean_inc(v_snd_3747_);
v___f_3763_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3763_, 0, v_snd_3747_);
lean_closure_set(v___f_3763_, 1, v_newHyp_3758_);
lean_closure_set(v___f_3763_, 2, v___x_3748_);
lean_closure_set(v___f_3763_, 3, v_toPure_3749_);
v___f_3764_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3764_, 0, v___f_3763_);
lean_inc(v_toBind_3751_);
v___f_3765_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3765_, 0, v_inst_3750_);
lean_closure_set(v___f_3765_, 1, v_toBind_3751_);
lean_closure_set(v___f_3765_, 2, v___f_3764_);
lean_inc_ref(v___f_3765_);
v___f_3766_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3766_, 0, v___f_3765_);
v___x_3774_ = lean_expr_eqv(v_type_3762_, v_type_3759_);
if (v___x_3774_ == 0)
{
lean_inc_ref(v_type_3759_);
lean_dec_ref(v_newHyp_3758_);
lean_dec(v___x_3748_);
lean_dec(v_snd_3747_);
goto v___jp_3767_;
}
else
{
if (v___x_3761_ == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_dec_ref(v___f_3766_);
lean_dec_ref(v___f_3765_);
lean_dec_ref(v_inst_3756_);
lean_dec(v_inst_3755_);
lean_dec_ref(v_toMonadRef_3754_);
lean_dec_ref(v_inst_3753_);
lean_dec_ref(v_inst_3752_);
lean_dec(v_toBind_3751_);
lean_dec_ref(v___x_3746_);
v___x_3775_ = lean_box(0);
v___x_3776_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3747_, v_newHyp_3758_, v___x_3748_, v_toPure_3749_, v___x_3775_);
return v___x_3776_;
}
else
{
lean_inc_ref(v_type_3759_);
lean_dec_ref(v_newHyp_3758_);
lean_dec(v___x_3748_);
lean_dec(v_snd_3747_);
goto v___jp_3767_;
}
}
v___jp_3767_:
{
lean_object* v_getInheritedTraceOptions_3768_; lean_object* v___x_3769_; lean_object* v___f_3770_; lean_object* v___f_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v_getInheritedTraceOptions_3768_ = lean_ctor_get(v_inst_3752_, 2);
lean_inc(v_getInheritedTraceOptions_3768_);
v___x_3769_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3751_, 3);
v___f_3770_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3770_, 0, v___f_3765_);
lean_closure_set(v___f_3770_, 1, v___x_3746_);
lean_closure_set(v___f_3770_, 2, v_type_3759_);
lean_closure_set(v___f_3770_, 3, v_inst_3753_);
lean_closure_set(v___f_3770_, 4, v_inst_3752_);
lean_closure_set(v___f_3770_, 5, v_toMonadRef_3754_);
lean_closure_set(v___f_3770_, 6, v_inst_3755_);
lean_closure_set(v___f_3770_, 7, v___x_3769_);
lean_closure_set(v___f_3770_, 8, v_toBind_3751_);
lean_closure_set(v___f_3770_, 9, v___f_3766_);
v___f_3771_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3771_, 0, v_inst_3756_);
lean_closure_set(v___f_3771_, 1, v_toPure_3749_);
lean_closure_set(v___f_3771_, 2, v___x_3769_);
lean_closure_set(v___f_3771_, 3, v_toBind_3751_);
v___x_3772_ = lean_apply_4(v_toBind_3751_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3768_, v___f_3771_);
v___x_3773_ = lean_apply_4(v_toBind_3751_, lean_box(0), lean_box(0), v___x_3772_, v___f_3770_);
return v___x_3773_;
}
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_inc_ref(v_value_3760_);
lean_dec_ref(v_newHyp_3758_);
lean_dec_ref(v_inst_3756_);
lean_dec(v_inst_3755_);
lean_dec_ref(v_toMonadRef_3754_);
lean_dec_ref(v_inst_3753_);
lean_dec_ref(v_inst_3752_);
lean_dec(v_toPure_3749_);
lean_dec(v___x_3748_);
lean_dec(v_snd_3747_);
lean_dec_ref(v___x_3746_);
v___x_3777_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3777_, 0, v_value_3760_);
v___x_3778_ = lean_apply_2(v_inst_3750_, lean_box(0), v___x_3777_);
v___x_3779_ = lean_apply_4(v_toBind_3751_, lean_box(0), lean_box(0), v___x_3778_, v___f_3757_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3780_, lean_object* v_toPure_3781_, lean_object* v_hyps_3782_, lean_object* v___x_3783_, lean_object* v_inst_3784_, lean_object* v_toBind_3785_, lean_object* v_inst_3786_, lean_object* v_inst_3787_, lean_object* v_toMonadRef_3788_, lean_object* v_inst_3789_, lean_object* v_inst_3790_, lean_object* v_f_3791_, lean_object* v___f_3792_, lean_object* v_next_3793_, lean_object* v_acc_3794_, lean_object* v_h_3795_, lean_object* v_G_3796_){
_start:
{
uint8_t v___x_3797_; 
v___x_3797_ = lean_nat_dec_lt(v_next_3793_, v___x_3780_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; 
lean_dec(v_G_3796_);
lean_dec(v_next_3793_);
lean_dec(v___f_3792_);
lean_dec(v_f_3791_);
lean_dec_ref(v_inst_3790_);
lean_dec(v_inst_3789_);
lean_dec_ref(v_toMonadRef_3788_);
lean_dec_ref(v_inst_3787_);
lean_dec_ref(v_inst_3786_);
lean_dec(v_toBind_3785_);
lean_dec(v_inst_3784_);
lean_dec(v___x_3783_);
v___x_3798_ = lean_apply_2(v_toPure_3781_, lean_box(0), v_acc_3794_);
return v___x_3798_;
}
else
{
lean_object* v_snd_3799_; lean_object* v___f_3800_; lean_object* v___x_3801_; lean_object* v___f_3802_; lean_object* v___x_3803_; lean_object* v___f_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v_snd_3799_ = lean_ctor_get(v_acc_3794_, 1);
lean_inc_n(v_snd_3799_, 2);
lean_dec_ref(v_acc_3794_);
lean_inc(v_next_3793_);
lean_inc_n(v_toPure_3781_, 2);
v___f_3800_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3800_, 0, v_toPure_3781_);
lean_closure_set(v___f_3800_, 1, v_next_3793_);
lean_closure_set(v___f_3800_, 2, v_G_3796_);
v___x_3801_ = lean_box(v___x_3797_);
v___f_3802_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3802_, 0, v___x_3801_);
lean_closure_set(v___f_3802_, 1, v_snd_3799_);
lean_closure_set(v___f_3802_, 2, v_toPure_3781_);
v___x_3803_ = lean_array_fget_borrowed(v_hyps_3782_, v_next_3793_);
lean_dec(v_next_3793_);
lean_inc_n(v_toBind_3785_, 3);
lean_inc_n(v___x_3803_, 2);
v___f_3804_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3804_, 0, v___x_3803_);
lean_closure_set(v___f_3804_, 1, v_snd_3799_);
lean_closure_set(v___f_3804_, 2, v___x_3783_);
lean_closure_set(v___f_3804_, 3, v_toPure_3781_);
lean_closure_set(v___f_3804_, 4, v_inst_3784_);
lean_closure_set(v___f_3804_, 5, v_toBind_3785_);
lean_closure_set(v___f_3804_, 6, v_inst_3786_);
lean_closure_set(v___f_3804_, 7, v_inst_3787_);
lean_closure_set(v___f_3804_, 8, v_toMonadRef_3788_);
lean_closure_set(v___f_3804_, 9, v_inst_3789_);
lean_closure_set(v___f_3804_, 10, v_inst_3790_);
lean_closure_set(v___f_3804_, 11, v___f_3802_);
v___x_3805_ = lean_apply_1(v_f_3791_, v___x_3803_);
v___x_3806_ = lean_apply_4(v_toBind_3785_, lean_box(0), lean_box(0), v___x_3805_, v___f_3804_);
v___x_3807_ = lean_apply_4(v_toBind_3785_, lean_box(0), lean_box(0), v___x_3806_, v___f_3792_);
v___x_3808_ = lean_apply_4(v_toBind_3785_, lean_box(0), lean_box(0), v___x_3807_, v___f_3800_);
return v___x_3808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3809_ = _args[0];
lean_object* v_toPure_3810_ = _args[1];
lean_object* v_hyps_3811_ = _args[2];
lean_object* v___x_3812_ = _args[3];
lean_object* v_inst_3813_ = _args[4];
lean_object* v_toBind_3814_ = _args[5];
lean_object* v_inst_3815_ = _args[6];
lean_object* v_inst_3816_ = _args[7];
lean_object* v_toMonadRef_3817_ = _args[8];
lean_object* v_inst_3818_ = _args[9];
lean_object* v_inst_3819_ = _args[10];
lean_object* v_f_3820_ = _args[11];
lean_object* v___f_3821_ = _args[12];
lean_object* v_next_3822_ = _args[13];
lean_object* v_acc_3823_ = _args[14];
lean_object* v_h_3824_ = _args[15];
lean_object* v_G_3825_ = _args[16];
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3809_, v_toPure_3810_, v_hyps_3811_, v___x_3812_, v_inst_3813_, v_toBind_3814_, v_inst_3815_, v_inst_3816_, v_toMonadRef_3817_, v_inst_3818_, v_inst_3819_, v_f_3820_, v___f_3821_, v_next_3822_, v_acc_3823_, v_h_3824_, v_G_3825_);
lean_dec_ref(v_hyps_3811_);
lean_dec(v___x_3809_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3827_, lean_object* v_inst_3828_, lean_object* v_toBind_3829_, lean_object* v_inst_3830_, lean_object* v_inst_3831_, lean_object* v_toMonadRef_3832_, lean_object* v_inst_3833_, lean_object* v_inst_3834_, lean_object* v_f_3835_, lean_object* v___f_3836_, lean_object* v___f_3837_, lean_object* v_hyps_3838_){
_start:
{
lean_object* v___x_3839_; lean_object* v_newHyps_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___f_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3839_ = lean_array_get_size(v_hyps_3838_);
v_newHyps_3840_ = lean_mk_empty_array_with_capacity(v___x_3839_);
v___x_3841_ = lean_unsigned_to_nat(0u);
v___x_3842_ = lean_box(0);
lean_inc(v_toBind_3829_);
v___f_3843_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3843_, 0, v___x_3839_);
lean_closure_set(v___f_3843_, 1, v_toPure_3827_);
lean_closure_set(v___f_3843_, 2, v_hyps_3838_);
lean_closure_set(v___f_3843_, 3, v___x_3842_);
lean_closure_set(v___f_3843_, 4, v_inst_3828_);
lean_closure_set(v___f_3843_, 5, v_toBind_3829_);
lean_closure_set(v___f_3843_, 6, v_inst_3830_);
lean_closure_set(v___f_3843_, 7, v_inst_3831_);
lean_closure_set(v___f_3843_, 8, v_toMonadRef_3832_);
lean_closure_set(v___f_3843_, 9, v_inst_3833_);
lean_closure_set(v___f_3843_, 10, v_inst_3834_);
lean_closure_set(v___f_3843_, 11, v_f_3835_);
lean_closure_set(v___f_3843_, 12, v___f_3836_);
v___x_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v_newHyps_3840_);
v___x_3845_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3843_, v___x_3841_, v___x_3844_, lean_box(0));
v___x_3846_ = lean_apply_4(v_toBind_3829_, lean_box(0), lean_box(0), v___x_3845_, v___f_3837_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3847_, lean_object* v_inst_3848_, lean_object* v_inst_3849_, lean_object* v_inst_3850_, lean_object* v_inst_3851_, lean_object* v_inst_3852_, lean_object* v_f_3853_){
_start:
{
lean_object* v_toApplicative_3854_; lean_object* v_toBind_3855_; lean_object* v_toPure_3856_; lean_object* v_toMonadRef_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___f_3860_; lean_object* v___f_3861_; lean_object* v___f_3862_; lean_object* v___f_3863_; lean_object* v___x_3864_; 
v_toApplicative_3854_ = lean_ctor_get(v_inst_3847_, 0);
v_toBind_3855_ = lean_ctor_get(v_inst_3847_, 1);
lean_inc_n(v_toBind_3855_, 3);
v_toPure_3856_ = lean_ctor_get(v_toApplicative_3854_, 1);
lean_inc_n(v_toPure_3856_, 4);
v_toMonadRef_3857_ = lean_ctor_get(v_inst_3849_, 1);
lean_inc_ref(v_toMonadRef_3857_);
lean_dec_ref(v_inst_3849_);
v___x_3858_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3848_, 2);
v___x_3859_ = lean_apply_2(v_inst_3848_, lean_box(0), v___x_3858_);
v___f_3860_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3860_, 0, v_toPure_3856_);
v___f_3861_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3861_, 0, v_inst_3848_);
lean_closure_set(v___f_3861_, 1, v_toBind_3855_);
lean_closure_set(v___f_3861_, 2, v___f_3860_);
lean_closure_set(v___f_3861_, 3, v_toPure_3856_);
v___f_3862_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3862_, 0, v_toPure_3856_);
v___f_3863_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3863_, 0, v_toPure_3856_);
lean_closure_set(v___f_3863_, 1, v_inst_3848_);
lean_closure_set(v___f_3863_, 2, v_toBind_3855_);
lean_closure_set(v___f_3863_, 3, v_inst_3850_);
lean_closure_set(v___f_3863_, 4, v_inst_3847_);
lean_closure_set(v___f_3863_, 5, v_toMonadRef_3857_);
lean_closure_set(v___f_3863_, 6, v_inst_3852_);
lean_closure_set(v___f_3863_, 7, v_inst_3851_);
lean_closure_set(v___f_3863_, 8, v_f_3853_);
lean_closure_set(v___f_3863_, 9, v___f_3862_);
lean_closure_set(v___f_3863_, 10, v___f_3861_);
v___x_3864_ = lean_apply_4(v_toBind_3855_, lean_box(0), lean_box(0), v___x_3859_, v___f_3863_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3865_, lean_object* v_inst_3866_, lean_object* v_inst_3867_, lean_object* v_inst_3868_, lean_object* v_inst_3869_, lean_object* v_inst_3870_, lean_object* v_inst_3871_, lean_object* v_inst_3872_, lean_object* v_inst_3873_, lean_object* v_f_3874_){
_start:
{
lean_object* v_toApplicative_3875_; lean_object* v_toBind_3876_; lean_object* v_toPure_3877_; lean_object* v_toMonadRef_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___f_3881_; lean_object* v___f_3882_; lean_object* v___f_3883_; lean_object* v___f_3884_; lean_object* v___x_3885_; 
v_toApplicative_3875_ = lean_ctor_get(v_inst_3866_, 0);
v_toBind_3876_ = lean_ctor_get(v_inst_3866_, 1);
lean_inc_n(v_toBind_3876_, 3);
v_toPure_3877_ = lean_ctor_get(v_toApplicative_3875_, 1);
lean_inc_n(v_toPure_3877_, 4);
v_toMonadRef_3878_ = lean_ctor_get(v_inst_3868_, 1);
lean_inc_ref(v_toMonadRef_3878_);
lean_dec_ref(v_inst_3868_);
v___x_3879_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3867_, 2);
v___x_3880_ = lean_apply_2(v_inst_3867_, lean_box(0), v___x_3879_);
v___f_3881_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3881_, 0, v_toPure_3877_);
v___f_3882_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3882_, 0, v_inst_3867_);
lean_closure_set(v___f_3882_, 1, v_toBind_3876_);
lean_closure_set(v___f_3882_, 2, v___f_3881_);
lean_closure_set(v___f_3882_, 3, v_toPure_3877_);
v___f_3883_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3883_, 0, v_toPure_3877_);
v___f_3884_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3884_, 0, v_toPure_3877_);
lean_closure_set(v___f_3884_, 1, v_inst_3867_);
lean_closure_set(v___f_3884_, 2, v_toBind_3876_);
lean_closure_set(v___f_3884_, 3, v_inst_3870_);
lean_closure_set(v___f_3884_, 4, v_inst_3866_);
lean_closure_set(v___f_3884_, 5, v_toMonadRef_3878_);
lean_closure_set(v___f_3884_, 6, v_inst_3872_);
lean_closure_set(v___f_3884_, 7, v_inst_3871_);
lean_closure_set(v___f_3884_, 8, v_f_3874_);
lean_closure_set(v___f_3884_, 9, v___f_3883_);
lean_closure_set(v___f_3884_, 10, v___f_3882_);
v___x_3885_ = lean_apply_4(v_toBind_3876_, lean_box(0), lean_box(0), v___x_3880_, v___f_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3886_, lean_object* v_inst_3887_, lean_object* v_inst_3888_, lean_object* v_inst_3889_, lean_object* v_inst_3890_, lean_object* v_inst_3891_, lean_object* v_inst_3892_, lean_object* v_inst_3893_, lean_object* v_inst_3894_, lean_object* v_f_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3886_, v_inst_3887_, v_inst_3888_, v_inst_3889_, v_inst_3890_, v_inst_3891_, v_inst_3892_, v_inst_3893_, v_inst_3894_, v_f_3895_);
lean_dec_ref(v_inst_3894_);
lean_dec_ref(v_inst_3890_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3897_, lean_object* v_x_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_apply_1(v_f_3897_, v___y_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3901_, lean_object* v_inst_3902_, lean_object* v___f_3903_, lean_object* v_hyps_3904_){
_start:
{
lean_object* v_toPure_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_toPure_3905_ = lean_ctor_get(v_toApplicative_3901_, 1);
lean_inc(v_toPure_3905_);
lean_dec_ref(v_toApplicative_3901_);
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = lean_array_get_size(v_hyps_3904_);
v___x_3908_ = lean_box(0);
v___x_3909_ = lean_nat_dec_lt(v___x_3906_, v___x_3907_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_dec_ref(v_hyps_3904_);
lean_dec(v___f_3903_);
lean_dec_ref(v_inst_3902_);
v___x_3910_ = lean_apply_2(v_toPure_3905_, lean_box(0), v___x_3908_);
return v___x_3910_;
}
else
{
uint8_t v___x_3911_; 
v___x_3911_ = lean_nat_dec_le(v___x_3907_, v___x_3907_);
if (v___x_3911_ == 0)
{
if (v___x_3909_ == 0)
{
lean_object* v___x_3912_; 
lean_dec_ref(v_hyps_3904_);
lean_dec(v___f_3903_);
lean_dec_ref(v_inst_3902_);
v___x_3912_ = lean_apply_2(v_toPure_3905_, lean_box(0), v___x_3908_);
return v___x_3912_;
}
else
{
size_t v___x_3913_; size_t v___x_3914_; lean_object* v___x_3915_; 
lean_dec(v_toPure_3905_);
v___x_3913_ = ((size_t)0ULL);
v___x_3914_ = lean_usize_of_nat(v___x_3907_);
v___x_3915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3902_, v___f_3903_, v_hyps_3904_, v___x_3913_, v___x_3914_, v___x_3908_);
return v___x_3915_;
}
}
else
{
size_t v___x_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
lean_dec(v_toPure_3905_);
v___x_3916_ = ((size_t)0ULL);
v___x_3917_ = lean_usize_of_nat(v___x_3907_);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3902_, v___f_3903_, v_hyps_3904_, v___x_3916_, v___x_3917_, v___x_3908_);
return v___x_3918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3919_, lean_object* v_inst_3920_, lean_object* v_f_3921_){
_start:
{
lean_object* v_toApplicative_3922_; lean_object* v_toBind_3923_; lean_object* v___f_3924_; lean_object* v___f_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_toApplicative_3922_ = lean_ctor_get(v_inst_3919_, 0);
lean_inc_ref(v_toApplicative_3922_);
v_toBind_3923_ = lean_ctor_get(v_inst_3919_, 1);
lean_inc(v_toBind_3923_);
v___f_3924_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3924_, 0, v_f_3921_);
v___f_3925_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3925_, 0, v_toApplicative_3922_);
lean_closure_set(v___f_3925_, 1, v_inst_3919_);
lean_closure_set(v___f_3925_, 2, v___f_3924_);
v___x_3926_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3927_ = lean_apply_2(v_inst_3920_, lean_box(0), v___x_3926_);
v___x_3928_ = lean_apply_4(v_toBind_3923_, lean_box(0), lean_box(0), v___x_3927_, v___f_3925_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3929_, lean_object* v_inst_3930_, lean_object* v_inst_3931_, lean_object* v_inst_3932_, lean_object* v_f_3933_){
_start:
{
lean_object* v_toApplicative_3934_; lean_object* v_toBind_3935_; lean_object* v___f_3936_; lean_object* v___f_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v_toApplicative_3934_ = lean_ctor_get(v_inst_3930_, 0);
lean_inc_ref(v_toApplicative_3934_);
v_toBind_3935_ = lean_ctor_get(v_inst_3930_, 1);
lean_inc(v_toBind_3935_);
v___f_3936_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3936_, 0, v_f_3933_);
v___f_3937_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3937_, 0, v_toApplicative_3934_);
lean_closure_set(v___f_3937_, 1, v_inst_3930_);
lean_closure_set(v___f_3937_, 2, v___f_3936_);
v___x_3938_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3939_ = lean_apply_2(v_inst_3931_, lean_box(0), v___x_3938_);
v___x_3940_ = lean_apply_4(v_toBind_3935_, lean_box(0), lean_box(0), v___x_3939_, v___f_3937_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3941_, lean_object* v_inst_3942_, lean_object* v_inst_3943_, lean_object* v_inst_3944_, lean_object* v_f_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3941_, v_inst_3942_, v_inst_3943_, v_inst_3944_, v_f_3945_);
lean_dec_ref(v_inst_3944_);
return v_res_3946_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_3949_, lean_object* v_methods_3950_, lean_object* v_config_3951_, lean_object* v_hyp_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v___x_3961_; lean_object* v_caches_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v_typeAnalysis_3969_; lean_object* v_target_3970_; lean_object* v_hypotheses_3971_; uint8_t v_didChange_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4013_; 
v___x_3961_ = lean_st_ref_get(v_a_3953_);
v_caches_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc_ref(v_caches_3962_);
lean_dec(v___x_3961_);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_3949_, v_caches_3962_);
v___x_3965_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_3966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3963_);
lean_ctor_set(v___x_3966_, 1, v___x_3964_);
lean_ctor_set(v___x_3966_, 2, v___x_3965_);
lean_ctor_set(v___x_3966_, 3, v___x_3965_);
v___x_3967_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3949_, v___x_3965_, v_caches_3962_);
v___x_3968_ = lean_st_ref_take(v_a_3953_);
v_typeAnalysis_3969_ = lean_ctor_get(v___x_3968_, 1);
v_target_3970_ = lean_ctor_get(v___x_3968_, 2);
v_hypotheses_3971_ = lean_ctor_get(v___x_3968_, 3);
v_didChange_3972_ = lean_ctor_get_uint8(v___x_3968_, sizeof(void*)*4);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; 
v_unused_4014_ = lean_ctor_get(v___x_3968_, 0);
lean_dec(v_unused_4014_);
v___x_3974_ = v___x_3968_;
v_isShared_3975_ = v_isSharedCheck_4013_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_hypotheses_3971_);
lean_inc(v_target_3970_);
lean_inc(v_typeAnalysis_3969_);
lean_dec(v___x_3968_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4013_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3967_);
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_3967_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_typeAnalysis_3969_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_target_3970_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_hypotheses_3971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4012_, sizeof(void*)*4, v_didChange_3972_);
v___x_3977_ = v_reuseFailAlloc_4012_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3978_; lean_object* v_type_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3978_ = lean_st_ref_put(v_a_3953_, v___x_3977_);
v_type_3979_ = lean_ctor_get(v_hyp_3952_, 1);
lean_inc_ref(v_type_3979_);
v___x_3980_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3980_, 0, v_type_3979_);
v___x_3981_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3980_, v_methods_3950_, v_config_3951_, v___x_3966_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v_fst_3983_; lean_object* v_snd_3984_; lean_object* v___x_3985_; lean_object* v_caches_3986_; lean_object* v_persistentCache_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v_typeAnalysis_3990_; lean_object* v_target_3991_; lean_object* v_hypotheses_3992_; uint8_t v_didChange_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4002_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v_fst_3983_ = lean_ctor_get(v_a_3982_, 0);
lean_inc(v_fst_3983_);
v_snd_3984_ = lean_ctor_get(v_a_3982_, 1);
lean_inc(v_snd_3984_);
lean_dec(v_a_3982_);
v___x_3985_ = lean_st_ref_get(v_a_3953_);
v_caches_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc_ref(v_caches_3986_);
lean_dec(v___x_3985_);
v_persistentCache_3987_ = lean_ctor_get(v_snd_3984_, 1);
lean_inc_ref(v_persistentCache_3987_);
lean_dec(v_snd_3984_);
v___x_3988_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3949_, v_persistentCache_3987_, v_caches_3986_);
v___x_3989_ = lean_st_ref_take(v_a_3953_);
v_typeAnalysis_3990_ = lean_ctor_get(v___x_3989_, 1);
v_target_3991_ = lean_ctor_get(v___x_3989_, 2);
v_hypotheses_3992_ = lean_ctor_get(v___x_3989_, 3);
v_didChange_3993_ = lean_ctor_get_uint8(v___x_3989_, sizeof(void*)*4);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; 
v_unused_4003_ = lean_ctor_get(v___x_3989_, 0);
lean_dec(v_unused_4003_);
v___x_3995_ = v___x_3989_;
v_isShared_3996_ = v_isSharedCheck_4002_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_hypotheses_3992_);
lean_inc(v_target_3991_);
lean_inc(v_typeAnalysis_3990_);
lean_dec(v___x_3989_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4002_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v___x_3988_);
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3988_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_typeAnalysis_3990_);
lean_ctor_set(v_reuseFailAlloc_4001_, 2, v_target_3991_);
lean_ctor_set(v_reuseFailAlloc_4001_, 3, v_hypotheses_3992_);
lean_ctor_set_uint8(v_reuseFailAlloc_4001_, sizeof(void*)*4, v_didChange_3993_);
v___x_3998_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_st_ref_put(v_a_3953_, v___x_3998_);
v___x_4000_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_3952_, v_fst_3983_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
return v___x_4000_;
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v_hyp_3952_);
v_a_4004_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3981_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3981_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_4015_, lean_object* v_methods_4016_, lean_object* v_config_4017_, lean_object* v_hyp_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
uint8_t v_cacheId_boxed_4027_; lean_object* v_res_4028_; 
v_cacheId_boxed_4027_ = lean_unbox(v_cacheId_4015_);
v_res_4028_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_4027_, v_methods_4016_, v_config_4017_, v_hyp_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_4029_, lean_object* v_methods_4030_, lean_object* v_config_4031_, lean_object* v_hyp_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4029_, v_methods_4030_, v_config_4031_, v_hyp_4032_, v_a_4034_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4046_, lean_object* v_methods_4047_, lean_object* v_config_4048_, lean_object* v_hyp_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
uint8_t v_cacheId_boxed_4062_; lean_object* v_res_4063_; 
v_cacheId_boxed_4062_ = lean_unbox(v_cacheId_4046_);
v_res_4063_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4062_, v_methods_4047_, v_config_4048_, v_hyp_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4064_, lean_object* v_methods_4065_, lean_object* v_config_4066_, lean_object* v_hyp_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v___x_4076_; lean_object* v_caches_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v_typeAnalysis_4084_; lean_object* v_target_4085_; lean_object* v_hypotheses_4086_; uint8_t v_didChange_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4128_; 
v___x_4076_ = lean_st_ref_get(v_a_4068_);
v_caches_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc_ref(v_caches_4077_);
lean_dec(v___x_4076_);
v___x_4078_ = lean_unsigned_to_nat(0u);
v___x_4079_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4064_, v_caches_4077_);
v___x_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4078_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4082_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4064_, v___x_4081_, v_caches_4077_);
v___x_4083_ = lean_st_ref_take(v_a_4068_);
v_typeAnalysis_4084_ = lean_ctor_get(v___x_4083_, 1);
v_target_4085_ = lean_ctor_get(v___x_4083_, 2);
v_hypotheses_4086_ = lean_ctor_get(v___x_4083_, 3);
v_didChange_4087_ = lean_ctor_get_uint8(v___x_4083_, sizeof(void*)*4);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; 
v_unused_4129_ = lean_ctor_get(v___x_4083_, 0);
lean_dec(v_unused_4129_);
v___x_4089_ = v___x_4083_;
v_isShared_4090_ = v_isSharedCheck_4128_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_hypotheses_4086_);
lean_inc(v_target_4085_);
lean_inc(v_typeAnalysis_4084_);
lean_dec(v___x_4083_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4128_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4082_);
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4082_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_typeAnalysis_4084_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_target_4085_);
lean_ctor_set(v_reuseFailAlloc_4127_, 3, v_hypotheses_4086_);
lean_ctor_set_uint8(v_reuseFailAlloc_4127_, sizeof(void*)*4, v_didChange_4087_);
v___x_4092_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
lean_object* v___x_4093_; lean_object* v_type_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4093_ = lean_st_ref_put(v_a_4068_, v___x_4092_);
v_type_4094_ = lean_ctor_get(v_hyp_4067_, 1);
lean_inc_ref(v_type_4094_);
v___x_4095_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4095_, 0, v_type_4094_);
v___x_4096_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4095_, v_methods_4065_, v_config_4066_, v___x_4080_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v_fst_4098_; lean_object* v_snd_4099_; lean_object* v___x_4100_; lean_object* v_caches_4101_; lean_object* v_cache_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v_typeAnalysis_4105_; lean_object* v_target_4106_; lean_object* v_hypotheses_4107_; uint8_t v_didChange_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4117_; 
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4096_, 1);
v_fst_4098_ = lean_ctor_get(v_a_4097_, 0);
lean_inc(v_fst_4098_);
v_snd_4099_ = lean_ctor_get(v_a_4097_, 1);
lean_inc(v_snd_4099_);
lean_dec(v_a_4097_);
v___x_4100_ = lean_st_ref_get(v_a_4068_);
v_caches_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc_ref(v_caches_4101_);
lean_dec(v___x_4100_);
v_cache_4102_ = lean_ctor_get(v_snd_4099_, 1);
lean_inc_ref(v_cache_4102_);
lean_dec(v_snd_4099_);
v___x_4103_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4064_, v_cache_4102_, v_caches_4101_);
v___x_4104_ = lean_st_ref_take(v_a_4068_);
v_typeAnalysis_4105_ = lean_ctor_get(v___x_4104_, 1);
v_target_4106_ = lean_ctor_get(v___x_4104_, 2);
v_hypotheses_4107_ = lean_ctor_get(v___x_4104_, 3);
v_didChange_4108_ = lean_ctor_get_uint8(v___x_4104_, sizeof(void*)*4);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4117_ == 0)
{
lean_object* v_unused_4118_; 
v_unused_4118_ = lean_ctor_get(v___x_4104_, 0);
lean_dec(v_unused_4118_);
v___x_4110_ = v___x_4104_;
v_isShared_4111_ = v_isSharedCheck_4117_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_hypotheses_4107_);
lean_inc(v_target_4106_);
lean_inc(v_typeAnalysis_4105_);
lean_dec(v___x_4104_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4117_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v___x_4103_);
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4103_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_typeAnalysis_4105_);
lean_ctor_set(v_reuseFailAlloc_4116_, 2, v_target_4106_);
lean_ctor_set(v_reuseFailAlloc_4116_, 3, v_hypotheses_4107_);
lean_ctor_set_uint8(v_reuseFailAlloc_4116_, sizeof(void*)*4, v_didChange_4108_);
v___x_4113_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = lean_st_ref_put(v_a_4068_, v___x_4113_);
v___x_4115_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4067_, v_fst_4098_);
lean_dec(v_fst_4098_);
return v___x_4115_;
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec_ref(v_hyp_4067_);
v_a_4119_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4096_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4096_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4130_, lean_object* v_methods_4131_, lean_object* v_config_4132_, lean_object* v_hyp_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
uint8_t v_cacheId_boxed_4142_; lean_object* v_res_4143_; 
v_cacheId_boxed_4142_ = lean_unbox(v_cacheId_4130_);
v_res_4143_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4142_, v_methods_4131_, v_config_4132_, v_hyp_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4144_, lean_object* v_methods_4145_, lean_object* v_config_4146_, lean_object* v_hyp_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4144_, v_methods_4145_, v_config_4146_, v_hyp_4147_, v_a_4149_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4161_, lean_object* v_methods_4162_, lean_object* v_config_4163_, lean_object* v_hyp_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
uint8_t v_cacheId_boxed_4177_; lean_object* v_res_4178_; 
v_cacheId_boxed_4177_ = lean_unbox(v_cacheId_4161_);
v_res_4178_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4177_, v_methods_4162_, v_config_4163_, v_hyp_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4179_, lean_object* v_a_4180_, lean_object* v___x_4181_, lean_object* v_____r_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4195_ = lean_array_push(v_snd_4179_, v_a_4180_);
v___x_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4181_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
v___x_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4199_, lean_object* v_a_4200_, lean_object* v___x_4201_, lean_object* v_____r_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4199_, v_a_4200_, v___x_4201_, v_____r_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4216_, lean_object* v___f_4217_, lean_object* v_____r_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; lean_object* v_caches_4232_; lean_object* v_typeAnalysis_4233_; lean_object* v_target_4234_; lean_object* v_hypotheses_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4245_; 
v___x_4231_ = lean_st_ref_take(v___y_4220_);
v_caches_4232_ = lean_ctor_get(v___x_4231_, 0);
v_typeAnalysis_4233_ = lean_ctor_get(v___x_4231_, 1);
v_target_4234_ = lean_ctor_get(v___x_4231_, 2);
v_hypotheses_4235_ = lean_ctor_get(v___x_4231_, 3);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4237_ = v___x_4231_;
v_isShared_4238_ = v_isSharedCheck_4245_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_hypotheses_4235_);
lean_inc(v_target_4234_);
lean_inc(v_typeAnalysis_4233_);
lean_inc(v_caches_4232_);
lean_dec(v___x_4231_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4245_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4239_; lean_object* v___x_4241_; 
v___x_4239_ = lean_box(0);
if (v_isShared_4238_ == 0)
{
v___x_4241_ = v___x_4237_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_caches_4232_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_typeAnalysis_4233_);
lean_ctor_set(v_reuseFailAlloc_4244_, 2, v_target_4234_);
lean_ctor_set(v_reuseFailAlloc_4244_, 3, v_hypotheses_4235_);
v___x_4241_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
lean_ctor_set_uint8(v___x_4241_, sizeof(void*)*4, v___x_4216_);
v___x_4242_ = lean_st_ref_put(v___y_4220_, v___x_4241_);
lean_inc(v___y_4229_);
lean_inc_ref(v___y_4228_);
lean_inc(v___y_4227_);
lean_inc_ref(v___y_4226_);
lean_inc(v___y_4225_);
lean_inc_ref(v___y_4224_);
lean_inc(v___y_4223_);
lean_inc_ref(v___y_4222_);
lean_inc(v___y_4221_);
lean_inc(v___y_4220_);
lean_inc_ref(v___y_4219_);
v___x_4243_ = lean_apply_13(v___f_4217_, v___x_4239_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, lean_box(0));
return v___x_4243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4246_, lean_object* v___f_4247_, lean_object* v_____r_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
uint8_t v___x_22285__boxed_4261_; lean_object* v_res_4262_; 
v___x_22285__boxed_4261_ = lean_unbox(v___x_4246_);
v_res_4262_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22285__boxed_4261_, v___f_4247_, v_____r_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4263_, lean_object* v_hypotheses_4264_, uint8_t v_cacheId_4265_, lean_object* v_methods_4266_, lean_object* v_config_4267_, lean_object* v___x_4268_, lean_object* v___x_4269_, lean_object* v___x_4270_, lean_object* v_toMonadRef_4271_, lean_object* v___f_4272_, lean_object* v_next_4273_, lean_object* v_acc_4274_, lean_object* v_h_4275_, lean_object* v_G_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v___y_4290_; uint8_t v___x_4312_; 
v___x_4312_ = lean_nat_dec_lt(v_next_4273_, v___x_4263_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; 
lean_dec_ref(v_G_4276_);
lean_dec(v___f_4272_);
lean_dec_ref(v_toMonadRef_4271_);
lean_dec_ref(v___x_4270_);
lean_dec_ref(v___x_4269_);
lean_dec(v___x_4268_);
lean_dec_ref(v_config_4267_);
lean_dec_ref(v_methods_4266_);
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v_acc_4274_);
return v___x_4313_;
}
else
{
lean_object* v_snd_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4388_; 
v_snd_4314_ = lean_ctor_get(v_acc_4274_, 1);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_acc_4274_);
if (v_isSharedCheck_4388_ == 0)
{
lean_object* v_unused_4389_; 
v_unused_4389_ = lean_ctor_get(v_acc_4274_, 0);
lean_dec(v_unused_4389_);
v___x_4316_ = v_acc_4274_;
v_isShared_4317_ = v_isSharedCheck_4388_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_snd_4314_);
lean_dec(v_acc_4274_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4388_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_array_fget_borrowed(v_hypotheses_4264_, v_next_4273_);
lean_inc(v___x_4318_);
v___x_4319_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4265_, v_methods_4266_, v_config_4267_, v___x_4318_, v___y_4278_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v_type_4321_; lean_object* v_value_4322_; uint8_t v___x_4323_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
v_type_4321_ = lean_ctor_get(v_a_4320_, 1);
v_value_4322_ = lean_ctor_get(v_a_4320_, 2);
lean_inc_ref(v_type_4321_);
v___x_4323_ = l_Lean_Expr_isFalse(v_type_4321_);
if (v___x_4323_ == 0)
{
lean_object* v_type_4324_; lean_object* v___f_4325_; uint8_t v___x_4355_; 
lean_del_object(v___x_4316_);
v_type_4324_ = lean_ctor_get(v___x_4318_, 1);
lean_inc(v___x_4268_);
lean_inc(v_a_4320_);
lean_inc(v_snd_4314_);
v___f_4325_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4325_, 0, v_snd_4314_);
lean_closure_set(v___f_4325_, 1, v_a_4320_);
lean_closure_set(v___f_4325_, 2, v___x_4268_);
v___x_4355_ = lean_expr_eqv(v_type_4324_, v_type_4321_);
if (v___x_4355_ == 0)
{
lean_inc_ref(v_type_4321_);
lean_dec(v_a_4320_);
lean_dec(v_snd_4314_);
lean_dec(v___x_4268_);
goto v___jp_4329_;
}
else
{
if (v___x_4323_ == 0)
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
lean_dec_ref(v___f_4325_);
lean_dec(v___f_4272_);
lean_dec_ref(v_toMonadRef_4271_);
lean_dec_ref(v___x_4270_);
lean_dec_ref(v___x_4269_);
v___x_4356_ = lean_box(0);
v___x_4357_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4314_, v_a_4320_, v___x_4268_, v___x_4356_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
v___y_4290_ = v___x_4357_;
goto v___jp_4289_;
}
else
{
lean_inc_ref(v_type_4321_);
lean_dec(v_a_4320_);
lean_dec(v_snd_4314_);
lean_dec(v___x_4268_);
goto v___jp_4329_;
}
}
v___jp_4326_:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = lean_box(0);
v___x_4328_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4312_, v___f_4325_, v___x_4327_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
v___y_4290_ = v___x_4328_;
goto v___jp_4289_;
}
v___jp_4329_:
{
lean_object* v_toCold_4330_; lean_object* v_options_4331_; uint8_t v_hasTrace_4332_; 
v_toCold_4330_ = lean_ctor_get(v___y_4286_, 0);
v_options_4331_ = lean_ctor_get(v_toCold_4330_, 2);
v_hasTrace_4332_ = lean_ctor_get_uint8(v_options_4331_, sizeof(void*)*1);
if (v_hasTrace_4332_ == 0)
{
lean_dec_ref(v_type_4321_);
lean_dec(v___f_4272_);
lean_dec_ref(v_toMonadRef_4271_);
lean_dec_ref(v___x_4270_);
lean_dec_ref(v___x_4269_);
goto v___jp_4326_;
}
else
{
lean_object* v_inheritedTraceOptions_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; uint8_t v___x_4336_; 
v_inheritedTraceOptions_4333_ = lean_ctor_get(v_toCold_4330_, 11);
v___x_4334_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4335_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4336_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4333_, v_options_4331_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_dec_ref(v_type_4321_);
lean_dec(v___f_4272_);
lean_dec_ref(v_toMonadRef_4271_);
lean_dec_ref(v___x_4270_);
lean_dec_ref(v___x_4269_);
goto v___jp_4326_;
}
else
{
lean_object* v_type_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_22210__overap_4343_; lean_object* v___x_4344_; 
v_type_4337_ = lean_ctor_get(v___x_4318_, 1);
lean_inc_ref(v_type_4337_);
v___x_4338_ = l_Lean_MessageData_ofExpr(v_type_4337_);
v___x_4339_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = l_Lean_MessageData_ofExpr(v_type_4321_);
v___x_4342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4340_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
v___x_22210__overap_4343_ = l_Lean_addTrace___redArg(v___x_4269_, v___x_4270_, v_toMonadRef_4271_, v___f_4272_, v___x_4334_, v___x_4342_);
lean_inc(v___y_4287_);
lean_inc_ref(v___y_4286_);
lean_inc(v___y_4285_);
lean_inc_ref(v___y_4284_);
lean_inc(v___y_4283_);
lean_inc_ref(v___y_4282_);
lean_inc(v___y_4281_);
lean_inc_ref(v___y_4280_);
lean_inc(v___y_4279_);
lean_inc(v___y_4278_);
lean_inc_ref(v___y_4277_);
v___x_4344_ = lean_apply_12(v___x_22210__overap_4343_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, lean_box(0));
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4346_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
lean_dec_ref_known(v___x_4344_, 1);
v___x_4346_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4312_, v___f_4325_, v_a_4345_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
v___y_4290_ = v___x_4346_;
goto v___jp_4289_;
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec_ref(v___f_4325_);
lean_dec_ref(v_G_4276_);
v_a_4347_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4344_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4344_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4358_; 
lean_inc_ref(v_value_4322_);
lean_dec(v_a_4320_);
lean_dec_ref(v_G_4276_);
lean_dec(v___f_4272_);
lean_dec_ref(v_toMonadRef_4271_);
lean_dec_ref(v___x_4270_);
lean_dec_ref(v___x_4269_);
lean_dec(v___x_4268_);
v___x_4358_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4322_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4370_; 
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4370_ == 0)
{
lean_object* v_unused_4371_; 
v_unused_4371_ = lean_ctor_get(v___x_4358_, 0);
lean_dec(v_unused_4371_);
v___x_4360_ = v___x_4358_;
v_isShared_4361_ = v_isSharedCheck_4370_;
goto v_resetjp_4359_;
}
else
{
lean_dec(v___x_4358_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4370_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4365_; 
v___x_4362_ = lean_box(v___x_4312_);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 0, v___x_4363_);
v___x_4365_ = v___x_4316_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v_snd_4314_);
v___x_4365_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4367_; 
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4365_);
v___x_4367_ = v___x_4360_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4365_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_del_object(v___x_4316_);
lean_dec(v_snd_4314_);
v_a_4372_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4358_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4358_);
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
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_del_object(v___x_4316_);
lean_dec(v_snd_4314_);
lean_dec_ref(v_G_4276_);
lean_dec(v___f_4272_);
lean_dec_ref(v_toMonadRef_4271_);
lean_dec_ref(v___x_4270_);
lean_dec_ref(v___x_4269_);
lean_dec(v___x_4268_);
v_a_4380_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4319_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4319_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
v___jp_4289_:
{
if (lean_obj_tag(v___y_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4303_; 
v_a_4291_ = lean_ctor_get(v___y_4290_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___y_4290_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4293_ = v___y_4290_;
v_isShared_4294_ = v_isSharedCheck_4303_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___y_4290_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4303_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
if (lean_obj_tag(v_a_4291_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; 
lean_dec_ref(v_G_4276_);
v_a_4295_ = lean_ctor_get(v_a_4291_, 0);
lean_inc(v_a_4295_);
lean_dec_ref_known(v_a_4291_, 1);
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 0, v_a_4295_);
v___x_4297_ = v___x_4293_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
lean_del_object(v___x_4293_);
v_a_4299_ = lean_ctor_get(v_a_4291_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v_a_4291_, 1);
v___x_4300_ = lean_unsigned_to_nat(1u);
v___x_4301_ = lean_nat_add(v_next_4273_, v___x_4300_);
lean_inc(v___y_4287_);
lean_inc_ref(v___y_4286_);
lean_inc(v___y_4285_);
lean_inc_ref(v___y_4284_);
lean_inc(v___y_4283_);
lean_inc_ref(v___y_4282_);
lean_inc(v___y_4281_);
lean_inc_ref(v___y_4280_);
lean_inc(v___y_4279_);
lean_inc(v___y_4278_);
lean_inc_ref(v___y_4277_);
v___x_4302_ = lean_apply_16(v_G_4276_, v___x_4301_, v_a_4299_, lean_box(0), lean_box(0), v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, lean_box(0));
return v___x_4302_;
}
}
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec_ref(v_G_4276_);
v_a_4304_ = lean_ctor_get(v___y_4290_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___y_4290_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___y_4290_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___y_4290_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4390_ = _args[0];
lean_object* v_hypotheses_4391_ = _args[1];
lean_object* v_cacheId_4392_ = _args[2];
lean_object* v_methods_4393_ = _args[3];
lean_object* v_config_4394_ = _args[4];
lean_object* v___x_4395_ = _args[5];
lean_object* v___x_4396_ = _args[6];
lean_object* v___x_4397_ = _args[7];
lean_object* v_toMonadRef_4398_ = _args[8];
lean_object* v___f_4399_ = _args[9];
lean_object* v_next_4400_ = _args[10];
lean_object* v_acc_4401_ = _args[11];
lean_object* v_h_4402_ = _args[12];
lean_object* v_G_4403_ = _args[13];
lean_object* v___y_4404_ = _args[14];
lean_object* v___y_4405_ = _args[15];
lean_object* v___y_4406_ = _args[16];
lean_object* v___y_4407_ = _args[17];
lean_object* v___y_4408_ = _args[18];
lean_object* v___y_4409_ = _args[19];
lean_object* v___y_4410_ = _args[20];
lean_object* v___y_4411_ = _args[21];
lean_object* v___y_4412_ = _args[22];
lean_object* v___y_4413_ = _args[23];
lean_object* v___y_4414_ = _args[24];
lean_object* v___y_4415_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4416_; lean_object* v_res_4417_; 
v_cacheId_boxed_4416_ = lean_unbox(v_cacheId_4392_);
v_res_4417_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4390_, v_hypotheses_4391_, v_cacheId_boxed_4416_, v_methods_4393_, v_config_4394_, v___x_4395_, v___x_4396_, v___x_4397_, v_toMonadRef_4398_, v___f_4399_, v_next_4400_, v_acc_4401_, v_h_4402_, v_G_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v_next_4400_);
lean_dec_ref(v_hypotheses_4391_);
lean_dec(v___x_4390_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4418_, lean_object* v_methods_4419_, lean_object* v_config_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v___x_4433_; lean_object* v_toApplicative_4434_; lean_object* v_toFunctor_4435_; lean_object* v_toSeq_4436_; lean_object* v_toSeqLeft_4437_; lean_object* v_toSeqRight_4438_; lean_object* v___f_4439_; lean_object* v___f_4440_; lean_object* v___f_4441_; lean_object* v___f_4442_; lean_object* v___x_4443_; lean_object* v___f_4444_; lean_object* v___f_4445_; lean_object* v___f_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v_toApplicative_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4537_; 
v___x_4433_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4434_ = lean_ctor_get(v___x_4433_, 0);
v_toFunctor_4435_ = lean_ctor_get(v_toApplicative_4434_, 0);
v_toSeq_4436_ = lean_ctor_get(v_toApplicative_4434_, 2);
v_toSeqLeft_4437_ = lean_ctor_get(v_toApplicative_4434_, 3);
v_toSeqRight_4438_ = lean_ctor_get(v_toApplicative_4434_, 4);
v___f_4439_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4440_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4435_, 2);
v___f_4441_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4441_, 0, v_toFunctor_4435_);
v___f_4442_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4442_, 0, v_toFunctor_4435_);
v___x_4443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___f_4441_);
lean_ctor_set(v___x_4443_, 1, v___f_4442_);
lean_inc(v_toSeqRight_4438_);
v___f_4444_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4444_, 0, v_toSeqRight_4438_);
lean_inc(v_toSeqLeft_4437_);
v___f_4445_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4445_, 0, v_toSeqLeft_4437_);
lean_inc(v_toSeq_4436_);
v___f_4446_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4446_, 0, v_toSeq_4436_);
v___x_4447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4443_);
lean_ctor_set(v___x_4447_, 1, v___f_4439_);
lean_ctor_set(v___x_4447_, 2, v___f_4446_);
lean_ctor_set(v___x_4447_, 3, v___f_4445_);
lean_ctor_set(v___x_4447_, 4, v___f_4444_);
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
lean_ctor_set(v___x_4448_, 1, v___f_4440_);
v___x_4449_ = l_StateRefT_x27_instMonad___redArg(v___x_4448_);
v_toApplicative_4450_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4537_ == 0)
{
lean_object* v_unused_4538_; 
v_unused_4538_ = lean_ctor_get(v___x_4449_, 1);
lean_dec(v_unused_4538_);
v___x_4452_ = v___x_4449_;
v_isShared_4453_ = v_isSharedCheck_4537_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_toApplicative_4450_);
lean_dec(v___x_4449_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4537_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v_toFunctor_4454_; lean_object* v_toSeq_4455_; lean_object* v_toSeqLeft_4456_; lean_object* v_toSeqRight_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4535_; 
v_toFunctor_4454_ = lean_ctor_get(v_toApplicative_4450_, 0);
v_toSeq_4455_ = lean_ctor_get(v_toApplicative_4450_, 2);
v_toSeqLeft_4456_ = lean_ctor_get(v_toApplicative_4450_, 3);
v_toSeqRight_4457_ = lean_ctor_get(v_toApplicative_4450_, 4);
v_isSharedCheck_4535_ = !lean_is_exclusive(v_toApplicative_4450_);
if (v_isSharedCheck_4535_ == 0)
{
lean_object* v_unused_4536_; 
v_unused_4536_ = lean_ctor_get(v_toApplicative_4450_, 1);
lean_dec(v_unused_4536_);
v___x_4459_ = v_toApplicative_4450_;
v_isShared_4460_ = v_isSharedCheck_4535_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_toSeqRight_4457_);
lean_inc(v_toSeqLeft_4456_);
lean_inc(v_toSeq_4455_);
lean_inc(v_toFunctor_4454_);
lean_dec(v_toApplicative_4450_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4535_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___f_4461_; lean_object* v___f_4462_; lean_object* v___f_4463_; lean_object* v___f_4464_; lean_object* v___x_4465_; lean_object* v___f_4466_; lean_object* v___f_4467_; lean_object* v___f_4468_; lean_object* v___x_4470_; 
v___f_4461_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4462_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4454_);
v___f_4463_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4463_, 0, v_toFunctor_4454_);
v___f_4464_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4464_, 0, v_toFunctor_4454_);
v___x_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___f_4463_);
lean_ctor_set(v___x_4465_, 1, v___f_4464_);
v___f_4466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4466_, 0, v_toSeqRight_4457_);
v___f_4467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4467_, 0, v_toSeqLeft_4456_);
v___f_4468_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4468_, 0, v_toSeq_4455_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 4, v___f_4466_);
lean_ctor_set(v___x_4459_, 3, v___f_4467_);
lean_ctor_set(v___x_4459_, 2, v___f_4468_);
lean_ctor_set(v___x_4459_, 1, v___f_4461_);
lean_ctor_set(v___x_4459_, 0, v___x_4465_);
v___x_4470_ = v___x_4459_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4534_, 1, v___f_4461_);
lean_ctor_set(v_reuseFailAlloc_4534_, 2, v___f_4468_);
lean_ctor_set(v_reuseFailAlloc_4534_, 3, v___f_4467_);
lean_ctor_set(v_reuseFailAlloc_4534_, 4, v___f_4466_);
v___x_4470_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4472_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 1, v___f_4462_);
lean_ctor_set(v___x_4452_, 0, v___x_4470_);
v___x_4472_ = v___x_4452_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4470_);
lean_ctor_set(v_reuseFailAlloc_4533_, 1, v___f_4462_);
v___x_4472_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v_toMonadRef_4481_; lean_object* v___f_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v_hypotheses_4485_; lean_object* v___x_4486_; lean_object* v_newHyps_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___f_4491_; lean_object* v___x_4492_; lean_object* v___x_22108__overap_4493_; lean_object* v___x_4494_; 
v___x_4473_ = l_StateRefT_x27_instMonad___redArg(v___x_4472_);
v___x_4474_ = l_ReaderT_instMonad___redArg(v___x_4473_);
v___x_4475_ = l_StateRefT_x27_instMonad___redArg(v___x_4474_);
v___x_4476_ = l_ReaderT_instMonad___redArg(v___x_4475_);
v___x_4477_ = l_ReaderT_instMonad___redArg(v___x_4476_);
v___x_4478_ = l_StateRefT_x27_instMonad___redArg(v___x_4477_);
v___x_4479_ = l_ReaderT_instMonad___redArg(v___x_4478_);
v___x_4480_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4481_ = lean_ctor_get(v___x_4480_, 0);
v___f_4482_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4483_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4484_ = lean_st_ref_get(v_a_4422_);
v_hypotheses_4485_ = lean_ctor_get(v___x_4484_, 3);
lean_inc_ref(v_hypotheses_4485_);
lean_dec(v___x_4484_);
v___x_4486_ = lean_array_get_size(v_hypotheses_4485_);
v_newHyps_4487_ = lean_mk_empty_array_with_capacity(v___x_4486_);
v___x_4488_ = lean_unsigned_to_nat(0u);
v___x_4489_ = lean_box(0);
v___x_4490_ = lean_box(v_cacheId_4418_);
lean_inc_ref(v_toMonadRef_4481_);
v___f_4491_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4491_, 0, v___x_4486_);
lean_closure_set(v___f_4491_, 1, v_hypotheses_4485_);
lean_closure_set(v___f_4491_, 2, v___x_4490_);
lean_closure_set(v___f_4491_, 3, v_methods_4419_);
lean_closure_set(v___f_4491_, 4, v_config_4420_);
lean_closure_set(v___f_4491_, 5, v___x_4489_);
lean_closure_set(v___f_4491_, 6, v___x_4479_);
lean_closure_set(v___f_4491_, 7, v___x_4483_);
lean_closure_set(v___f_4491_, 8, v_toMonadRef_4481_);
lean_closure_set(v___f_4491_, 9, v___f_4482_);
v___x_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4489_);
lean_ctor_set(v___x_4492_, 1, v_newHyps_4487_);
v___x_22108__overap_4493_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4491_, v___x_4488_, v___x_4492_, lean_box(0));
lean_inc(v_a_4431_);
lean_inc_ref(v_a_4430_);
lean_inc(v_a_4429_);
lean_inc_ref(v_a_4428_);
lean_inc(v_a_4427_);
lean_inc_ref(v_a_4426_);
lean_inc(v_a_4425_);
lean_inc_ref(v_a_4424_);
lean_inc(v_a_4423_);
lean_inc(v_a_4422_);
lean_inc_ref(v_a_4421_);
v___x_4494_ = lean_apply_12(v___x_22108__overap_4493_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, lean_box(0));
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4524_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4497_ = v___x_4494_;
v_isShared_4498_ = v_isSharedCheck_4524_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4494_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4524_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v_fst_4499_; 
v_fst_4499_ = lean_ctor_get(v_a_4495_, 0);
if (lean_obj_tag(v_fst_4499_) == 0)
{
lean_object* v_snd_4500_; lean_object* v___x_4501_; lean_object* v_caches_4502_; lean_object* v_typeAnalysis_4503_; lean_object* v_target_4504_; uint8_t v_didChange_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4518_; 
v_snd_4500_ = lean_ctor_get(v_a_4495_, 1);
lean_inc(v_snd_4500_);
lean_dec(v_a_4495_);
v___x_4501_ = lean_st_ref_take(v_a_4422_);
v_caches_4502_ = lean_ctor_get(v___x_4501_, 0);
v_typeAnalysis_4503_ = lean_ctor_get(v___x_4501_, 1);
v_target_4504_ = lean_ctor_get(v___x_4501_, 2);
v_didChange_4505_ = lean_ctor_get_uint8(v___x_4501_, sizeof(void*)*4);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4518_ == 0)
{
lean_object* v_unused_4519_; 
v_unused_4519_ = lean_ctor_get(v___x_4501_, 3);
lean_dec(v_unused_4519_);
v___x_4507_ = v___x_4501_;
v_isShared_4508_ = v_isSharedCheck_4518_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_target_4504_);
lean_inc(v_typeAnalysis_4503_);
lean_inc(v_caches_4502_);
lean_dec(v___x_4501_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4518_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
lean_ctor_set(v___x_4507_, 3, v_snd_4500_);
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_caches_4502_);
lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_typeAnalysis_4503_);
lean_ctor_set(v_reuseFailAlloc_4517_, 2, v_target_4504_);
lean_ctor_set(v_reuseFailAlloc_4517_, 3, v_snd_4500_);
lean_ctor_set_uint8(v_reuseFailAlloc_4517_, sizeof(void*)*4, v_didChange_4505_);
v___x_4510_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; uint8_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4515_; 
v___x_4511_ = lean_st_ref_put(v_a_4422_, v___x_4510_);
v___x_4512_ = 0;
v___x_4513_ = lean_box(v___x_4512_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4513_);
v___x_4515_ = v___x_4497_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4513_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
else
{
lean_object* v_val_4520_; lean_object* v___x_4522_; 
lean_inc_ref(v_fst_4499_);
lean_dec(v_a_4495_);
v_val_4520_ = lean_ctor_get(v_fst_4499_, 0);
lean_inc(v_val_4520_);
lean_dec_ref_known(v_fst_4499_, 1);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v_val_4520_);
v___x_4522_ = v___x_4497_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_val_4520_);
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
else
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
v_a_4525_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4527_ = v___x_4494_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4494_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_4539_, lean_object* v_methods_4540_, lean_object* v_config_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
uint8_t v_cacheId_boxed_4554_; lean_object* v_res_4555_; 
v_cacheId_boxed_4554_ = lean_unbox(v_cacheId_4539_);
v_res_4555_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_4554_, v_methods_4540_, v_config_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_4556_, lean_object* v_hypotheses_4557_, uint8_t v_cacheId_4558_, lean_object* v_methods_4559_, lean_object* v_config_4560_, lean_object* v___x_4561_, lean_object* v___x_4562_, lean_object* v___x_4563_, lean_object* v_toMonadRef_4564_, lean_object* v___f_4565_, lean_object* v_next_4566_, lean_object* v_acc_4567_, lean_object* v_h_4568_, lean_object* v_G_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___y_4583_; uint8_t v___x_4605_; 
v___x_4605_ = lean_nat_dec_lt(v_next_4566_, v___x_4556_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; 
lean_dec_ref(v_G_4569_);
lean_dec(v___f_4565_);
lean_dec_ref(v_toMonadRef_4564_);
lean_dec_ref(v___x_4563_);
lean_dec_ref(v___x_4562_);
lean_dec(v___x_4561_);
lean_dec_ref(v_config_4560_);
lean_dec_ref(v_methods_4559_);
v___x_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4606_, 0, v_acc_4567_);
return v___x_4606_;
}
else
{
lean_object* v_snd_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4681_; 
v_snd_4607_ = lean_ctor_get(v_acc_4567_, 1);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_acc_4567_);
if (v_isSharedCheck_4681_ == 0)
{
lean_object* v_unused_4682_; 
v_unused_4682_ = lean_ctor_get(v_acc_4567_, 0);
lean_dec(v_unused_4682_);
v___x_4609_ = v_acc_4567_;
v_isShared_4610_ = v_isSharedCheck_4681_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_snd_4607_);
lean_dec(v_acc_4567_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4681_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4611_ = lean_array_fget_borrowed(v_hypotheses_4557_, v_next_4566_);
lean_inc(v___x_4611_);
v___x_4612_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4558_, v_methods_4559_, v_config_4560_, v___x_4611_, v___y_4571_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v_type_4614_; lean_object* v_value_4615_; uint8_t v___x_4616_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
lean_inc(v_a_4613_);
lean_dec_ref_known(v___x_4612_, 1);
v_type_4614_ = lean_ctor_get(v_a_4613_, 1);
v_value_4615_ = lean_ctor_get(v_a_4613_, 2);
lean_inc_ref(v_type_4614_);
v___x_4616_ = l_Lean_Expr_isFalse(v_type_4614_);
if (v___x_4616_ == 0)
{
lean_object* v_type_4617_; lean_object* v___f_4618_; uint8_t v___x_4648_; 
lean_del_object(v___x_4609_);
v_type_4617_ = lean_ctor_get(v___x_4611_, 1);
lean_inc(v___x_4561_);
lean_inc(v_a_4613_);
lean_inc(v_snd_4607_);
v___f_4618_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4618_, 0, v_snd_4607_);
lean_closure_set(v___f_4618_, 1, v_a_4613_);
lean_closure_set(v___f_4618_, 2, v___x_4561_);
v___x_4648_ = lean_expr_eqv(v_type_4617_, v_type_4614_);
if (v___x_4648_ == 0)
{
lean_inc_ref(v_type_4614_);
lean_dec(v_a_4613_);
lean_dec(v_snd_4607_);
lean_dec(v___x_4561_);
goto v___jp_4622_;
}
else
{
if (v___x_4616_ == 0)
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
lean_dec_ref(v___f_4618_);
lean_dec(v___f_4565_);
lean_dec_ref(v_toMonadRef_4564_);
lean_dec_ref(v___x_4563_);
lean_dec_ref(v___x_4562_);
v___x_4649_ = lean_box(0);
v___x_4650_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4607_, v_a_4613_, v___x_4561_, v___x_4649_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
v___y_4583_ = v___x_4650_;
goto v___jp_4582_;
}
else
{
lean_inc_ref(v_type_4614_);
lean_dec(v_a_4613_);
lean_dec(v_snd_4607_);
lean_dec(v___x_4561_);
goto v___jp_4622_;
}
}
v___jp_4619_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_box(0);
v___x_4621_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4605_, v___f_4618_, v___x_4620_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
v___y_4583_ = v___x_4621_;
goto v___jp_4582_;
}
v___jp_4622_:
{
lean_object* v_toCold_4623_; lean_object* v_options_4624_; uint8_t v_hasTrace_4625_; 
v_toCold_4623_ = lean_ctor_get(v___y_4579_, 0);
v_options_4624_ = lean_ctor_get(v_toCold_4623_, 2);
v_hasTrace_4625_ = lean_ctor_get_uint8(v_options_4624_, sizeof(void*)*1);
if (v_hasTrace_4625_ == 0)
{
lean_dec_ref(v_type_4614_);
lean_dec(v___f_4565_);
lean_dec_ref(v_toMonadRef_4564_);
lean_dec_ref(v___x_4563_);
lean_dec_ref(v___x_4562_);
goto v___jp_4619_;
}
else
{
lean_object* v_inheritedTraceOptions_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; uint8_t v___x_4629_; 
v_inheritedTraceOptions_4626_ = lean_ctor_get(v_toCold_4623_, 11);
v___x_4627_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4628_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4629_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4626_, v_options_4624_, v___x_4628_);
if (v___x_4629_ == 0)
{
lean_dec_ref(v_type_4614_);
lean_dec(v___f_4565_);
lean_dec_ref(v_toMonadRef_4564_);
lean_dec_ref(v___x_4563_);
lean_dec_ref(v___x_4562_);
goto v___jp_4619_;
}
else
{
lean_object* v_type_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_22210__overap_4636_; lean_object* v___x_4637_; 
v_type_4630_ = lean_ctor_get(v___x_4611_, 1);
lean_inc_ref(v_type_4630_);
v___x_4631_ = l_Lean_MessageData_ofExpr(v_type_4630_);
v___x_4632_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4631_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
v___x_4634_ = l_Lean_MessageData_ofExpr(v_type_4614_);
v___x_4635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4633_);
lean_ctor_set(v___x_4635_, 1, v___x_4634_);
v___x_22210__overap_4636_ = l_Lean_addTrace___redArg(v___x_4562_, v___x_4563_, v_toMonadRef_4564_, v___f_4565_, v___x_4627_, v___x_4635_);
lean_inc(v___y_4580_);
lean_inc_ref(v___y_4579_);
lean_inc(v___y_4578_);
lean_inc_ref(v___y_4577_);
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4575_);
lean_inc(v___y_4574_);
lean_inc_ref(v___y_4573_);
lean_inc(v___y_4572_);
lean_inc(v___y_4571_);
lean_inc_ref(v___y_4570_);
v___x_4637_ = lean_apply_12(v___x_22210__overap_4636_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, lean_box(0));
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4639_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref_known(v___x_4637_, 1);
v___x_4639_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4605_, v___f_4618_, v_a_4638_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
v___y_4583_ = v___x_4639_;
goto v___jp_4582_;
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec_ref(v___f_4618_);
lean_dec_ref(v_G_4569_);
v_a_4640_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4637_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4637_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4651_; 
lean_inc_ref(v_value_4615_);
lean_dec(v_a_4613_);
lean_dec_ref(v_G_4569_);
lean_dec(v___f_4565_);
lean_dec_ref(v_toMonadRef_4564_);
lean_dec_ref(v___x_4563_);
lean_dec_ref(v___x_4562_);
lean_dec(v___x_4561_);
v___x_4651_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4615_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4663_; 
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4663_ == 0)
{
lean_object* v_unused_4664_; 
v_unused_4664_ = lean_ctor_get(v___x_4651_, 0);
lean_dec(v_unused_4664_);
v___x_4653_ = v___x_4651_;
v_isShared_4654_ = v_isSharedCheck_4663_;
goto v_resetjp_4652_;
}
else
{
lean_dec(v___x_4651_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4663_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4658_; 
v___x_4655_ = lean_box(v___x_4605_);
v___x_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v___x_4656_);
v___x_4658_ = v___x_4609_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4662_, 1, v_snd_4607_);
v___x_4658_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
lean_object* v___x_4660_; 
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 0, v___x_4658_);
v___x_4660_ = v___x_4653_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
lean_del_object(v___x_4609_);
lean_dec(v_snd_4607_);
v_a_4665_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4651_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4651_);
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
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_del_object(v___x_4609_);
lean_dec(v_snd_4607_);
lean_dec_ref(v_G_4569_);
lean_dec(v___f_4565_);
lean_dec_ref(v_toMonadRef_4564_);
lean_dec_ref(v___x_4563_);
lean_dec_ref(v___x_4562_);
lean_dec(v___x_4561_);
v_a_4673_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4612_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4612_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
v___jp_4582_:
{
if (lean_obj_tag(v___y_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4596_; 
v_a_4584_ = lean_ctor_get(v___y_4583_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___y_4583_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4586_ = v___y_4583_;
v_isShared_4587_ = v_isSharedCheck_4596_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___y_4583_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4596_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
if (lean_obj_tag(v_a_4584_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4590_; 
lean_dec_ref(v_G_4569_);
v_a_4588_ = lean_ctor_get(v_a_4584_, 0);
lean_inc(v_a_4588_);
lean_dec_ref_known(v_a_4584_, 1);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 0, v_a_4588_);
v___x_4590_ = v___x_4586_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4588_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
lean_del_object(v___x_4586_);
v_a_4592_ = lean_ctor_get(v_a_4584_, 0);
lean_inc(v_a_4592_);
lean_dec_ref_known(v_a_4584_, 1);
v___x_4593_ = lean_unsigned_to_nat(1u);
v___x_4594_ = lean_nat_add(v_next_4566_, v___x_4593_);
lean_inc(v___y_4580_);
lean_inc_ref(v___y_4579_);
lean_inc(v___y_4578_);
lean_inc_ref(v___y_4577_);
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4575_);
lean_inc(v___y_4574_);
lean_inc_ref(v___y_4573_);
lean_inc(v___y_4572_);
lean_inc(v___y_4571_);
lean_inc_ref(v___y_4570_);
v___x_4595_ = lean_apply_16(v_G_4569_, v___x_4594_, v_a_4592_, lean_box(0), lean_box(0), v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, lean_box(0));
return v___x_4595_;
}
}
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
lean_dec_ref(v_G_4569_);
v_a_4597_ = lean_ctor_get(v___y_4583_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___y_4583_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___y_4583_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___y_4583_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4683_ = _args[0];
lean_object* v_hypotheses_4684_ = _args[1];
lean_object* v_cacheId_4685_ = _args[2];
lean_object* v_methods_4686_ = _args[3];
lean_object* v_config_4687_ = _args[4];
lean_object* v___x_4688_ = _args[5];
lean_object* v___x_4689_ = _args[6];
lean_object* v___x_4690_ = _args[7];
lean_object* v_toMonadRef_4691_ = _args[8];
lean_object* v___f_4692_ = _args[9];
lean_object* v_next_4693_ = _args[10];
lean_object* v_acc_4694_ = _args[11];
lean_object* v_h_4695_ = _args[12];
lean_object* v_G_4696_ = _args[13];
lean_object* v___y_4697_ = _args[14];
lean_object* v___y_4698_ = _args[15];
lean_object* v___y_4699_ = _args[16];
lean_object* v___y_4700_ = _args[17];
lean_object* v___y_4701_ = _args[18];
lean_object* v___y_4702_ = _args[19];
lean_object* v___y_4703_ = _args[20];
lean_object* v___y_4704_ = _args[21];
lean_object* v___y_4705_ = _args[22];
lean_object* v___y_4706_ = _args[23];
lean_object* v___y_4707_ = _args[24];
lean_object* v___y_4708_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4709_; lean_object* v_res_4710_; 
v_cacheId_boxed_4709_ = lean_unbox(v_cacheId_4685_);
v_res_4710_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4683_, v_hypotheses_4684_, v_cacheId_boxed_4709_, v_methods_4686_, v_config_4687_, v___x_4688_, v___x_4689_, v___x_4690_, v_toMonadRef_4691_, v___f_4692_, v_next_4693_, v_acc_4694_, v_h_4695_, v_G_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v_next_4693_);
lean_dec_ref(v_hypotheses_4684_);
lean_dec(v___x_4683_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4711_, lean_object* v_methods_4712_, lean_object* v_config_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v___x_4726_; lean_object* v_toApplicative_4727_; lean_object* v_toFunctor_4728_; lean_object* v_toSeq_4729_; lean_object* v_toSeqLeft_4730_; lean_object* v_toSeqRight_4731_; lean_object* v___f_4732_; lean_object* v___f_4733_; lean_object* v___f_4734_; lean_object* v___f_4735_; lean_object* v___x_4736_; lean_object* v___f_4737_; lean_object* v___f_4738_; lean_object* v___f_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v_toApplicative_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4830_; 
v___x_4726_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4727_ = lean_ctor_get(v___x_4726_, 0);
v_toFunctor_4728_ = lean_ctor_get(v_toApplicative_4727_, 0);
v_toSeq_4729_ = lean_ctor_get(v_toApplicative_4727_, 2);
v_toSeqLeft_4730_ = lean_ctor_get(v_toApplicative_4727_, 3);
v_toSeqRight_4731_ = lean_ctor_get(v_toApplicative_4727_, 4);
v___f_4732_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4733_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4728_, 2);
v___f_4734_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4734_, 0, v_toFunctor_4728_);
v___f_4735_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4735_, 0, v_toFunctor_4728_);
v___x_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4736_, 0, v___f_4734_);
lean_ctor_set(v___x_4736_, 1, v___f_4735_);
lean_inc(v_toSeqRight_4731_);
v___f_4737_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4737_, 0, v_toSeqRight_4731_);
lean_inc(v_toSeqLeft_4730_);
v___f_4738_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4738_, 0, v_toSeqLeft_4730_);
lean_inc(v_toSeq_4729_);
v___f_4739_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4739_, 0, v_toSeq_4729_);
v___x_4740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4736_);
lean_ctor_set(v___x_4740_, 1, v___f_4732_);
lean_ctor_set(v___x_4740_, 2, v___f_4739_);
lean_ctor_set(v___x_4740_, 3, v___f_4738_);
lean_ctor_set(v___x_4740_, 4, v___f_4737_);
v___x_4741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
lean_ctor_set(v___x_4741_, 1, v___f_4733_);
v___x_4742_ = l_StateRefT_x27_instMonad___redArg(v___x_4741_);
v_toApplicative_4743_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4830_ == 0)
{
lean_object* v_unused_4831_; 
v_unused_4831_ = lean_ctor_get(v___x_4742_, 1);
lean_dec(v_unused_4831_);
v___x_4745_ = v___x_4742_;
v_isShared_4746_ = v_isSharedCheck_4830_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_toApplicative_4743_);
lean_dec(v___x_4742_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4830_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v_toFunctor_4747_; lean_object* v_toSeq_4748_; lean_object* v_toSeqLeft_4749_; lean_object* v_toSeqRight_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4828_; 
v_toFunctor_4747_ = lean_ctor_get(v_toApplicative_4743_, 0);
v_toSeq_4748_ = lean_ctor_get(v_toApplicative_4743_, 2);
v_toSeqLeft_4749_ = lean_ctor_get(v_toApplicative_4743_, 3);
v_toSeqRight_4750_ = lean_ctor_get(v_toApplicative_4743_, 4);
v_isSharedCheck_4828_ = !lean_is_exclusive(v_toApplicative_4743_);
if (v_isSharedCheck_4828_ == 0)
{
lean_object* v_unused_4829_; 
v_unused_4829_ = lean_ctor_get(v_toApplicative_4743_, 1);
lean_dec(v_unused_4829_);
v___x_4752_ = v_toApplicative_4743_;
v_isShared_4753_ = v_isSharedCheck_4828_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_toSeqRight_4750_);
lean_inc(v_toSeqLeft_4749_);
lean_inc(v_toSeq_4748_);
lean_inc(v_toFunctor_4747_);
lean_dec(v_toApplicative_4743_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4828_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___f_4754_; lean_object* v___f_4755_; lean_object* v___f_4756_; lean_object* v___f_4757_; lean_object* v___x_4758_; lean_object* v___f_4759_; lean_object* v___f_4760_; lean_object* v___f_4761_; lean_object* v___x_4763_; 
v___f_4754_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4755_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4747_);
v___f_4756_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4756_, 0, v_toFunctor_4747_);
v___f_4757_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4757_, 0, v_toFunctor_4747_);
v___x_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___f_4756_);
lean_ctor_set(v___x_4758_, 1, v___f_4757_);
v___f_4759_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4759_, 0, v_toSeqRight_4750_);
v___f_4760_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4760_, 0, v_toSeqLeft_4749_);
v___f_4761_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4761_, 0, v_toSeq_4748_);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 4, v___f_4759_);
lean_ctor_set(v___x_4752_, 3, v___f_4760_);
lean_ctor_set(v___x_4752_, 2, v___f_4761_);
lean_ctor_set(v___x_4752_, 1, v___f_4754_);
lean_ctor_set(v___x_4752_, 0, v___x_4758_);
v___x_4763_ = v___x_4752_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4758_);
lean_ctor_set(v_reuseFailAlloc_4827_, 1, v___f_4754_);
lean_ctor_set(v_reuseFailAlloc_4827_, 2, v___f_4761_);
lean_ctor_set(v_reuseFailAlloc_4827_, 3, v___f_4760_);
lean_ctor_set(v_reuseFailAlloc_4827_, 4, v___f_4759_);
v___x_4763_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4765_; 
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 1, v___f_4755_);
lean_ctor_set(v___x_4745_, 0, v___x_4763_);
v___x_4765_ = v___x_4745_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4763_);
lean_ctor_set(v_reuseFailAlloc_4826_, 1, v___f_4755_);
v___x_4765_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v_toMonadRef_4774_; lean_object* v___f_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v_hypotheses_4778_; lean_object* v___x_4779_; lean_object* v_newHyps_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___f_4784_; lean_object* v___x_4785_; lean_object* v___x_22108__overap_4786_; lean_object* v___x_4787_; 
v___x_4766_ = l_StateRefT_x27_instMonad___redArg(v___x_4765_);
v___x_4767_ = l_ReaderT_instMonad___redArg(v___x_4766_);
v___x_4768_ = l_StateRefT_x27_instMonad___redArg(v___x_4767_);
v___x_4769_ = l_ReaderT_instMonad___redArg(v___x_4768_);
v___x_4770_ = l_ReaderT_instMonad___redArg(v___x_4769_);
v___x_4771_ = l_StateRefT_x27_instMonad___redArg(v___x_4770_);
v___x_4772_ = l_ReaderT_instMonad___redArg(v___x_4771_);
v___x_4773_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4774_ = lean_ctor_get(v___x_4773_, 0);
v___f_4775_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4776_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4777_ = lean_st_ref_get(v_a_4715_);
v_hypotheses_4778_ = lean_ctor_get(v___x_4777_, 3);
lean_inc_ref(v_hypotheses_4778_);
lean_dec(v___x_4777_);
v___x_4779_ = lean_array_get_size(v_hypotheses_4778_);
v_newHyps_4780_ = lean_mk_empty_array_with_capacity(v___x_4779_);
v___x_4781_ = lean_unsigned_to_nat(0u);
v___x_4782_ = lean_box(0);
v___x_4783_ = lean_box(v_cacheId_4711_);
lean_inc_ref(v_toMonadRef_4774_);
v___f_4784_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4784_, 0, v___x_4779_);
lean_closure_set(v___f_4784_, 1, v_hypotheses_4778_);
lean_closure_set(v___f_4784_, 2, v___x_4783_);
lean_closure_set(v___f_4784_, 3, v_methods_4712_);
lean_closure_set(v___f_4784_, 4, v_config_4713_);
lean_closure_set(v___f_4784_, 5, v___x_4782_);
lean_closure_set(v___f_4784_, 6, v___x_4772_);
lean_closure_set(v___f_4784_, 7, v___x_4776_);
lean_closure_set(v___f_4784_, 8, v_toMonadRef_4774_);
lean_closure_set(v___f_4784_, 9, v___f_4775_);
v___x_4785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4782_);
lean_ctor_set(v___x_4785_, 1, v_newHyps_4780_);
v___x_22108__overap_4786_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4784_, v___x_4781_, v___x_4785_, lean_box(0));
lean_inc(v_a_4724_);
lean_inc_ref(v_a_4723_);
lean_inc(v_a_4722_);
lean_inc_ref(v_a_4721_);
lean_inc(v_a_4720_);
lean_inc_ref(v_a_4719_);
lean_inc(v_a_4718_);
lean_inc_ref(v_a_4717_);
lean_inc(v_a_4716_);
lean_inc(v_a_4715_);
lean_inc_ref(v_a_4714_);
v___x_4787_ = lean_apply_12(v___x_22108__overap_4786_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, lean_box(0));
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4817_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4790_ = v___x_4787_;
v_isShared_4791_ = v_isSharedCheck_4817_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4787_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4817_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v_fst_4792_; 
v_fst_4792_ = lean_ctor_get(v_a_4788_, 0);
if (lean_obj_tag(v_fst_4792_) == 0)
{
lean_object* v_snd_4793_; lean_object* v___x_4794_; lean_object* v_caches_4795_; lean_object* v_typeAnalysis_4796_; lean_object* v_target_4797_; uint8_t v_didChange_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4811_; 
v_snd_4793_ = lean_ctor_get(v_a_4788_, 1);
lean_inc(v_snd_4793_);
lean_dec(v_a_4788_);
v___x_4794_ = lean_st_ref_take(v_a_4715_);
v_caches_4795_ = lean_ctor_get(v___x_4794_, 0);
v_typeAnalysis_4796_ = lean_ctor_get(v___x_4794_, 1);
v_target_4797_ = lean_ctor_get(v___x_4794_, 2);
v_didChange_4798_ = lean_ctor_get_uint8(v___x_4794_, sizeof(void*)*4);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4811_ == 0)
{
lean_object* v_unused_4812_; 
v_unused_4812_ = lean_ctor_get(v___x_4794_, 3);
lean_dec(v_unused_4812_);
v___x_4800_ = v___x_4794_;
v_isShared_4801_ = v_isSharedCheck_4811_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_target_4797_);
lean_inc(v_typeAnalysis_4796_);
lean_inc(v_caches_4795_);
lean_dec(v___x_4794_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4811_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 3, v_snd_4793_);
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_caches_4795_);
lean_ctor_set(v_reuseFailAlloc_4810_, 1, v_typeAnalysis_4796_);
lean_ctor_set(v_reuseFailAlloc_4810_, 2, v_target_4797_);
lean_ctor_set(v_reuseFailAlloc_4810_, 3, v_snd_4793_);
lean_ctor_set_uint8(v_reuseFailAlloc_4810_, sizeof(void*)*4, v_didChange_4798_);
v___x_4803_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
lean_object* v___x_4804_; uint8_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
v___x_4804_ = lean_st_ref_put(v_a_4715_, v___x_4803_);
v___x_4805_ = 0;
v___x_4806_ = lean_box(v___x_4805_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4806_);
v___x_4808_ = v___x_4790_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
else
{
lean_object* v_val_4813_; lean_object* v___x_4815_; 
lean_inc_ref(v_fst_4792_);
lean_dec(v_a_4788_);
v_val_4813_ = lean_ctor_get(v_fst_4792_, 0);
lean_inc(v_val_4813_);
lean_dec_ref_known(v_fst_4792_, 1);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v_val_4813_);
v___x_4815_ = v___x_4790_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_val_4813_);
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
else
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
v_a_4818_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4787_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4787_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4832_, lean_object* v_methods_4833_, lean_object* v_config_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_){
_start:
{
uint8_t v_cacheId_boxed_4847_; lean_object* v_res_4848_; 
v_cacheId_boxed_4847_ = lean_unbox(v_cacheId_4832_);
v_res_4848_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4847_, v_methods_4833_, v_config_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
lean_dec(v_a_4845_);
lean_dec_ref(v_a_4844_);
lean_dec(v_a_4843_);
lean_dec_ref(v_a_4842_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v___x_4855_; lean_object* v_env_4856_; lean_object* v___x_4857_; lean_object* v_toCold_4858_; lean_object* v_mctx_4859_; lean_object* v_lctx_4860_; lean_object* v_options_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4855_ = lean_st_ref_get(v___y_4853_);
v_env_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc_ref(v_env_4856_);
lean_dec(v___x_4855_);
v___x_4857_ = lean_st_ref_get(v___y_4851_);
v_toCold_4858_ = lean_ctor_get(v___y_4852_, 0);
v_mctx_4859_ = lean_ctor_get(v___x_4857_, 0);
lean_inc_ref(v_mctx_4859_);
lean_dec(v___x_4857_);
v_lctx_4860_ = lean_ctor_get(v___y_4850_, 2);
v_options_4861_ = lean_ctor_get(v_toCold_4858_, 2);
lean_inc_ref(v_options_4861_);
lean_inc_ref(v_lctx_4860_);
v___x_4862_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4862_, 0, v_env_4856_);
lean_ctor_set(v___x_4862_, 1, v_mctx_4859_);
lean_ctor_set(v___x_4862_, 2, v_lctx_4860_);
lean_ctor_set(v___x_4862_, 3, v_options_4861_);
v___x_4863_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4862_);
lean_ctor_set(v___x_4863_, 1, v_msgData_4849_);
v___x_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
return v_res_4871_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4872_; double v___x_4873_; 
v___x_4872_ = lean_unsigned_to_nat(0u);
v___x_4873_ = lean_float_of_nat(v___x_4872_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4877_, lean_object* v_msg_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v_ref_4884_; lean_object* v___x_4885_; lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4931_; 
v_ref_4884_ = lean_ctor_get(v___y_4881_, 2);
v___x_4885_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4888_ = v___x_4885_;
v_isShared_4889_ = v_isSharedCheck_4931_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4885_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4931_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4890_; lean_object* v_traceState_4891_; lean_object* v_env_4892_; lean_object* v_nextMacroScope_4893_; lean_object* v_ngen_4894_; lean_object* v_auxDeclNGen_4895_; lean_object* v_cache_4896_; lean_object* v_recordedDeps_4897_; lean_object* v_messages_4898_; lean_object* v_infoState_4899_; lean_object* v_snapshotTasks_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4930_; 
v___x_4890_ = lean_st_ref_take(v___y_4882_);
v_traceState_4891_ = lean_ctor_get(v___x_4890_, 4);
v_env_4892_ = lean_ctor_get(v___x_4890_, 0);
v_nextMacroScope_4893_ = lean_ctor_get(v___x_4890_, 1);
v_ngen_4894_ = lean_ctor_get(v___x_4890_, 2);
v_auxDeclNGen_4895_ = lean_ctor_get(v___x_4890_, 3);
v_cache_4896_ = lean_ctor_get(v___x_4890_, 5);
v_recordedDeps_4897_ = lean_ctor_get(v___x_4890_, 6);
v_messages_4898_ = lean_ctor_get(v___x_4890_, 7);
v_infoState_4899_ = lean_ctor_get(v___x_4890_, 8);
v_snapshotTasks_4900_ = lean_ctor_get(v___x_4890_, 9);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4902_ = v___x_4890_;
v_isShared_4903_ = v_isSharedCheck_4930_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_snapshotTasks_4900_);
lean_inc(v_infoState_4899_);
lean_inc(v_messages_4898_);
lean_inc(v_recordedDeps_4897_);
lean_inc(v_cache_4896_);
lean_inc(v_traceState_4891_);
lean_inc(v_auxDeclNGen_4895_);
lean_inc(v_ngen_4894_);
lean_inc(v_nextMacroScope_4893_);
lean_inc(v_env_4892_);
lean_dec(v___x_4890_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4930_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
uint64_t v_tid_4904_; lean_object* v_traces_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4929_; 
v_tid_4904_ = lean_ctor_get_uint64(v_traceState_4891_, sizeof(void*)*1);
v_traces_4905_ = lean_ctor_get(v_traceState_4891_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v_traceState_4891_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4907_ = v_traceState_4891_;
v_isShared_4908_ = v_isSharedCheck_4929_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_traces_4905_);
lean_dec(v_traceState_4891_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4929_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; double v___x_4911_; uint8_t v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4909_ = lean_box(0);
v___x_4910_ = lean_box(0);
v___x_4911_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4912_ = 0;
v___x_4913_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4914_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4914_, 0, v_cls_4877_);
lean_ctor_set(v___x_4914_, 1, v___x_4910_);
lean_ctor_set(v___x_4914_, 2, v___x_4913_);
lean_ctor_set_float(v___x_4914_, sizeof(void*)*3, v___x_4911_);
lean_ctor_set_float(v___x_4914_, sizeof(void*)*3 + 8, v___x_4911_);
lean_ctor_set_uint8(v___x_4914_, sizeof(void*)*3 + 16, v___x_4912_);
v___x_4915_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4916_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4914_);
lean_ctor_set(v___x_4916_, 1, v_a_4886_);
lean_ctor_set(v___x_4916_, 2, v___x_4915_);
lean_inc(v_ref_4884_);
v___x_4917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4917_, 0, v_ref_4884_);
lean_ctor_set(v___x_4917_, 1, v___x_4916_);
v___x_4918_ = l_Lean_PersistentArray_push___redArg(v_traces_4905_, v___x_4917_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4918_);
v___x_4920_ = v___x_4907_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4918_);
lean_ctor_set_uint64(v_reuseFailAlloc_4928_, sizeof(void*)*1, v_tid_4904_);
v___x_4920_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
lean_object* v___x_4922_; 
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 4, v___x_4920_);
v___x_4922_ = v___x_4902_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_env_4892_);
lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_nextMacroScope_4893_);
lean_ctor_set(v_reuseFailAlloc_4927_, 2, v_ngen_4894_);
lean_ctor_set(v_reuseFailAlloc_4927_, 3, v_auxDeclNGen_4895_);
lean_ctor_set(v_reuseFailAlloc_4927_, 4, v___x_4920_);
lean_ctor_set(v_reuseFailAlloc_4927_, 5, v_cache_4896_);
lean_ctor_set(v_reuseFailAlloc_4927_, 6, v_recordedDeps_4897_);
lean_ctor_set(v_reuseFailAlloc_4927_, 7, v_messages_4898_);
lean_ctor_set(v_reuseFailAlloc_4927_, 8, v_infoState_4899_);
lean_ctor_set(v_reuseFailAlloc_4927_, 9, v_snapshotTasks_4900_);
v___x_4922_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
lean_object* v___x_4923_; lean_object* v___x_4925_; 
v___x_4923_ = lean_st_ref_put(v___y_4882_, v___x_4922_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 0, v___x_4909_);
v___x_4925_ = v___x_4888_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4909_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4932_, lean_object* v_msg_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4932_, v_msg_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_4940_, lean_object* v___f_4941_, lean_object* v_____r_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v___x_4956_; lean_object* v_caches_4957_; lean_object* v_typeAnalysis_4958_; lean_object* v_target_4959_; lean_object* v_hypotheses_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4970_; 
v___x_4956_ = lean_st_ref_take(v___y_4945_);
v_caches_4957_ = lean_ctor_get(v___x_4956_, 0);
v_typeAnalysis_4958_ = lean_ctor_get(v___x_4956_, 1);
v_target_4959_ = lean_ctor_get(v___x_4956_, 2);
v_hypotheses_4960_ = lean_ctor_get(v___x_4956_, 3);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4962_ = v___x_4956_;
v_isShared_4963_ = v_isSharedCheck_4970_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_hypotheses_4960_);
lean_inc(v_target_4959_);
lean_inc(v_typeAnalysis_4958_);
lean_inc(v_caches_4957_);
lean_dec(v___x_4956_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4970_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4964_; lean_object* v___x_4966_; 
v___x_4964_ = lean_box(0);
if (v_isShared_4963_ == 0)
{
v___x_4966_ = v___x_4962_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v_caches_4957_);
lean_ctor_set(v_reuseFailAlloc_4969_, 1, v_typeAnalysis_4958_);
lean_ctor_set(v_reuseFailAlloc_4969_, 2, v_target_4959_);
lean_ctor_set(v_reuseFailAlloc_4969_, 3, v_hypotheses_4960_);
v___x_4966_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; 
lean_ctor_set_uint8(v___x_4966_, sizeof(void*)*4, v___x_4940_);
v___x_4967_ = lean_st_ref_put(v___y_4945_, v___x_4966_);
lean_inc(v___y_4954_);
lean_inc_ref(v___y_4953_);
lean_inc(v___y_4952_);
lean_inc_ref(v___y_4951_);
lean_inc(v___y_4950_);
lean_inc_ref(v___y_4949_);
lean_inc(v___y_4948_);
lean_inc_ref(v___y_4947_);
lean_inc(v___y_4946_);
lean_inc(v___y_4945_);
lean_inc_ref(v___y_4944_);
lean_inc(v___y_4943_);
v___x_4968_ = lean_apply_14(v___f_4941_, v___x_4964_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, lean_box(0));
return v___x_4968_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_4971_, lean_object* v___f_4972_, lean_object* v_____r_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
uint8_t v___x_35925__boxed_4987_; lean_object* v_res_4988_; 
v___x_35925__boxed_4987_ = lean_unbox(v___x_4971_);
v_res_4988_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35925__boxed_4987_, v___f_4972_, v_____r_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec(v___y_4977_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec(v___y_4974_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_4989_, lean_object* v_a_4990_, lean_object* v___x_4991_, lean_object* v_____r_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5006_ = lean_array_push(v_snd_4989_, v_a_4990_);
v___x_5007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_4991_);
lean_ctor_set(v___x_5007_, 1, v___x_5006_);
v___x_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5007_);
v___x_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5008_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_5010_ = _args[0];
lean_object* v_a_5011_ = _args[1];
lean_object* v___x_5012_ = _args[2];
lean_object* v_____r_5013_ = _args[3];
lean_object* v___y_5014_ = _args[4];
lean_object* v___y_5015_ = _args[5];
lean_object* v___y_5016_ = _args[6];
lean_object* v___y_5017_ = _args[7];
lean_object* v___y_5018_ = _args[8];
lean_object* v___y_5019_ = _args[9];
lean_object* v___y_5020_ = _args[10];
lean_object* v___y_5021_ = _args[11];
lean_object* v___y_5022_ = _args[12];
lean_object* v___y_5023_ = _args[13];
lean_object* v___y_5024_ = _args[14];
lean_object* v___y_5025_ = _args[15];
lean_object* v___y_5026_ = _args[16];
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5010_, v_a_5011_, v___x_5012_, v_____r_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
lean_dec(v___y_5014_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5028_, lean_object* v___x_5029_, lean_object* v_methods_5030_, lean_object* v_config_5031_, lean_object* v_a_5032_, lean_object* v_b_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v___y_5048_; uint8_t v___x_5070_; 
v___x_5070_ = lean_nat_dec_lt(v_a_5032_, v_upperBound_5028_);
if (v___x_5070_ == 0)
{
lean_object* v___x_5071_; 
lean_dec(v_a_5032_);
lean_dec_ref(v_config_5031_);
lean_dec_ref(v_methods_5030_);
v___x_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5071_, 0, v_b_5033_);
return v___x_5071_;
}
else
{
lean_object* v_snd_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5171_; 
v_snd_5072_ = lean_ctor_get(v_b_5033_, 1);
v_isSharedCheck_5171_ = !lean_is_exclusive(v_b_5033_);
if (v_isSharedCheck_5171_ == 0)
{
lean_object* v_unused_5172_; 
v_unused_5172_ = lean_ctor_get(v_b_5033_, 0);
lean_dec(v_unused_5172_);
v___x_5074_ = v_b_5033_;
v_isShared_5075_ = v_isSharedCheck_5171_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_snd_5072_);
lean_dec(v_b_5033_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5171_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v_type_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5076_ = lean_box(0);
v___x_5077_ = lean_array_fget_borrowed(v___x_5029_, v_a_5032_);
v___x_5078_ = lean_st_ref_take(v___y_5034_);
v___x_5079_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5080_ = lean_st_ref_put(v___y_5034_, v___x_5079_);
v_type_5081_ = lean_ctor_get(v___x_5077_, 1);
v___x_5082_ = lean_unsigned_to_nat(0u);
v___x_5083_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5083_, 0, v___x_5082_);
lean_ctor_set(v___x_5083_, 1, v___x_5078_);
lean_ctor_set(v___x_5083_, 2, v___x_5079_);
lean_ctor_set(v___x_5083_, 3, v___x_5079_);
lean_inc_ref(v_type_5081_);
v___x_5084_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5084_, 0, v_type_5081_);
lean_inc_ref(v_config_5031_);
lean_inc_ref(v_methods_5030_);
v___x_5085_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5084_, v_methods_5030_, v_config_5031_, v___x_5083_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v_snd_5087_; lean_object* v_fst_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5162_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref_known(v___x_5085_, 1);
v_snd_5087_ = lean_ctor_get(v_a_5086_, 1);
v_fst_5088_ = lean_ctor_get(v_a_5086_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v_a_5086_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5090_ = v_a_5086_;
v_isShared_5091_ = v_isSharedCheck_5162_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_snd_5087_);
lean_inc(v_fst_5088_);
lean_dec(v_a_5086_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5162_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v_persistentCache_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
v_persistentCache_5092_ = lean_ctor_get(v_snd_5087_, 1);
lean_inc_ref(v_persistentCache_5092_);
lean_dec(v_snd_5087_);
v___x_5093_ = lean_st_ref_swap(v___y_5034_, v_persistentCache_5092_);
lean_dec(v___x_5093_);
lean_inc(v___x_5077_);
v___x_5094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5077_, v_fst_5088_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; lean_object* v_type_5096_; lean_object* v_value_5097_; uint8_t v___x_5098_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
lean_inc(v_a_5095_);
lean_dec_ref_known(v___x_5094_, 1);
v_type_5096_ = lean_ctor_get(v_a_5095_, 1);
v_value_5097_ = lean_ctor_get(v_a_5095_, 2);
lean_inc_ref(v_type_5096_);
v___x_5098_ = l_Lean_Expr_isFalse(v_type_5096_);
if (v___x_5098_ == 0)
{
lean_object* v___f_5099_; uint8_t v___x_5129_; 
lean_del_object(v___x_5090_);
lean_inc(v_a_5095_);
lean_inc(v_snd_5072_);
v___f_5099_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5099_, 0, v_snd_5072_);
lean_closure_set(v___f_5099_, 1, v_a_5095_);
lean_closure_set(v___f_5099_, 2, v___x_5076_);
v___x_5129_ = lean_expr_eqv(v_type_5081_, v_type_5096_);
if (v___x_5129_ == 0)
{
lean_inc_ref(v_type_5096_);
lean_dec(v_a_5095_);
lean_dec(v_snd_5072_);
goto v___jp_5103_;
}
else
{
if (v___x_5098_ == 0)
{
lean_object* v___x_5130_; lean_object* v___x_5131_; 
lean_dec_ref(v___f_5099_);
lean_del_object(v___x_5074_);
v___x_5130_ = lean_box(0);
v___x_5131_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5072_, v_a_5095_, v___x_5076_, v___x_5130_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
v___y_5048_ = v___x_5131_;
goto v___jp_5047_;
}
else
{
lean_inc_ref(v_type_5096_);
lean_dec(v_a_5095_);
lean_dec(v_snd_5072_);
goto v___jp_5103_;
}
}
v___jp_5100_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5101_ = lean_box(0);
v___x_5102_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5070_, v___f_5099_, v___x_5101_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
v___y_5048_ = v___x_5102_;
goto v___jp_5047_;
}
v___jp_5103_:
{
lean_object* v_toCold_5104_; lean_object* v_options_5105_; uint8_t v_hasTrace_5106_; 
v_toCold_5104_ = lean_ctor_get(v___y_5044_, 0);
v_options_5105_ = lean_ctor_get(v_toCold_5104_, 2);
v_hasTrace_5106_ = lean_ctor_get_uint8(v_options_5105_, sizeof(void*)*1);
if (v_hasTrace_5106_ == 0)
{
lean_dec_ref(v_type_5096_);
lean_del_object(v___x_5074_);
goto v___jp_5100_;
}
else
{
lean_object* v_inheritedTraceOptions_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; uint8_t v___x_5110_; 
v_inheritedTraceOptions_5107_ = lean_ctor_get(v_toCold_5104_, 11);
v___x_5108_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5109_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5110_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5107_, v_options_5105_, v___x_5109_);
if (v___x_5110_ == 0)
{
lean_dec_ref(v_type_5096_);
lean_del_object(v___x_5074_);
goto v___jp_5100_;
}
else
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5114_; 
lean_inc_ref(v_type_5081_);
v___x_5111_ = l_Lean_MessageData_ofExpr(v_type_5081_);
v___x_5112_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5075_ == 0)
{
lean_ctor_set_tag(v___x_5074_, 7);
lean_ctor_set(v___x_5074_, 1, v___x_5112_);
lean_ctor_set(v___x_5074_, 0, v___x_5111_);
v___x_5114_ = v___x_5074_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v___x_5111_);
lean_ctor_set(v_reuseFailAlloc_5128_, 1, v___x_5112_);
v___x_5114_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
v___x_5115_ = l_Lean_MessageData_ofExpr(v_type_5096_);
v___x_5116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5116_, 0, v___x_5114_);
lean_ctor_set(v___x_5116_, 1, v___x_5115_);
v___x_5117_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5108_, v___x_5116_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v___x_5119_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_a_5118_);
lean_dec_ref_known(v___x_5117_, 1);
v___x_5119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5070_, v___f_5099_, v_a_5118_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
v___y_5048_ = v___x_5119_;
goto v___jp_5047_;
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5127_; 
lean_dec_ref(v___f_5099_);
lean_dec(v_a_5032_);
lean_dec_ref(v_config_5031_);
lean_dec_ref(v_methods_5030_);
v_a_5120_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5122_ = v___x_5117_;
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5117_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5125_; 
if (v_isShared_5123_ == 0)
{
v___x_5125_ = v___x_5122_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
return v___x_5125_;
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
lean_object* v___x_5132_; 
lean_inc_ref(v_value_5097_);
lean_dec(v_a_5095_);
lean_del_object(v___x_5074_);
lean_dec(v_a_5032_);
lean_dec_ref(v_config_5031_);
lean_dec_ref(v_methods_5030_);
v___x_5132_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5097_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5144_; 
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5144_ == 0)
{
lean_object* v_unused_5145_; 
v_unused_5145_ = lean_ctor_get(v___x_5132_, 0);
lean_dec(v_unused_5145_);
v___x_5134_ = v___x_5132_;
v_isShared_5135_ = v_isSharedCheck_5144_;
goto v_resetjp_5133_;
}
else
{
lean_dec(v___x_5132_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5144_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5139_; 
v___x_5136_ = lean_box(v___x_5070_);
v___x_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 1, v_snd_5072_);
lean_ctor_set(v___x_5090_, 0, v___x_5137_);
v___x_5139_ = v___x_5090_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v___x_5137_);
lean_ctor_set(v_reuseFailAlloc_5143_, 1, v_snd_5072_);
v___x_5139_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
lean_object* v___x_5141_; 
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 0, v___x_5139_);
v___x_5141_ = v___x_5134_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v___x_5139_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
}
else
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
lean_del_object(v___x_5090_);
lean_dec(v_snd_5072_);
v_a_5146_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5148_ = v___x_5132_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5132_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5146_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
}
else
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5161_; 
lean_del_object(v___x_5090_);
lean_del_object(v___x_5074_);
lean_dec(v_snd_5072_);
lean_dec(v_a_5032_);
lean_dec_ref(v_config_5031_);
lean_dec_ref(v_methods_5030_);
v_a_5154_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5156_ = v___x_5094_;
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5094_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5159_; 
if (v_isShared_5157_ == 0)
{
v___x_5159_ = v___x_5156_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
lean_del_object(v___x_5074_);
lean_dec(v_snd_5072_);
lean_dec(v_a_5032_);
lean_dec_ref(v_config_5031_);
lean_dec_ref(v_methods_5030_);
v_a_5163_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5085_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5085_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
}
v___jp_5047_:
{
if (lean_obj_tag(v___y_5048_) == 0)
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5061_; 
v_a_5049_ = lean_ctor_get(v___y_5048_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___y_5048_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5051_ = v___y_5048_;
v_isShared_5052_ = v_isSharedCheck_5061_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___y_5048_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5061_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
if (lean_obj_tag(v_a_5049_) == 0)
{
lean_object* v_a_5053_; lean_object* v___x_5055_; 
lean_dec(v_a_5032_);
lean_dec_ref(v_config_5031_);
lean_dec_ref(v_methods_5030_);
v_a_5053_ = lean_ctor_get(v_a_5049_, 0);
lean_inc(v_a_5053_);
lean_dec_ref_known(v_a_5049_, 1);
if (v_isShared_5052_ == 0)
{
lean_ctor_set(v___x_5051_, 0, v_a_5053_);
v___x_5055_ = v___x_5051_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5053_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
else
{
lean_object* v_a_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
lean_del_object(v___x_5051_);
v_a_5057_ = lean_ctor_get(v_a_5049_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v_a_5049_, 1);
v___x_5058_ = lean_unsigned_to_nat(1u);
v___x_5059_ = lean_nat_add(v_a_5032_, v___x_5058_);
lean_dec(v_a_5032_);
v_a_5032_ = v___x_5059_;
v_b_5033_ = v_a_5057_;
goto _start;
}
}
}
else
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5069_; 
lean_dec(v_a_5032_);
lean_dec_ref(v_config_5031_);
lean_dec_ref(v_methods_5030_);
v_a_5062_ = lean_ctor_get(v___y_5048_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___y_5048_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5064_ = v___y_5048_;
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___y_5048_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5067_; 
if (v_isShared_5065_ == 0)
{
v___x_5067_ = v___x_5064_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_a_5062_);
v___x_5067_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
return v___x_5067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5173_ = _args[0];
lean_object* v___x_5174_ = _args[1];
lean_object* v_methods_5175_ = _args[2];
lean_object* v_config_5176_ = _args[3];
lean_object* v_a_5177_ = _args[4];
lean_object* v_b_5178_ = _args[5];
lean_object* v___y_5179_ = _args[6];
lean_object* v___y_5180_ = _args[7];
lean_object* v___y_5181_ = _args[8];
lean_object* v___y_5182_ = _args[9];
lean_object* v___y_5183_ = _args[10];
lean_object* v___y_5184_ = _args[11];
lean_object* v___y_5185_ = _args[12];
lean_object* v___y_5186_ = _args[13];
lean_object* v___y_5187_ = _args[14];
lean_object* v___y_5188_ = _args[15];
lean_object* v___y_5189_ = _args[16];
lean_object* v___y_5190_ = _args[17];
lean_object* v___y_5191_ = _args[18];
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5173_, v___x_5174_, v_methods_5175_, v_config_5176_, v_a_5177_, v_b_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___x_5174_);
lean_dec(v_upperBound_5173_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_5193_, lean_object* v_config_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_){
_start:
{
lean_object* v___x_5208_; lean_object* v_hypotheses_5209_; lean_object* v___x_5210_; lean_object* v_newHyps_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v___x_5208_ = lean_st_ref_get(v_a_5197_);
v_hypotheses_5209_ = lean_ctor_get(v___x_5208_, 3);
lean_inc_ref(v_hypotheses_5209_);
lean_dec(v___x_5208_);
v___x_5210_ = lean_array_get_size(v_hypotheses_5209_);
v_newHyps_5211_ = lean_mk_empty_array_with_capacity(v___x_5210_);
v___x_5212_ = lean_unsigned_to_nat(0u);
v___x_5213_ = lean_box(0);
v___x_5214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5214_, 0, v___x_5213_);
lean_ctor_set(v___x_5214_, 1, v_newHyps_5211_);
v___x_5215_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_5210_, v_hypotheses_5209_, v_methods_5193_, v_config_5194_, v___x_5212_, v___x_5214_, v_a_5195_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_);
lean_dec_ref(v_hypotheses_5209_);
if (lean_obj_tag(v___x_5215_) == 0)
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5245_; 
v_a_5216_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5218_ = v___x_5215_;
v_isShared_5219_ = v_isSharedCheck_5245_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5215_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5245_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v_fst_5220_; 
v_fst_5220_ = lean_ctor_get(v_a_5216_, 0);
if (lean_obj_tag(v_fst_5220_) == 0)
{
lean_object* v_snd_5221_; lean_object* v___x_5222_; lean_object* v_caches_5223_; lean_object* v_typeAnalysis_5224_; lean_object* v_target_5225_; uint8_t v_didChange_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5239_; 
v_snd_5221_ = lean_ctor_get(v_a_5216_, 1);
lean_inc(v_snd_5221_);
lean_dec(v_a_5216_);
v___x_5222_ = lean_st_ref_take(v_a_5197_);
v_caches_5223_ = lean_ctor_get(v___x_5222_, 0);
v_typeAnalysis_5224_ = lean_ctor_get(v___x_5222_, 1);
v_target_5225_ = lean_ctor_get(v___x_5222_, 2);
v_didChange_5226_ = lean_ctor_get_uint8(v___x_5222_, sizeof(void*)*4);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5222_);
if (v_isSharedCheck_5239_ == 0)
{
lean_object* v_unused_5240_; 
v_unused_5240_ = lean_ctor_get(v___x_5222_, 3);
lean_dec(v_unused_5240_);
v___x_5228_ = v___x_5222_;
v_isShared_5229_ = v_isSharedCheck_5239_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_target_5225_);
lean_inc(v_typeAnalysis_5224_);
lean_inc(v_caches_5223_);
lean_dec(v___x_5222_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5239_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 3, v_snd_5221_);
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_caches_5223_);
lean_ctor_set(v_reuseFailAlloc_5238_, 1, v_typeAnalysis_5224_);
lean_ctor_set(v_reuseFailAlloc_5238_, 2, v_target_5225_);
lean_ctor_set(v_reuseFailAlloc_5238_, 3, v_snd_5221_);
lean_ctor_set_uint8(v_reuseFailAlloc_5238_, sizeof(void*)*4, v_didChange_5226_);
v___x_5231_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
lean_object* v___x_5232_; uint8_t v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5236_; 
v___x_5232_ = lean_st_ref_put(v_a_5197_, v___x_5231_);
v___x_5233_ = 0;
v___x_5234_ = lean_box(v___x_5233_);
if (v_isShared_5219_ == 0)
{
lean_ctor_set(v___x_5218_, 0, v___x_5234_);
v___x_5236_ = v___x_5218_;
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
lean_object* v_val_5241_; lean_object* v___x_5243_; 
lean_inc_ref(v_fst_5220_);
lean_dec(v_a_5216_);
v_val_5241_ = lean_ctor_get(v_fst_5220_, 0);
lean_inc(v_val_5241_);
lean_dec_ref_known(v_fst_5220_, 1);
if (v_isShared_5219_ == 0)
{
lean_ctor_set(v___x_5218_, 0, v_val_5241_);
v___x_5243_ = v___x_5218_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_val_5241_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
else
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5253_; 
v_a_5246_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5248_ = v___x_5215_;
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5215_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5251_; 
if (v_isShared_5249_ == 0)
{
v___x_5251_ = v___x_5248_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_5254_, lean_object* v_config_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5254_, v_config_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_);
lean_dec(v_a_5267_);
lean_dec_ref(v_a_5266_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_a_5259_);
lean_dec(v_a_5258_);
lean_dec_ref(v_a_5257_);
lean_dec(v_a_5256_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_5270_, lean_object* v_msg_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_){
_start:
{
lean_object* v___x_5285_; 
v___x_5285_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5270_, v_msg_5271_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_5286_, lean_object* v_msg_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5286_, v_msg_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec(v___y_5297_);
lean_dec_ref(v___y_5296_);
lean_dec(v___y_5295_);
lean_dec_ref(v___y_5294_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_upperBound_5302_, lean_object* v___x_5303_, lean_object* v_methods_5304_, lean_object* v_config_5305_, lean_object* v_inst_5306_, lean_object* v_R_5307_, lean_object* v_a_5308_, lean_object* v_b_5309_, lean_object* v_c_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v___x_5324_; 
v___x_5324_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5302_, v___x_5303_, v_methods_5304_, v_config_5305_, v_a_5308_, v_b_5309_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
return v___x_5324_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5325_ = _args[0];
lean_object* v___x_5326_ = _args[1];
lean_object* v_methods_5327_ = _args[2];
lean_object* v_config_5328_ = _args[3];
lean_object* v_inst_5329_ = _args[4];
lean_object* v_R_5330_ = _args[5];
lean_object* v_a_5331_ = _args[6];
lean_object* v_b_5332_ = _args[7];
lean_object* v_c_5333_ = _args[8];
lean_object* v___y_5334_ = _args[9];
lean_object* v___y_5335_ = _args[10];
lean_object* v___y_5336_ = _args[11];
lean_object* v___y_5337_ = _args[12];
lean_object* v___y_5338_ = _args[13];
lean_object* v___y_5339_ = _args[14];
lean_object* v___y_5340_ = _args[15];
lean_object* v___y_5341_ = _args[16];
lean_object* v___y_5342_ = _args[17];
lean_object* v___y_5343_ = _args[18];
lean_object* v___y_5344_ = _args[19];
lean_object* v___y_5345_ = _args[20];
lean_object* v___y_5346_ = _args[21];
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5325_, v___x_5326_, v_methods_5327_, v_config_5328_, v_inst_5329_, v_R_5330_, v_a_5331_, v_b_5332_, v_c_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
lean_dec(v___y_5345_);
lean_dec_ref(v___y_5344_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
lean_dec(v___y_5334_);
lean_dec_ref(v___x_5326_);
lean_dec(v_upperBound_5325_);
return v_res_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_5348_, lean_object* v_config_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_){
_start:
{
lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; 
v___x_5362_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5363_ = lean_st_mk_ref(v___x_5362_);
v___x_5364_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5348_, v_config_5349_, v___x_5363_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5364_) == 0)
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5373_; 
v_a_5365_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5367_ = v___x_5364_;
v_isShared_5368_ = v_isSharedCheck_5373_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5364_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5373_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5369_; lean_object* v___x_5371_; 
v___x_5369_ = lean_st_ref_get(v___x_5363_);
lean_dec(v___x_5363_);
lean_dec(v___x_5369_);
if (v_isShared_5368_ == 0)
{
v___x_5371_ = v___x_5367_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5365_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
else
{
lean_dec(v___x_5363_);
return v___x_5364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_5374_, lean_object* v_config_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_){
_start:
{
lean_object* v_res_5388_; 
v_res_5388_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5374_, v_config_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_, v_a_5385_, v_a_5386_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
lean_dec(v_a_5384_);
lean_dec_ref(v_a_5383_);
lean_dec(v_a_5382_);
lean_dec_ref(v_a_5381_);
lean_dec(v_a_5380_);
lean_dec_ref(v_a_5379_);
lean_dec(v_a_5378_);
lean_dec(v_a_5377_);
lean_dec_ref(v_a_5376_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_5389_, lean_object* v_msg_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v_ref_5396_; lean_object* v___x_5397_; lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5443_; 
v_ref_5396_ = lean_ctor_get(v___y_5393_, 2);
v___x_5397_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_);
v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5443_ == 0)
{
v___x_5400_ = v___x_5397_;
v_isShared_5401_ = v_isSharedCheck_5443_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_dec(v___x_5397_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5443_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5402_; lean_object* v_traceState_5403_; lean_object* v_env_5404_; lean_object* v_nextMacroScope_5405_; lean_object* v_ngen_5406_; lean_object* v_auxDeclNGen_5407_; lean_object* v_cache_5408_; lean_object* v_recordedDeps_5409_; lean_object* v_messages_5410_; lean_object* v_infoState_5411_; lean_object* v_snapshotTasks_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5442_; 
v___x_5402_ = lean_st_ref_take(v___y_5394_);
v_traceState_5403_ = lean_ctor_get(v___x_5402_, 4);
v_env_5404_ = lean_ctor_get(v___x_5402_, 0);
v_nextMacroScope_5405_ = lean_ctor_get(v___x_5402_, 1);
v_ngen_5406_ = lean_ctor_get(v___x_5402_, 2);
v_auxDeclNGen_5407_ = lean_ctor_get(v___x_5402_, 3);
v_cache_5408_ = lean_ctor_get(v___x_5402_, 5);
v_recordedDeps_5409_ = lean_ctor_get(v___x_5402_, 6);
v_messages_5410_ = lean_ctor_get(v___x_5402_, 7);
v_infoState_5411_ = lean_ctor_get(v___x_5402_, 8);
v_snapshotTasks_5412_ = lean_ctor_get(v___x_5402_, 9);
v_isSharedCheck_5442_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5442_ == 0)
{
v___x_5414_ = v___x_5402_;
v_isShared_5415_ = v_isSharedCheck_5442_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_snapshotTasks_5412_);
lean_inc(v_infoState_5411_);
lean_inc(v_messages_5410_);
lean_inc(v_recordedDeps_5409_);
lean_inc(v_cache_5408_);
lean_inc(v_traceState_5403_);
lean_inc(v_auxDeclNGen_5407_);
lean_inc(v_ngen_5406_);
lean_inc(v_nextMacroScope_5405_);
lean_inc(v_env_5404_);
lean_dec(v___x_5402_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5442_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
uint64_t v_tid_5416_; lean_object* v_traces_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5441_; 
v_tid_5416_ = lean_ctor_get_uint64(v_traceState_5403_, sizeof(void*)*1);
v_traces_5417_ = lean_ctor_get(v_traceState_5403_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v_traceState_5403_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5419_ = v_traceState_5403_;
v_isShared_5420_ = v_isSharedCheck_5441_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_traces_5417_);
lean_dec(v_traceState_5403_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5441_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; double v___x_5423_; uint8_t v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5432_; 
v___x_5421_ = lean_box(0);
v___x_5422_ = lean_box(0);
v___x_5423_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5424_ = 0;
v___x_5425_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5426_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5426_, 0, v_cls_5389_);
lean_ctor_set(v___x_5426_, 1, v___x_5422_);
lean_ctor_set(v___x_5426_, 2, v___x_5425_);
lean_ctor_set_float(v___x_5426_, sizeof(void*)*3, v___x_5423_);
lean_ctor_set_float(v___x_5426_, sizeof(void*)*3 + 8, v___x_5423_);
lean_ctor_set_uint8(v___x_5426_, sizeof(void*)*3 + 16, v___x_5424_);
v___x_5427_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5428_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5426_);
lean_ctor_set(v___x_5428_, 1, v_a_5398_);
lean_ctor_set(v___x_5428_, 2, v___x_5427_);
lean_inc(v_ref_5396_);
v___x_5429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5429_, 0, v_ref_5396_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___x_5430_ = l_Lean_PersistentArray_push___redArg(v_traces_5417_, v___x_5429_);
if (v_isShared_5420_ == 0)
{
lean_ctor_set(v___x_5419_, 0, v___x_5430_);
v___x_5432_ = v___x_5419_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5430_);
lean_ctor_set_uint64(v_reuseFailAlloc_5440_, sizeof(void*)*1, v_tid_5416_);
v___x_5432_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
lean_object* v___x_5434_; 
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 4, v___x_5432_);
v___x_5434_ = v___x_5414_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_env_5404_);
lean_ctor_set(v_reuseFailAlloc_5439_, 1, v_nextMacroScope_5405_);
lean_ctor_set(v_reuseFailAlloc_5439_, 2, v_ngen_5406_);
lean_ctor_set(v_reuseFailAlloc_5439_, 3, v_auxDeclNGen_5407_);
lean_ctor_set(v_reuseFailAlloc_5439_, 4, v___x_5432_);
lean_ctor_set(v_reuseFailAlloc_5439_, 5, v_cache_5408_);
lean_ctor_set(v_reuseFailAlloc_5439_, 6, v_recordedDeps_5409_);
lean_ctor_set(v_reuseFailAlloc_5439_, 7, v_messages_5410_);
lean_ctor_set(v_reuseFailAlloc_5439_, 8, v_infoState_5411_);
lean_ctor_set(v_reuseFailAlloc_5439_, 9, v_snapshotTasks_5412_);
v___x_5434_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5435_; lean_object* v___x_5437_; 
v___x_5435_ = lean_st_ref_put(v___y_5394_, v___x_5434_);
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 0, v___x_5421_);
v___x_5437_ = v___x_5400_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5421_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5444_, lean_object* v_msg_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5444_, v_msg_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
lean_dec(v___y_5449_);
lean_dec_ref(v___y_5448_);
lean_dec(v___y_5447_);
lean_dec_ref(v___y_5446_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5452_, lean_object* v___x_5453_, lean_object* v_methods_5454_, lean_object* v_config_5455_, lean_object* v_a_5456_, lean_object* v_b_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_){
_start:
{
lean_object* v___y_5472_; uint8_t v___x_5494_; 
v___x_5494_ = lean_nat_dec_lt(v_a_5456_, v_upperBound_5452_);
if (v___x_5494_ == 0)
{
lean_object* v___x_5495_; 
lean_dec(v_a_5456_);
lean_dec_ref(v_config_5455_);
lean_dec_ref(v_methods_5454_);
v___x_5495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5495_, 0, v_b_5457_);
return v___x_5495_;
}
else
{
lean_object* v_snd_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5602_; 
v_snd_5496_ = lean_ctor_get(v_b_5457_, 1);
v_isSharedCheck_5602_ = !lean_is_exclusive(v_b_5457_);
if (v_isSharedCheck_5602_ == 0)
{
lean_object* v_unused_5603_; 
v_unused_5603_ = lean_ctor_get(v_b_5457_, 0);
lean_dec(v_unused_5603_);
v___x_5498_ = v_b_5457_;
v_isShared_5499_ = v_isSharedCheck_5602_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_snd_5496_);
lean_dec(v_b_5457_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5602_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v_type_5505_; lean_object* v___x_5506_; lean_object* v___x_5508_; 
v___x_5500_ = lean_box(0);
v___x_5501_ = lean_array_fget_borrowed(v___x_5453_, v_a_5456_);
v___x_5502_ = lean_st_ref_take(v___y_5458_);
v___x_5503_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5504_ = lean_st_ref_put(v___y_5458_, v___x_5503_);
v_type_5505_ = lean_ctor_get(v___x_5501_, 1);
v___x_5506_ = lean_unsigned_to_nat(0u);
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 1, v___x_5502_);
lean_ctor_set(v___x_5498_, 0, v___x_5506_);
v___x_5508_ = v___x_5498_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5506_);
lean_ctor_set(v_reuseFailAlloc_5601_, 1, v___x_5502_);
v___x_5508_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; 
lean_inc_ref(v_type_5505_);
v___x_5509_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5509_, 0, v_type_5505_);
lean_inc_ref(v_config_5455_);
lean_inc_ref(v_methods_5454_);
v___x_5510_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5509_, v_methods_5454_, v_config_5455_, v___x_5508_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
if (lean_obj_tag(v___x_5510_) == 0)
{
lean_object* v_a_5511_; lean_object* v_snd_5512_; lean_object* v_fst_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5592_; 
v_a_5511_ = lean_ctor_get(v___x_5510_, 0);
lean_inc(v_a_5511_);
lean_dec_ref_known(v___x_5510_, 1);
v_snd_5512_ = lean_ctor_get(v_a_5511_, 1);
v_fst_5513_ = lean_ctor_get(v_a_5511_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v_a_5511_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5515_ = v_a_5511_;
v_isShared_5516_ = v_isSharedCheck_5592_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_snd_5512_);
lean_inc(v_fst_5513_);
lean_dec(v_a_5511_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5592_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v_cache_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5590_; 
v_cache_5517_ = lean_ctor_get(v_snd_5512_, 1);
v_isSharedCheck_5590_ = !lean_is_exclusive(v_snd_5512_);
if (v_isSharedCheck_5590_ == 0)
{
lean_object* v_unused_5591_; 
v_unused_5591_ = lean_ctor_get(v_snd_5512_, 0);
lean_dec(v_unused_5591_);
v___x_5519_ = v_snd_5512_;
v_isShared_5520_ = v_isSharedCheck_5590_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_cache_5517_);
lean_dec(v_snd_5512_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5590_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; 
v___x_5521_ = lean_st_ref_swap(v___y_5458_, v_cache_5517_);
lean_dec(v___x_5521_);
lean_inc(v___x_5501_);
v___x_5522_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5501_, v_fst_5513_);
lean_dec(v_fst_5513_);
if (lean_obj_tag(v___x_5522_) == 0)
{
lean_object* v_a_5523_; lean_object* v_type_5524_; lean_object* v_value_5525_; uint8_t v___x_5526_; 
v_a_5523_ = lean_ctor_get(v___x_5522_, 0);
lean_inc(v_a_5523_);
lean_dec_ref_known(v___x_5522_, 1);
v_type_5524_ = lean_ctor_get(v_a_5523_, 1);
v_value_5525_ = lean_ctor_get(v_a_5523_, 2);
lean_inc_ref(v_type_5524_);
v___x_5526_ = l_Lean_Expr_isFalse(v_type_5524_);
if (v___x_5526_ == 0)
{
lean_object* v___f_5527_; uint8_t v___x_5557_; 
lean_del_object(v___x_5515_);
lean_inc(v_a_5523_);
lean_inc(v_snd_5496_);
v___f_5527_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5527_, 0, v_snd_5496_);
lean_closure_set(v___f_5527_, 1, v_a_5523_);
lean_closure_set(v___f_5527_, 2, v___x_5500_);
v___x_5557_ = lean_expr_eqv(v_type_5505_, v_type_5524_);
if (v___x_5557_ == 0)
{
lean_inc_ref(v_type_5524_);
lean_dec(v_a_5523_);
lean_dec(v_snd_5496_);
goto v___jp_5531_;
}
else
{
if (v___x_5526_ == 0)
{
lean_object* v___x_5558_; lean_object* v___x_5559_; 
lean_dec_ref(v___f_5527_);
lean_del_object(v___x_5519_);
v___x_5558_ = lean_box(0);
v___x_5559_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5496_, v_a_5523_, v___x_5500_, v___x_5558_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
v___y_5472_ = v___x_5559_;
goto v___jp_5471_;
}
else
{
lean_inc_ref(v_type_5524_);
lean_dec(v_a_5523_);
lean_dec(v_snd_5496_);
goto v___jp_5531_;
}
}
v___jp_5528_:
{
lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5529_ = lean_box(0);
v___x_5530_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5494_, v___f_5527_, v___x_5529_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
v___y_5472_ = v___x_5530_;
goto v___jp_5471_;
}
v___jp_5531_:
{
lean_object* v_toCold_5532_; lean_object* v_options_5533_; uint8_t v_hasTrace_5534_; 
v_toCold_5532_ = lean_ctor_get(v___y_5468_, 0);
v_options_5533_ = lean_ctor_get(v_toCold_5532_, 2);
v_hasTrace_5534_ = lean_ctor_get_uint8(v_options_5533_, sizeof(void*)*1);
if (v_hasTrace_5534_ == 0)
{
lean_dec_ref(v_type_5524_);
lean_del_object(v___x_5519_);
goto v___jp_5528_;
}
else
{
lean_object* v_inheritedTraceOptions_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; uint8_t v___x_5538_; 
v_inheritedTraceOptions_5535_ = lean_ctor_get(v_toCold_5532_, 11);
v___x_5536_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5537_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5538_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5535_, v_options_5533_, v___x_5537_);
if (v___x_5538_ == 0)
{
lean_dec_ref(v_type_5524_);
lean_del_object(v___x_5519_);
goto v___jp_5528_;
}
else
{
lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5542_; 
lean_inc_ref(v_type_5505_);
v___x_5539_ = l_Lean_MessageData_ofExpr(v_type_5505_);
v___x_5540_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5520_ == 0)
{
lean_ctor_set_tag(v___x_5519_, 7);
lean_ctor_set(v___x_5519_, 1, v___x_5540_);
lean_ctor_set(v___x_5519_, 0, v___x_5539_);
v___x_5542_ = v___x_5519_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v___x_5540_);
v___x_5542_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; 
v___x_5543_ = l_Lean_MessageData_ofExpr(v_type_5524_);
v___x_5544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5542_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
v___x_5545_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5536_, v___x_5544_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_object* v_a_5546_; lean_object* v___x_5547_; 
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_a_5546_);
lean_dec_ref_known(v___x_5545_, 1);
v___x_5547_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5494_, v___f_5527_, v_a_5546_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
v___y_5472_ = v___x_5547_;
goto v___jp_5471_;
}
else
{
lean_object* v_a_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5555_; 
lean_dec_ref(v___f_5527_);
lean_dec(v_a_5456_);
lean_dec_ref(v_config_5455_);
lean_dec_ref(v_methods_5454_);
v_a_5548_ = lean_ctor_get(v___x_5545_, 0);
v_isSharedCheck_5555_ = !lean_is_exclusive(v___x_5545_);
if (v_isSharedCheck_5555_ == 0)
{
v___x_5550_ = v___x_5545_;
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_a_5548_);
lean_dec(v___x_5545_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5553_; 
if (v_isShared_5551_ == 0)
{
v___x_5553_ = v___x_5550_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_a_5548_);
v___x_5553_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
return v___x_5553_;
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
lean_object* v___x_5560_; 
lean_inc_ref(v_value_5525_);
lean_dec(v_a_5523_);
lean_del_object(v___x_5519_);
lean_dec(v_a_5456_);
lean_dec_ref(v_config_5455_);
lean_dec_ref(v_methods_5454_);
v___x_5560_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5525_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5572_; 
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5572_ == 0)
{
lean_object* v_unused_5573_; 
v_unused_5573_ = lean_ctor_get(v___x_5560_, 0);
lean_dec(v_unused_5573_);
v___x_5562_ = v___x_5560_;
v_isShared_5563_ = v_isSharedCheck_5572_;
goto v_resetjp_5561_;
}
else
{
lean_dec(v___x_5560_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5572_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5567_; 
v___x_5564_ = lean_box(v___x_5494_);
v___x_5565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5564_);
if (v_isShared_5516_ == 0)
{
lean_ctor_set(v___x_5515_, 1, v_snd_5496_);
lean_ctor_set(v___x_5515_, 0, v___x_5565_);
v___x_5567_ = v___x_5515_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_snd_5496_);
v___x_5567_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
lean_object* v___x_5569_; 
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 0, v___x_5567_);
v___x_5569_ = v___x_5562_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v___x_5567_);
v___x_5569_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
return v___x_5569_;
}
}
}
}
else
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5581_; 
lean_del_object(v___x_5515_);
lean_dec(v_snd_5496_);
v_a_5574_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5576_ = v___x_5560_;
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___x_5560_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
}
}
else
{
lean_object* v_a_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5589_; 
lean_del_object(v___x_5519_);
lean_del_object(v___x_5515_);
lean_dec(v_snd_5496_);
lean_dec(v_a_5456_);
lean_dec_ref(v_config_5455_);
lean_dec_ref(v_methods_5454_);
v_a_5582_ = lean_ctor_get(v___x_5522_, 0);
v_isSharedCheck_5589_ = !lean_is_exclusive(v___x_5522_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5584_ = v___x_5522_;
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_a_5582_);
lean_dec(v___x_5522_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5587_; 
if (v_isShared_5585_ == 0)
{
v___x_5587_ = v___x_5584_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5582_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
}
}
}
}
}
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5600_; 
lean_dec(v_snd_5496_);
lean_dec(v_a_5456_);
lean_dec_ref(v_config_5455_);
lean_dec_ref(v_methods_5454_);
v_a_5593_ = lean_ctor_get(v___x_5510_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5595_ = v___x_5510_;
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5510_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5596_ == 0)
{
v___x_5598_ = v___x_5595_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_a_5593_);
v___x_5598_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
return v___x_5598_;
}
}
}
}
}
}
v___jp_5471_:
{
if (lean_obj_tag(v___y_5472_) == 0)
{
lean_object* v_a_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5485_; 
v_a_5473_ = lean_ctor_get(v___y_5472_, 0);
v_isSharedCheck_5485_ = !lean_is_exclusive(v___y_5472_);
if (v_isSharedCheck_5485_ == 0)
{
v___x_5475_ = v___y_5472_;
v_isShared_5476_ = v_isSharedCheck_5485_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_a_5473_);
lean_dec(v___y_5472_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5485_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
if (lean_obj_tag(v_a_5473_) == 0)
{
lean_object* v_a_5477_; lean_object* v___x_5479_; 
lean_dec(v_a_5456_);
lean_dec_ref(v_config_5455_);
lean_dec_ref(v_methods_5454_);
v_a_5477_ = lean_ctor_get(v_a_5473_, 0);
lean_inc(v_a_5477_);
lean_dec_ref_known(v_a_5473_, 1);
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 0, v_a_5477_);
v___x_5479_ = v___x_5475_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5477_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
else
{
lean_object* v_a_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
lean_del_object(v___x_5475_);
v_a_5481_ = lean_ctor_get(v_a_5473_, 0);
lean_inc(v_a_5481_);
lean_dec_ref_known(v_a_5473_, 1);
v___x_5482_ = lean_unsigned_to_nat(1u);
v___x_5483_ = lean_nat_add(v_a_5456_, v___x_5482_);
lean_dec(v_a_5456_);
v_a_5456_ = v___x_5483_;
v_b_5457_ = v_a_5481_;
goto _start;
}
}
}
else
{
lean_object* v_a_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5493_; 
lean_dec(v_a_5456_);
lean_dec_ref(v_config_5455_);
lean_dec_ref(v_methods_5454_);
v_a_5486_ = lean_ctor_get(v___y_5472_, 0);
v_isSharedCheck_5493_ = !lean_is_exclusive(v___y_5472_);
if (v_isSharedCheck_5493_ == 0)
{
v___x_5488_ = v___y_5472_;
v_isShared_5489_ = v_isSharedCheck_5493_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_a_5486_);
lean_dec(v___y_5472_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5493_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5491_; 
if (v_isShared_5489_ == 0)
{
v___x_5491_ = v___x_5488_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5486_);
v___x_5491_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
return v___x_5491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5604_ = _args[0];
lean_object* v___x_5605_ = _args[1];
lean_object* v_methods_5606_ = _args[2];
lean_object* v_config_5607_ = _args[3];
lean_object* v_a_5608_ = _args[4];
lean_object* v_b_5609_ = _args[5];
lean_object* v___y_5610_ = _args[6];
lean_object* v___y_5611_ = _args[7];
lean_object* v___y_5612_ = _args[8];
lean_object* v___y_5613_ = _args[9];
lean_object* v___y_5614_ = _args[10];
lean_object* v___y_5615_ = _args[11];
lean_object* v___y_5616_ = _args[12];
lean_object* v___y_5617_ = _args[13];
lean_object* v___y_5618_ = _args[14];
lean_object* v___y_5619_ = _args[15];
lean_object* v___y_5620_ = _args[16];
lean_object* v___y_5621_ = _args[17];
lean_object* v___y_5622_ = _args[18];
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5604_, v___x_5605_, v_methods_5606_, v_config_5607_, v_a_5608_, v_b_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
lean_dec(v___y_5621_);
lean_dec_ref(v___y_5620_);
lean_dec(v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec_ref(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec(v___y_5613_);
lean_dec(v___y_5612_);
lean_dec_ref(v___y_5611_);
lean_dec(v___y_5610_);
lean_dec_ref(v___x_5605_);
lean_dec(v_upperBound_5604_);
return v_res_5623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5624_, lean_object* v_config_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_){
_start:
{
lean_object* v___x_5639_; lean_object* v_hypotheses_5640_; lean_object* v___x_5641_; lean_object* v_newHyps_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; 
v___x_5639_ = lean_st_ref_get(v_a_5628_);
v_hypotheses_5640_ = lean_ctor_get(v___x_5639_, 3);
lean_inc_ref(v_hypotheses_5640_);
lean_dec(v___x_5639_);
v___x_5641_ = lean_array_get_size(v_hypotheses_5640_);
v_newHyps_5642_ = lean_mk_empty_array_with_capacity(v___x_5641_);
v___x_5643_ = lean_unsigned_to_nat(0u);
v___x_5644_ = lean_box(0);
v___x_5645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
lean_ctor_set(v___x_5645_, 1, v_newHyps_5642_);
v___x_5646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5641_, v_hypotheses_5640_, v_methods_5624_, v_config_5625_, v___x_5643_, v___x_5645_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_);
lean_dec_ref(v_hypotheses_5640_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_object* v_a_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5676_; 
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
v_isSharedCheck_5676_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5676_ == 0)
{
v___x_5649_ = v___x_5646_;
v_isShared_5650_ = v_isSharedCheck_5676_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_a_5647_);
lean_dec(v___x_5646_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5676_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v_fst_5651_; 
v_fst_5651_ = lean_ctor_get(v_a_5647_, 0);
if (lean_obj_tag(v_fst_5651_) == 0)
{
lean_object* v_snd_5652_; lean_object* v___x_5653_; lean_object* v_caches_5654_; lean_object* v_typeAnalysis_5655_; lean_object* v_target_5656_; uint8_t v_didChange_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5670_; 
v_snd_5652_ = lean_ctor_get(v_a_5647_, 1);
lean_inc(v_snd_5652_);
lean_dec(v_a_5647_);
v___x_5653_ = lean_st_ref_take(v_a_5628_);
v_caches_5654_ = lean_ctor_get(v___x_5653_, 0);
v_typeAnalysis_5655_ = lean_ctor_get(v___x_5653_, 1);
v_target_5656_ = lean_ctor_get(v___x_5653_, 2);
v_didChange_5657_ = lean_ctor_get_uint8(v___x_5653_, sizeof(void*)*4);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5670_ == 0)
{
lean_object* v_unused_5671_; 
v_unused_5671_ = lean_ctor_get(v___x_5653_, 3);
lean_dec(v_unused_5671_);
v___x_5659_ = v___x_5653_;
v_isShared_5660_ = v_isSharedCheck_5670_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_target_5656_);
lean_inc(v_typeAnalysis_5655_);
lean_inc(v_caches_5654_);
lean_dec(v___x_5653_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5670_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v___x_5662_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 3, v_snd_5652_);
v___x_5662_ = v___x_5659_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_caches_5654_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v_typeAnalysis_5655_);
lean_ctor_set(v_reuseFailAlloc_5669_, 2, v_target_5656_);
lean_ctor_set(v_reuseFailAlloc_5669_, 3, v_snd_5652_);
lean_ctor_set_uint8(v_reuseFailAlloc_5669_, sizeof(void*)*4, v_didChange_5657_);
v___x_5662_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5663_; uint8_t v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5667_; 
v___x_5663_ = lean_st_ref_put(v_a_5628_, v___x_5662_);
v___x_5664_ = 0;
v___x_5665_ = lean_box(v___x_5664_);
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 0, v___x_5665_);
v___x_5667_ = v___x_5649_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v___x_5665_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
}
else
{
lean_object* v_val_5672_; lean_object* v___x_5674_; 
lean_inc_ref(v_fst_5651_);
lean_dec(v_a_5647_);
v_val_5672_ = lean_ctor_get(v_fst_5651_, 0);
lean_inc(v_val_5672_);
lean_dec_ref_known(v_fst_5651_, 1);
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 0, v_val_5672_);
v___x_5674_ = v___x_5649_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_val_5672_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
else
{
lean_object* v_a_5677_; lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5684_; 
v_a_5677_ = lean_ctor_get(v___x_5646_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5679_ = v___x_5646_;
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
else
{
lean_inc(v_a_5677_);
lean_dec(v___x_5646_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v___x_5682_; 
if (v_isShared_5680_ == 0)
{
v___x_5682_ = v___x_5679_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_a_5677_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5685_, lean_object* v_config_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_){
_start:
{
lean_object* v_res_5700_; 
v_res_5700_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5685_, v_config_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_);
lean_dec(v_a_5698_);
lean_dec_ref(v_a_5697_);
lean_dec(v_a_5696_);
lean_dec_ref(v_a_5695_);
lean_dec(v_a_5694_);
lean_dec_ref(v_a_5693_);
lean_dec(v_a_5692_);
lean_dec_ref(v_a_5691_);
lean_dec(v_a_5690_);
lean_dec(v_a_5689_);
lean_dec_ref(v_a_5688_);
lean_dec(v_a_5687_);
return v_res_5700_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5701_, lean_object* v_msg_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_){
_start:
{
lean_object* v___x_5716_; 
v___x_5716_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5701_, v_msg_5702_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5717_, lean_object* v_msg_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_){
_start:
{
lean_object* v_res_5732_; 
v_res_5732_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5717_, v_msg_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_);
lean_dec(v___y_5730_);
lean_dec_ref(v___y_5729_);
lean_dec(v___y_5728_);
lean_dec_ref(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v___y_5725_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec(v___y_5721_);
lean_dec_ref(v___y_5720_);
lean_dec(v___y_5719_);
return v_res_5732_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5733_, lean_object* v___x_5734_, lean_object* v_methods_5735_, lean_object* v_config_5736_, lean_object* v_inst_5737_, lean_object* v_R_5738_, lean_object* v_a_5739_, lean_object* v_b_5740_, lean_object* v_c_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_){
_start:
{
lean_object* v___x_5755_; 
v___x_5755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5733_, v___x_5734_, v_methods_5735_, v_config_5736_, v_a_5739_, v_b_5740_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_);
return v___x_5755_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5756_ = _args[0];
lean_object* v___x_5757_ = _args[1];
lean_object* v_methods_5758_ = _args[2];
lean_object* v_config_5759_ = _args[3];
lean_object* v_inst_5760_ = _args[4];
lean_object* v_R_5761_ = _args[5];
lean_object* v_a_5762_ = _args[6];
lean_object* v_b_5763_ = _args[7];
lean_object* v_c_5764_ = _args[8];
lean_object* v___y_5765_ = _args[9];
lean_object* v___y_5766_ = _args[10];
lean_object* v___y_5767_ = _args[11];
lean_object* v___y_5768_ = _args[12];
lean_object* v___y_5769_ = _args[13];
lean_object* v___y_5770_ = _args[14];
lean_object* v___y_5771_ = _args[15];
lean_object* v___y_5772_ = _args[16];
lean_object* v___y_5773_ = _args[17];
lean_object* v___y_5774_ = _args[18];
lean_object* v___y_5775_ = _args[19];
lean_object* v___y_5776_ = _args[20];
lean_object* v___y_5777_ = _args[21];
_start:
{
lean_object* v_res_5778_; 
v_res_5778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5756_, v___x_5757_, v_methods_5758_, v_config_5759_, v_inst_5760_, v_R_5761_, v_a_5762_, v_b_5763_, v_c_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
lean_dec(v___y_5776_);
lean_dec_ref(v___y_5775_);
lean_dec(v___y_5774_);
lean_dec_ref(v___y_5773_);
lean_dec(v___y_5772_);
lean_dec_ref(v___y_5771_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5768_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___x_5757_);
lean_dec(v_upperBound_5756_);
return v_res_5778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5779_, lean_object* v_config_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_){
_start:
{
lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5793_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5794_ = lean_st_mk_ref(v___x_5793_);
v___x_5795_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5779_, v_config_5780_, v___x_5794_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_);
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5804_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5798_ = v___x_5795_;
v_isShared_5799_ = v_isSharedCheck_5804_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5795_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5804_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v___x_5800_; lean_object* v___x_5802_; 
v___x_5800_ = lean_st_ref_get(v___x_5794_);
lean_dec(v___x_5794_);
lean_dec(v___x_5800_);
if (v_isShared_5799_ == 0)
{
v___x_5802_ = v___x_5798_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_a_5796_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
else
{
lean_dec(v___x_5794_);
return v___x_5795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5805_, lean_object* v_config_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_, lean_object* v_a_5818_){
_start:
{
lean_object* v_res_5819_; 
v_res_5819_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5805_, v_config_5806_, v_a_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_, v_a_5816_, v_a_5817_);
lean_dec(v_a_5817_);
lean_dec_ref(v_a_5816_);
lean_dec(v_a_5815_);
lean_dec_ref(v_a_5814_);
lean_dec(v_a_5813_);
lean_dec_ref(v_a_5812_);
lean_dec(v_a_5811_);
lean_dec_ref(v_a_5810_);
lean_dec(v_a_5809_);
lean_dec(v_a_5808_);
lean_dec_ref(v_a_5807_);
return v_res_5819_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
return v___x_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5823_, lean_object* v_x_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; 
v___x_5837_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5838_ = l_Lean_MessageData_ofName(v_name_5823_);
v___x_5839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5839_, 0, v___x_5837_);
lean_ctor_set(v___x_5839_, 1, v___x_5838_);
v___x_5840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5840_, 0, v___x_5839_);
return v___x_5840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5841_, lean_object* v_x_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5841_, v_x_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
lean_dec(v___y_5853_);
lean_dec_ref(v___y_5852_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
lean_dec(v___y_5845_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
lean_dec_ref(v_x_5842_);
return v_res_5855_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5856_; 
v___x_5856_ = l_instMonadExceptOfEIO___redArg();
return v___x_5856_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5857_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5858_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5857_);
return v___x_5858_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5859_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5860_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5859_);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5861_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5862_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5861_);
return v___x_5862_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5863_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5864_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5863_);
return v___x_5864_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5866_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5865_);
return v___x_5866_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5867_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5868_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5867_);
return v___x_5868_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5869_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5870_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5869_);
return v___x_5870_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5871_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5872_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5871_);
return v___x_5872_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; 
v___x_5873_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5874_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5873_);
return v___x_5874_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5875_; lean_object* v___x_5876_; 
v___x_5875_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5876_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5875_);
return v___x_5876_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5877_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5878_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5877_);
return v___x_5878_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5880_; double v___x_5881_; 
v___x_5880_ = lean_unsigned_to_nat(1000000000u);
v___x_5881_ = lean_float_of_nat(v___x_5880_);
return v___x_5881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_, lean_object* v_a_5892_, lean_object* v_a_5893_){
_start:
{
lean_object* v___x_5895_; lean_object* v_toApplicative_5896_; lean_object* v_toFunctor_5897_; lean_object* v_toSeq_5898_; lean_object* v_toSeqLeft_5899_; lean_object* v_toSeqRight_5900_; lean_object* v___f_5901_; lean_object* v___f_5902_; lean_object* v___f_5903_; lean_object* v___f_5904_; lean_object* v___x_5905_; lean_object* v___f_5906_; lean_object* v___f_5907_; lean_object* v___f_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v_toApplicative_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_6055_; 
v___x_5895_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5896_ = lean_ctor_get(v___x_5895_, 0);
v_toFunctor_5897_ = lean_ctor_get(v_toApplicative_5896_, 0);
v_toSeq_5898_ = lean_ctor_get(v_toApplicative_5896_, 2);
v_toSeqLeft_5899_ = lean_ctor_get(v_toApplicative_5896_, 3);
v_toSeqRight_5900_ = lean_ctor_get(v_toApplicative_5896_, 4);
v___f_5901_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5902_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5897_, 2);
v___f_5903_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5903_, 0, v_toFunctor_5897_);
v___f_5904_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5904_, 0, v_toFunctor_5897_);
v___x_5905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5905_, 0, v___f_5903_);
lean_ctor_set(v___x_5905_, 1, v___f_5904_);
lean_inc(v_toSeqRight_5900_);
v___f_5906_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5906_, 0, v_toSeqRight_5900_);
lean_inc(v_toSeqLeft_5899_);
v___f_5907_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5907_, 0, v_toSeqLeft_5899_);
lean_inc(v_toSeq_5898_);
v___f_5908_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5908_, 0, v_toSeq_5898_);
v___x_5909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5905_);
lean_ctor_set(v___x_5909_, 1, v___f_5901_);
lean_ctor_set(v___x_5909_, 2, v___f_5908_);
lean_ctor_set(v___x_5909_, 3, v___f_5907_);
lean_ctor_set(v___x_5909_, 4, v___f_5906_);
v___x_5910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5909_);
lean_ctor_set(v___x_5910_, 1, v___f_5902_);
v___x_5911_ = l_StateRefT_x27_instMonad___redArg(v___x_5910_);
v_toApplicative_5912_ = lean_ctor_get(v___x_5911_, 0);
v_isSharedCheck_6055_ = !lean_is_exclusive(v___x_5911_);
if (v_isSharedCheck_6055_ == 0)
{
lean_object* v_unused_6056_; 
v_unused_6056_ = lean_ctor_get(v___x_5911_, 1);
lean_dec(v_unused_6056_);
v___x_5914_ = v___x_5911_;
v_isShared_5915_ = v_isSharedCheck_6055_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_toApplicative_5912_);
lean_dec(v___x_5911_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_6055_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
lean_object* v_toFunctor_5916_; lean_object* v_toSeq_5917_; lean_object* v_toSeqLeft_5918_; lean_object* v_toSeqRight_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_6053_; 
v_toFunctor_5916_ = lean_ctor_get(v_toApplicative_5912_, 0);
v_toSeq_5917_ = lean_ctor_get(v_toApplicative_5912_, 2);
v_toSeqLeft_5918_ = lean_ctor_get(v_toApplicative_5912_, 3);
v_toSeqRight_5919_ = lean_ctor_get(v_toApplicative_5912_, 4);
v_isSharedCheck_6053_ = !lean_is_exclusive(v_toApplicative_5912_);
if (v_isSharedCheck_6053_ == 0)
{
lean_object* v_unused_6054_; 
v_unused_6054_ = lean_ctor_get(v_toApplicative_5912_, 1);
lean_dec(v_unused_6054_);
v___x_5921_ = v_toApplicative_5912_;
v_isShared_5922_ = v_isSharedCheck_6053_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_toSeqRight_5919_);
lean_inc(v_toSeqLeft_5918_);
lean_inc(v_toSeq_5917_);
lean_inc(v_toFunctor_5916_);
lean_dec(v_toApplicative_5912_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_6053_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___f_5923_; lean_object* v___f_5924_; lean_object* v___f_5925_; lean_object* v___f_5926_; lean_object* v___x_5927_; lean_object* v___f_5928_; lean_object* v___f_5929_; lean_object* v___f_5930_; lean_object* v___x_5932_; 
v___f_5923_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5924_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5916_);
v___f_5925_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5925_, 0, v_toFunctor_5916_);
v___f_5926_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5926_, 0, v_toFunctor_5916_);
v___x_5927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___f_5925_);
lean_ctor_set(v___x_5927_, 1, v___f_5926_);
v___f_5928_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5928_, 0, v_toSeqRight_5919_);
v___f_5929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5929_, 0, v_toSeqLeft_5918_);
v___f_5930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5930_, 0, v_toSeq_5917_);
if (v_isShared_5922_ == 0)
{
lean_ctor_set(v___x_5921_, 4, v___f_5928_);
lean_ctor_set(v___x_5921_, 3, v___f_5929_);
lean_ctor_set(v___x_5921_, 2, v___f_5930_);
lean_ctor_set(v___x_5921_, 1, v___f_5923_);
lean_ctor_set(v___x_5921_, 0, v___x_5927_);
v___x_5932_ = v___x_5921_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_6052_; 
v_reuseFailAlloc_6052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6052_, 0, v___x_5927_);
lean_ctor_set(v_reuseFailAlloc_6052_, 1, v___f_5923_);
lean_ctor_set(v_reuseFailAlloc_6052_, 2, v___f_5930_);
lean_ctor_set(v_reuseFailAlloc_6052_, 3, v___f_5929_);
lean_ctor_set(v_reuseFailAlloc_6052_, 4, v___f_5928_);
v___x_5932_ = v_reuseFailAlloc_6052_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
lean_object* v___x_5934_; 
if (v_isShared_5915_ == 0)
{
lean_ctor_set(v___x_5914_, 1, v___f_5924_);
lean_ctor_set(v___x_5914_, 0, v___x_5932_);
v___x_5934_ = v___x_5914_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_6051_; 
v_reuseFailAlloc_6051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6051_, 0, v___x_5932_);
lean_ctor_set(v_reuseFailAlloc_6051_, 1, v___f_5924_);
v___x_5934_ = v_reuseFailAlloc_6051_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v_toMonadRef_5944_; lean_object* v___x_5945_; lean_object* v_name_5946_; lean_object* v_run_x27_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_6050_; 
v___x_5935_ = l_StateRefT_x27_instMonad___redArg(v___x_5934_);
v___x_5936_ = l_ReaderT_instMonad___redArg(v___x_5935_);
v___x_5937_ = l_StateRefT_x27_instMonad___redArg(v___x_5936_);
v___x_5938_ = l_ReaderT_instMonad___redArg(v___x_5937_);
v___x_5939_ = l_ReaderT_instMonad___redArg(v___x_5938_);
v___x_5940_ = l_StateRefT_x27_instMonad___redArg(v___x_5939_);
v___x_5941_ = l_ReaderT_instMonad___redArg(v___x_5940_);
v___x_5942_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5943_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_5944_ = lean_ctor_get(v___x_5943_, 0);
v___x_5945_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_name_5946_ = lean_ctor_get(v_pass_5882_, 0);
v_run_x27_5947_ = lean_ctor_get(v_pass_5882_, 1);
v_isSharedCheck_6050_ = !lean_is_exclusive(v_pass_5882_);
if (v_isSharedCheck_6050_ == 0)
{
v___x_5949_ = v_pass_5882_;
v_isShared_5950_ = v_isSharedCheck_6050_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_run_x27_5947_);
lean_inc(v_name_5946_);
lean_dec(v_pass_5882_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_6050_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
lean_object* v___x_5951_; lean_object* v_toCold_5952_; lean_object* v_options_5953_; uint8_t v_hasTrace_5954_; 
v___x_5951_ = l_Lean_KVMap_instValueBool;
v_toCold_5952_ = lean_ctor_get(v_a_5892_, 0);
v_options_5953_ = lean_ctor_get(v_toCold_5952_, 2);
v_hasTrace_5954_ = lean_ctor_get_uint8(v_options_5953_, sizeof(void*)*1);
if (v_hasTrace_5954_ == 0)
{
lean_object* v___x_5955_; 
lean_del_object(v___x_5949_);
lean_dec(v_name_5946_);
lean_dec_ref(v___x_5941_);
lean_inc(v_a_5893_);
lean_inc_ref(v_a_5892_);
lean_inc(v_a_5891_);
lean_inc_ref(v_a_5890_);
lean_inc(v_a_5889_);
lean_inc_ref(v_a_5888_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc(v_a_5884_);
lean_inc_ref(v_a_5883_);
v___x_5955_ = lean_apply_12(v_run_x27_5947_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, lean_box(0));
return v___x_5955_;
}
else
{
lean_object* v_inheritedTraceOptions_5956_; lean_object* v___f_5957_; lean_object* v___f_5958_; lean_object* v___f_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; uint8_t v___x_5963_; lean_object* v___y_5965_; lean_object* v___y_5966_; lean_object* v_a_5967_; lean_object* v___y_5983_; lean_object* v___y_5984_; lean_object* v_a_5985_; 
v_inheritedTraceOptions_5956_ = lean_ctor_get(v_toCold_5952_, 11);
v___f_5957_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5957_, 0, v_name_5946_);
v___f_5958_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_5959_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5960_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5961_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5962_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5963_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5956_, v_options_5953_, v___x_5962_);
if (v___x_5963_ == 0)
{
lean_object* v___x_6046_; lean_object* v___x_6047_; uint8_t v___x_6048_; 
v___x_6046_ = l_Lean_trace_profiler;
v___x_6047_ = l_Lean_Option_get___redArg(v___x_5951_, v_options_5953_, v___x_6046_);
v___x_6048_ = lean_unbox(v___x_6047_);
lean_dec(v___x_6047_);
if (v___x_6048_ == 0)
{
lean_object* v___x_6049_; 
lean_dec_ref(v___f_5957_);
lean_del_object(v___x_5949_);
lean_dec_ref(v___x_5941_);
lean_inc(v_a_5893_);
lean_inc_ref(v_a_5892_);
lean_inc(v_a_5891_);
lean_inc_ref(v_a_5890_);
lean_inc(v_a_5889_);
lean_inc_ref(v_a_5888_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc(v_a_5884_);
lean_inc_ref(v_a_5883_);
v___x_6049_ = lean_apply_12(v_run_x27_5947_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, lean_box(0));
return v___x_6049_;
}
else
{
goto v___jp_5995_;
}
}
else
{
goto v___jp_5995_;
}
v___jp_5964_:
{
lean_object* v___x_5968_; double v___x_5969_; double v___x_5970_; double v___x_5971_; double v___x_5972_; double v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5977_; 
v___x_5968_ = lean_io_mono_nanos_now();
v___x_5969_ = lean_float_of_nat(v___y_5966_);
v___x_5970_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5971_ = lean_float_div(v___x_5969_, v___x_5970_);
v___x_5972_ = lean_float_of_nat(v___x_5968_);
v___x_5973_ = lean_float_div(v___x_5972_, v___x_5970_);
v___x_5974_ = lean_box_float(v___x_5971_);
v___x_5975_ = lean_box_float(v___x_5973_);
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 1, v___x_5975_);
lean_ctor_set(v___x_5949_, 0, v___x_5974_);
v___x_5977_ = v___x_5949_;
goto v_reusejp_5976_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5981_, 1, v___x_5975_);
v___x_5977_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5976_;
}
v_reusejp_5976_:
{
lean_object* v___x_5978_; lean_object* v___x_28875__overap_5979_; lean_object* v___x_5980_; 
v___x_5978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5978_, 0, v_a_5967_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
lean_inc_ref(v_toMonadRef_5944_);
v___x_28875__overap_5979_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5941_, v___x_5942_, v_toMonadRef_5944_, v___f_5958_, lean_box(0), v___x_5945_, v___f_5959_, v___x_5960_, v_hasTrace_5954_, v___x_5961_, v_options_5953_, v___x_5963_, v___y_5965_, v___f_5957_, v___x_5978_);
lean_inc(v_a_5893_);
lean_inc_ref(v_a_5892_);
lean_inc(v_a_5891_);
lean_inc_ref(v_a_5890_);
lean_inc(v_a_5889_);
lean_inc_ref(v_a_5888_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc(v_a_5884_);
lean_inc_ref(v_a_5883_);
v___x_5980_ = lean_apply_12(v___x_28875__overap_5979_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, lean_box(0));
return v___x_5980_;
}
}
v___jp_5982_:
{
lean_object* v___x_5986_; double v___x_5987_; double v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_28896__overap_5993_; lean_object* v___x_5994_; 
v___x_5986_ = lean_io_get_num_heartbeats();
v___x_5987_ = lean_float_of_nat(v___y_5984_);
v___x_5988_ = lean_float_of_nat(v___x_5986_);
v___x_5989_ = lean_box_float(v___x_5987_);
v___x_5990_ = lean_box_float(v___x_5988_);
v___x_5991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5992_, 0, v_a_5985_);
lean_ctor_set(v___x_5992_, 1, v___x_5991_);
lean_inc_ref(v_toMonadRef_5944_);
v___x_28896__overap_5993_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5941_, v___x_5942_, v_toMonadRef_5944_, v___f_5958_, lean_box(0), v___x_5945_, v___f_5959_, v___x_5960_, v_hasTrace_5954_, v___x_5961_, v_options_5953_, v___x_5963_, v___y_5983_, v___f_5957_, v___x_5992_);
lean_inc(v_a_5893_);
lean_inc_ref(v_a_5892_);
lean_inc(v_a_5891_);
lean_inc_ref(v_a_5890_);
lean_inc(v_a_5889_);
lean_inc_ref(v_a_5888_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc(v_a_5884_);
lean_inc_ref(v_a_5883_);
v___x_5994_ = lean_apply_12(v___x_28896__overap_5993_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, lean_box(0));
return v___x_5994_;
}
v___jp_5995_:
{
lean_object* v___x_28853__overap_5996_; lean_object* v___x_5997_; 
lean_inc_ref(v___x_5941_);
v___x_28853__overap_5996_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5941_, v___x_5942_);
lean_inc(v_a_5893_);
lean_inc_ref(v_a_5892_);
lean_inc(v_a_5891_);
lean_inc_ref(v_a_5890_);
lean_inc(v_a_5889_);
lean_inc_ref(v_a_5888_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc(v_a_5884_);
lean_inc_ref(v_a_5883_);
v___x_5997_ = lean_apply_12(v___x_28853__overap_5996_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, lean_box(0));
if (lean_obj_tag(v___x_5997_) == 0)
{
lean_object* v_a_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; uint8_t v___x_6001_; 
v_a_5998_ = lean_ctor_get(v___x_5997_, 0);
lean_inc(v_a_5998_);
lean_dec_ref_known(v___x_5997_, 1);
v___x_5999_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6000_ = l_Lean_Option_get___redArg(v___x_5951_, v_options_5953_, v___x_5999_);
v___x_6001_ = lean_unbox(v___x_6000_);
lean_dec(v___x_6000_);
if (v___x_6001_ == 0)
{
lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6002_ = lean_io_mono_nanos_now();
lean_inc(v_a_5893_);
lean_inc_ref(v_a_5892_);
lean_inc(v_a_5891_);
lean_inc_ref(v_a_5890_);
lean_inc(v_a_5889_);
lean_inc_ref(v_a_5888_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc(v_a_5884_);
lean_inc_ref(v_a_5883_);
v___x_6003_ = lean_apply_12(v_run_x27_5947_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, lean_box(0));
if (lean_obj_tag(v___x_6003_) == 0)
{
lean_object* v_a_6004_; lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6011_; 
v_a_6004_ = lean_ctor_get(v___x_6003_, 0);
v_isSharedCheck_6011_ = !lean_is_exclusive(v___x_6003_);
if (v_isSharedCheck_6011_ == 0)
{
v___x_6006_ = v___x_6003_;
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_a_6004_);
lean_dec(v___x_6003_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v___x_6009_; 
if (v_isShared_6007_ == 0)
{
lean_ctor_set_tag(v___x_6006_, 1);
v___x_6009_ = v___x_6006_;
goto v_reusejp_6008_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
v___x_6009_ = v_reuseFailAlloc_6010_;
goto v_reusejp_6008_;
}
v_reusejp_6008_:
{
v___y_5965_ = v_a_5998_;
v___y_5966_ = v___x_6002_;
v_a_5967_ = v___x_6009_;
goto v___jp_5964_;
}
}
}
else
{
lean_object* v_a_6012_; lean_object* v___x_6014_; uint8_t v_isShared_6015_; uint8_t v_isSharedCheck_6019_; 
v_a_6012_ = lean_ctor_get(v___x_6003_, 0);
v_isSharedCheck_6019_ = !lean_is_exclusive(v___x_6003_);
if (v_isSharedCheck_6019_ == 0)
{
v___x_6014_ = v___x_6003_;
v_isShared_6015_ = v_isSharedCheck_6019_;
goto v_resetjp_6013_;
}
else
{
lean_inc(v_a_6012_);
lean_dec(v___x_6003_);
v___x_6014_ = lean_box(0);
v_isShared_6015_ = v_isSharedCheck_6019_;
goto v_resetjp_6013_;
}
v_resetjp_6013_:
{
lean_object* v___x_6017_; 
if (v_isShared_6015_ == 0)
{
lean_ctor_set_tag(v___x_6014_, 0);
v___x_6017_ = v___x_6014_;
goto v_reusejp_6016_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_a_6012_);
v___x_6017_ = v_reuseFailAlloc_6018_;
goto v_reusejp_6016_;
}
v_reusejp_6016_:
{
v___y_5965_ = v_a_5998_;
v___y_5966_ = v___x_6002_;
v_a_5967_ = v___x_6017_;
goto v___jp_5964_;
}
}
}
}
else
{
lean_object* v___x_6020_; lean_object* v___x_6021_; 
lean_del_object(v___x_5949_);
v___x_6020_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5893_);
lean_inc_ref(v_a_5892_);
lean_inc(v_a_5891_);
lean_inc_ref(v_a_5890_);
lean_inc(v_a_5889_);
lean_inc_ref(v_a_5888_);
lean_inc(v_a_5887_);
lean_inc_ref(v_a_5886_);
lean_inc(v_a_5885_);
lean_inc(v_a_5884_);
lean_inc_ref(v_a_5883_);
v___x_6021_ = lean_apply_12(v_run_x27_5947_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, lean_box(0));
if (lean_obj_tag(v___x_6021_) == 0)
{
lean_object* v_a_6022_; lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6029_; 
v_a_6022_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6029_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6029_ == 0)
{
v___x_6024_ = v___x_6021_;
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
else
{
lean_inc(v_a_6022_);
lean_dec(v___x_6021_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6027_; 
if (v_isShared_6025_ == 0)
{
lean_ctor_set_tag(v___x_6024_, 1);
v___x_6027_ = v___x_6024_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6028_; 
v_reuseFailAlloc_6028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
v___x_6027_ = v_reuseFailAlloc_6028_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
v___y_5983_ = v_a_5998_;
v___y_5984_ = v___x_6020_;
v_a_5985_ = v___x_6027_;
goto v___jp_5982_;
}
}
}
else
{
lean_object* v_a_6030_; lean_object* v___x_6032_; uint8_t v_isShared_6033_; uint8_t v_isSharedCheck_6037_; 
v_a_6030_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6037_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6037_ == 0)
{
v___x_6032_ = v___x_6021_;
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
else
{
lean_inc(v_a_6030_);
lean_dec(v___x_6021_);
v___x_6032_ = lean_box(0);
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
v_resetjp_6031_:
{
lean_object* v___x_6035_; 
if (v_isShared_6033_ == 0)
{
lean_ctor_set_tag(v___x_6032_, 0);
v___x_6035_ = v___x_6032_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_a_6030_);
v___x_6035_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
v___y_5983_ = v_a_5998_;
v___y_5984_ = v___x_6020_;
v_a_5985_ = v___x_6035_;
goto v___jp_5982_;
}
}
}
}
}
else
{
lean_object* v_a_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6045_; 
lean_dec_ref(v___f_5957_);
lean_del_object(v___x_5949_);
lean_dec_ref(v_run_x27_5947_);
lean_dec_ref(v___x_5941_);
v_a_6038_ = lean_ctor_get(v___x_5997_, 0);
v_isSharedCheck_6045_ = !lean_is_exclusive(v___x_5997_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6040_ = v___x_5997_;
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_a_6038_);
lean_dec(v___x_5997_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
v_resetjp_6039_:
{
lean_object* v___x_6043_; 
if (v_isShared_6041_ == 0)
{
v___x_6043_ = v___x_6040_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v_a_6038_);
v___x_6043_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
return v___x_6043_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_){
_start:
{
lean_object* v_res_6070_; 
v_res_6070_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6057_, v_a_6058_, v_a_6059_, v_a_6060_, v_a_6061_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_, v_a_6066_, v_a_6067_, v_a_6068_);
lean_dec(v_a_6068_);
lean_dec_ref(v_a_6067_);
lean_dec(v_a_6066_);
lean_dec_ref(v_a_6065_);
lean_dec(v_a_6064_);
lean_dec_ref(v_a_6063_);
lean_dec(v_a_6062_);
lean_dec_ref(v_a_6061_);
lean_dec(v_a_6060_);
lean_dec(v_a_6059_);
lean_dec_ref(v_a_6058_);
return v_res_6070_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6071_ = lean_unsigned_to_nat(32u);
v___x_6072_ = lean_mk_empty_array_with_capacity(v___x_6071_);
v___x_6073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
return v___x_6073_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6074_ = ((size_t)5ULL);
v___x_6075_ = lean_unsigned_to_nat(0u);
v___x_6076_ = lean_unsigned_to_nat(32u);
v___x_6077_ = lean_mk_empty_array_with_capacity(v___x_6076_);
v___x_6078_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6079_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6079_, 0, v___x_6078_);
lean_ctor_set(v___x_6079_, 1, v___x_6077_);
lean_ctor_set(v___x_6079_, 2, v___x_6075_);
lean_ctor_set(v___x_6079_, 3, v___x_6075_);
lean_ctor_set_usize(v___x_6079_, 4, v___x_6074_);
return v___x_6079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6080_){
_start:
{
lean_object* v___x_6082_; lean_object* v_traceState_6083_; lean_object* v_traces_6084_; lean_object* v___x_6085_; lean_object* v_traceState_6086_; lean_object* v_env_6087_; lean_object* v_nextMacroScope_6088_; lean_object* v_ngen_6089_; lean_object* v_auxDeclNGen_6090_; lean_object* v_cache_6091_; lean_object* v_recordedDeps_6092_; lean_object* v_messages_6093_; lean_object* v_infoState_6094_; lean_object* v_snapshotTasks_6095_; lean_object* v___x_6097_; uint8_t v_isShared_6098_; uint8_t v_isSharedCheck_6114_; 
v___x_6082_ = lean_st_ref_get(v___y_6080_);
v_traceState_6083_ = lean_ctor_get(v___x_6082_, 4);
lean_inc_ref(v_traceState_6083_);
lean_dec(v___x_6082_);
v_traces_6084_ = lean_ctor_get(v_traceState_6083_, 0);
lean_inc_ref(v_traces_6084_);
lean_dec_ref(v_traceState_6083_);
v___x_6085_ = lean_st_ref_take(v___y_6080_);
v_traceState_6086_ = lean_ctor_get(v___x_6085_, 4);
v_env_6087_ = lean_ctor_get(v___x_6085_, 0);
v_nextMacroScope_6088_ = lean_ctor_get(v___x_6085_, 1);
v_ngen_6089_ = lean_ctor_get(v___x_6085_, 2);
v_auxDeclNGen_6090_ = lean_ctor_get(v___x_6085_, 3);
v_cache_6091_ = lean_ctor_get(v___x_6085_, 5);
v_recordedDeps_6092_ = lean_ctor_get(v___x_6085_, 6);
v_messages_6093_ = lean_ctor_get(v___x_6085_, 7);
v_infoState_6094_ = lean_ctor_get(v___x_6085_, 8);
v_snapshotTasks_6095_ = lean_ctor_get(v___x_6085_, 9);
v_isSharedCheck_6114_ = !lean_is_exclusive(v___x_6085_);
if (v_isSharedCheck_6114_ == 0)
{
v___x_6097_ = v___x_6085_;
v_isShared_6098_ = v_isSharedCheck_6114_;
goto v_resetjp_6096_;
}
else
{
lean_inc(v_snapshotTasks_6095_);
lean_inc(v_infoState_6094_);
lean_inc(v_messages_6093_);
lean_inc(v_recordedDeps_6092_);
lean_inc(v_cache_6091_);
lean_inc(v_traceState_6086_);
lean_inc(v_auxDeclNGen_6090_);
lean_inc(v_ngen_6089_);
lean_inc(v_nextMacroScope_6088_);
lean_inc(v_env_6087_);
lean_dec(v___x_6085_);
v___x_6097_ = lean_box(0);
v_isShared_6098_ = v_isSharedCheck_6114_;
goto v_resetjp_6096_;
}
v_resetjp_6096_:
{
uint64_t v_tid_6099_; lean_object* v___x_6101_; uint8_t v_isShared_6102_; uint8_t v_isSharedCheck_6112_; 
v_tid_6099_ = lean_ctor_get_uint64(v_traceState_6086_, sizeof(void*)*1);
v_isSharedCheck_6112_ = !lean_is_exclusive(v_traceState_6086_);
if (v_isSharedCheck_6112_ == 0)
{
lean_object* v_unused_6113_; 
v_unused_6113_ = lean_ctor_get(v_traceState_6086_, 0);
lean_dec(v_unused_6113_);
v___x_6101_ = v_traceState_6086_;
v_isShared_6102_ = v_isSharedCheck_6112_;
goto v_resetjp_6100_;
}
else
{
lean_dec(v_traceState_6086_);
v___x_6101_ = lean_box(0);
v_isShared_6102_ = v_isSharedCheck_6112_;
goto v_resetjp_6100_;
}
v_resetjp_6100_:
{
lean_object* v___x_6103_; lean_object* v___x_6105_; 
v___x_6103_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6102_ == 0)
{
lean_ctor_set(v___x_6101_, 0, v___x_6103_);
v___x_6105_ = v___x_6101_;
goto v_reusejp_6104_;
}
else
{
lean_object* v_reuseFailAlloc_6111_; 
v_reuseFailAlloc_6111_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6111_, 0, v___x_6103_);
lean_ctor_set_uint64(v_reuseFailAlloc_6111_, sizeof(void*)*1, v_tid_6099_);
v___x_6105_ = v_reuseFailAlloc_6111_;
goto v_reusejp_6104_;
}
v_reusejp_6104_:
{
lean_object* v___x_6107_; 
if (v_isShared_6098_ == 0)
{
lean_ctor_set(v___x_6097_, 4, v___x_6105_);
v___x_6107_ = v___x_6097_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_env_6087_);
lean_ctor_set(v_reuseFailAlloc_6110_, 1, v_nextMacroScope_6088_);
lean_ctor_set(v_reuseFailAlloc_6110_, 2, v_ngen_6089_);
lean_ctor_set(v_reuseFailAlloc_6110_, 3, v_auxDeclNGen_6090_);
lean_ctor_set(v_reuseFailAlloc_6110_, 4, v___x_6105_);
lean_ctor_set(v_reuseFailAlloc_6110_, 5, v_cache_6091_);
lean_ctor_set(v_reuseFailAlloc_6110_, 6, v_recordedDeps_6092_);
lean_ctor_set(v_reuseFailAlloc_6110_, 7, v_messages_6093_);
lean_ctor_set(v_reuseFailAlloc_6110_, 8, v_infoState_6094_);
lean_ctor_set(v_reuseFailAlloc_6110_, 9, v_snapshotTasks_6095_);
v___x_6107_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
lean_object* v___x_6108_; lean_object* v___x_6109_; 
v___x_6108_ = lean_st_ref_put(v___y_6080_, v___x_6107_);
v___x_6109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6109_, 0, v_traces_6084_);
return v___x_6109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6115_, lean_object* v___y_6116_){
_start:
{
lean_object* v_res_6117_; 
v_res_6117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6115_);
lean_dec(v___y_6115_);
return v_res_6117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6128_);
return v___x_6130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_){
_start:
{
lean_object* v_res_6143_; 
v_res_6143_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_);
lean_dec(v___y_6141_);
lean_dec_ref(v___y_6140_);
lean_dec(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v___y_6137_);
lean_dec_ref(v___y_6136_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
lean_dec(v___y_6133_);
lean_dec(v___y_6132_);
lean_dec_ref(v___y_6131_);
return v_res_6143_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6144_, lean_object* v_opt_6145_){
_start:
{
lean_object* v_name_6146_; lean_object* v_defValue_6147_; lean_object* v_map_6148_; lean_object* v___x_6149_; 
v_name_6146_ = lean_ctor_get(v_opt_6145_, 0);
v_defValue_6147_ = lean_ctor_get(v_opt_6145_, 1);
v_map_6148_ = lean_ctor_get(v_opts_6144_, 0);
v___x_6149_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6148_, v_name_6146_);
if (lean_obj_tag(v___x_6149_) == 0)
{
uint8_t v___x_6150_; 
v___x_6150_ = lean_unbox(v_defValue_6147_);
return v___x_6150_;
}
else
{
lean_object* v_val_6151_; 
v_val_6151_ = lean_ctor_get(v___x_6149_, 0);
lean_inc(v_val_6151_);
lean_dec_ref_known(v___x_6149_, 1);
if (lean_obj_tag(v_val_6151_) == 1)
{
uint8_t v_v_6152_; 
v_v_6152_ = lean_ctor_get_uint8(v_val_6151_, 0);
lean_dec_ref_known(v_val_6151_, 0);
return v_v_6152_;
}
else
{
uint8_t v___x_6153_; 
lean_dec(v_val_6151_);
v___x_6153_ = lean_unbox(v_defValue_6147_);
return v___x_6153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6154_, lean_object* v_opt_6155_){
_start:
{
uint8_t v_res_6156_; lean_object* v_r_6157_; 
v_res_6156_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6154_, v_opt_6155_);
lean_dec_ref(v_opt_6155_);
lean_dec_ref(v_opts_6154_);
v_r_6157_ = lean_box(v_res_6156_);
return v_r_6157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6158_, lean_object* v_msg_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_){
_start:
{
lean_object* v_ref_6165_; lean_object* v___x_6166_; lean_object* v_a_6167_; lean_object* v___x_6169_; uint8_t v_isShared_6170_; uint8_t v_isSharedCheck_6212_; 
v_ref_6165_ = lean_ctor_get(v___y_6162_, 2);
v___x_6166_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_);
v_a_6167_ = lean_ctor_get(v___x_6166_, 0);
v_isSharedCheck_6212_ = !lean_is_exclusive(v___x_6166_);
if (v_isSharedCheck_6212_ == 0)
{
v___x_6169_ = v___x_6166_;
v_isShared_6170_ = v_isSharedCheck_6212_;
goto v_resetjp_6168_;
}
else
{
lean_inc(v_a_6167_);
lean_dec(v___x_6166_);
v___x_6169_ = lean_box(0);
v_isShared_6170_ = v_isSharedCheck_6212_;
goto v_resetjp_6168_;
}
v_resetjp_6168_:
{
lean_object* v___x_6171_; lean_object* v_traceState_6172_; lean_object* v_env_6173_; lean_object* v_nextMacroScope_6174_; lean_object* v_ngen_6175_; lean_object* v_auxDeclNGen_6176_; lean_object* v_cache_6177_; lean_object* v_recordedDeps_6178_; lean_object* v_messages_6179_; lean_object* v_infoState_6180_; lean_object* v_snapshotTasks_6181_; lean_object* v___x_6183_; uint8_t v_isShared_6184_; uint8_t v_isSharedCheck_6211_; 
v___x_6171_ = lean_st_ref_take(v___y_6163_);
v_traceState_6172_ = lean_ctor_get(v___x_6171_, 4);
v_env_6173_ = lean_ctor_get(v___x_6171_, 0);
v_nextMacroScope_6174_ = lean_ctor_get(v___x_6171_, 1);
v_ngen_6175_ = lean_ctor_get(v___x_6171_, 2);
v_auxDeclNGen_6176_ = lean_ctor_get(v___x_6171_, 3);
v_cache_6177_ = lean_ctor_get(v___x_6171_, 5);
v_recordedDeps_6178_ = lean_ctor_get(v___x_6171_, 6);
v_messages_6179_ = lean_ctor_get(v___x_6171_, 7);
v_infoState_6180_ = lean_ctor_get(v___x_6171_, 8);
v_snapshotTasks_6181_ = lean_ctor_get(v___x_6171_, 9);
v_isSharedCheck_6211_ = !lean_is_exclusive(v___x_6171_);
if (v_isSharedCheck_6211_ == 0)
{
v___x_6183_ = v___x_6171_;
v_isShared_6184_ = v_isSharedCheck_6211_;
goto v_resetjp_6182_;
}
else
{
lean_inc(v_snapshotTasks_6181_);
lean_inc(v_infoState_6180_);
lean_inc(v_messages_6179_);
lean_inc(v_recordedDeps_6178_);
lean_inc(v_cache_6177_);
lean_inc(v_traceState_6172_);
lean_inc(v_auxDeclNGen_6176_);
lean_inc(v_ngen_6175_);
lean_inc(v_nextMacroScope_6174_);
lean_inc(v_env_6173_);
lean_dec(v___x_6171_);
v___x_6183_ = lean_box(0);
v_isShared_6184_ = v_isSharedCheck_6211_;
goto v_resetjp_6182_;
}
v_resetjp_6182_:
{
uint64_t v_tid_6185_; lean_object* v_traces_6186_; lean_object* v___x_6188_; uint8_t v_isShared_6189_; uint8_t v_isSharedCheck_6210_; 
v_tid_6185_ = lean_ctor_get_uint64(v_traceState_6172_, sizeof(void*)*1);
v_traces_6186_ = lean_ctor_get(v_traceState_6172_, 0);
v_isSharedCheck_6210_ = !lean_is_exclusive(v_traceState_6172_);
if (v_isSharedCheck_6210_ == 0)
{
v___x_6188_ = v_traceState_6172_;
v_isShared_6189_ = v_isSharedCheck_6210_;
goto v_resetjp_6187_;
}
else
{
lean_inc(v_traces_6186_);
lean_dec(v_traceState_6172_);
v___x_6188_ = lean_box(0);
v_isShared_6189_ = v_isSharedCheck_6210_;
goto v_resetjp_6187_;
}
v_resetjp_6187_:
{
lean_object* v___x_6190_; lean_object* v___x_6191_; double v___x_6192_; uint8_t v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6201_; 
v___x_6190_ = lean_box(0);
v___x_6191_ = lean_box(0);
v___x_6192_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6193_ = 0;
v___x_6194_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6195_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6195_, 0, v_cls_6158_);
lean_ctor_set(v___x_6195_, 1, v___x_6191_);
lean_ctor_set(v___x_6195_, 2, v___x_6194_);
lean_ctor_set_float(v___x_6195_, sizeof(void*)*3, v___x_6192_);
lean_ctor_set_float(v___x_6195_, sizeof(void*)*3 + 8, v___x_6192_);
lean_ctor_set_uint8(v___x_6195_, sizeof(void*)*3 + 16, v___x_6193_);
v___x_6196_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6197_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6195_);
lean_ctor_set(v___x_6197_, 1, v_a_6167_);
lean_ctor_set(v___x_6197_, 2, v___x_6196_);
lean_inc(v_ref_6165_);
v___x_6198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6198_, 0, v_ref_6165_);
lean_ctor_set(v___x_6198_, 1, v___x_6197_);
v___x_6199_ = l_Lean_PersistentArray_push___redArg(v_traces_6186_, v___x_6198_);
if (v_isShared_6189_ == 0)
{
lean_ctor_set(v___x_6188_, 0, v___x_6199_);
v___x_6201_ = v___x_6188_;
goto v_reusejp_6200_;
}
else
{
lean_object* v_reuseFailAlloc_6209_; 
v_reuseFailAlloc_6209_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6209_, 0, v___x_6199_);
lean_ctor_set_uint64(v_reuseFailAlloc_6209_, sizeof(void*)*1, v_tid_6185_);
v___x_6201_ = v_reuseFailAlloc_6209_;
goto v_reusejp_6200_;
}
v_reusejp_6200_:
{
lean_object* v___x_6203_; 
if (v_isShared_6184_ == 0)
{
lean_ctor_set(v___x_6183_, 4, v___x_6201_);
v___x_6203_ = v___x_6183_;
goto v_reusejp_6202_;
}
else
{
lean_object* v_reuseFailAlloc_6208_; 
v_reuseFailAlloc_6208_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_env_6173_);
lean_ctor_set(v_reuseFailAlloc_6208_, 1, v_nextMacroScope_6174_);
lean_ctor_set(v_reuseFailAlloc_6208_, 2, v_ngen_6175_);
lean_ctor_set(v_reuseFailAlloc_6208_, 3, v_auxDeclNGen_6176_);
lean_ctor_set(v_reuseFailAlloc_6208_, 4, v___x_6201_);
lean_ctor_set(v_reuseFailAlloc_6208_, 5, v_cache_6177_);
lean_ctor_set(v_reuseFailAlloc_6208_, 6, v_recordedDeps_6178_);
lean_ctor_set(v_reuseFailAlloc_6208_, 7, v_messages_6179_);
lean_ctor_set(v_reuseFailAlloc_6208_, 8, v_infoState_6180_);
lean_ctor_set(v_reuseFailAlloc_6208_, 9, v_snapshotTasks_6181_);
v___x_6203_ = v_reuseFailAlloc_6208_;
goto v_reusejp_6202_;
}
v_reusejp_6202_:
{
lean_object* v___x_6204_; lean_object* v___x_6206_; 
v___x_6204_ = lean_st_ref_put(v___y_6163_, v___x_6203_);
if (v_isShared_6170_ == 0)
{
lean_ctor_set(v___x_6169_, 0, v___x_6190_);
v___x_6206_ = v___x_6169_;
goto v_reusejp_6205_;
}
else
{
lean_object* v_reuseFailAlloc_6207_; 
v_reuseFailAlloc_6207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6207_, 0, v___x_6190_);
v___x_6206_ = v_reuseFailAlloc_6207_;
goto v_reusejp_6205_;
}
v_reusejp_6205_:
{
return v___x_6206_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6213_, lean_object* v_msg_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_){
_start:
{
lean_object* v_res_6220_; 
v_res_6220_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6213_, v_msg_6214_, v___y_6215_, v___y_6216_, v___y_6217_, v___y_6218_);
lean_dec(v___y_6218_);
lean_dec_ref(v___y_6217_);
lean_dec(v___y_6216_);
lean_dec_ref(v___y_6215_);
return v_res_6220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6221_){
_start:
{
if (lean_obj_tag(v_e_6221_) == 0)
{
uint8_t v___x_6222_; 
v___x_6222_ = 2;
return v___x_6222_;
}
else
{
lean_object* v_a_6223_; uint8_t v___x_6224_; 
v_a_6223_ = lean_ctor_get(v_e_6221_, 0);
v___x_6224_ = lean_unbox(v_a_6223_);
if (v___x_6224_ == 0)
{
uint8_t v___x_6225_; 
v___x_6225_ = 1;
return v___x_6225_;
}
else
{
uint8_t v___x_6226_; 
v___x_6226_ = 0;
return v___x_6226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6227_){
_start:
{
uint8_t v_res_6228_; lean_object* v_r_6229_; 
v_res_6228_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6227_);
lean_dec_ref(v_e_6227_);
v_r_6229_ = lean_box(v_res_6228_);
return v_r_6229_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6230_){
_start:
{
if (lean_obj_tag(v_x_6230_) == 0)
{
lean_object* v_a_6232_; lean_object* v___x_6234_; uint8_t v_isShared_6235_; uint8_t v_isSharedCheck_6239_; 
v_a_6232_ = lean_ctor_get(v_x_6230_, 0);
v_isSharedCheck_6239_ = !lean_is_exclusive(v_x_6230_);
if (v_isSharedCheck_6239_ == 0)
{
v___x_6234_ = v_x_6230_;
v_isShared_6235_ = v_isSharedCheck_6239_;
goto v_resetjp_6233_;
}
else
{
lean_inc(v_a_6232_);
lean_dec(v_x_6230_);
v___x_6234_ = lean_box(0);
v_isShared_6235_ = v_isSharedCheck_6239_;
goto v_resetjp_6233_;
}
v_resetjp_6233_:
{
lean_object* v___x_6237_; 
if (v_isShared_6235_ == 0)
{
lean_ctor_set_tag(v___x_6234_, 1);
v___x_6237_ = v___x_6234_;
goto v_reusejp_6236_;
}
else
{
lean_object* v_reuseFailAlloc_6238_; 
v_reuseFailAlloc_6238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
v___x_6237_ = v_reuseFailAlloc_6238_;
goto v_reusejp_6236_;
}
v_reusejp_6236_:
{
return v___x_6237_;
}
}
}
else
{
lean_object* v_a_6240_; lean_object* v___x_6242_; uint8_t v_isShared_6243_; uint8_t v_isSharedCheck_6247_; 
v_a_6240_ = lean_ctor_get(v_x_6230_, 0);
v_isSharedCheck_6247_ = !lean_is_exclusive(v_x_6230_);
if (v_isSharedCheck_6247_ == 0)
{
v___x_6242_ = v_x_6230_;
v_isShared_6243_ = v_isSharedCheck_6247_;
goto v_resetjp_6241_;
}
else
{
lean_inc(v_a_6240_);
lean_dec(v_x_6230_);
v___x_6242_ = lean_box(0);
v_isShared_6243_ = v_isSharedCheck_6247_;
goto v_resetjp_6241_;
}
v_resetjp_6241_:
{
lean_object* v___x_6245_; 
if (v_isShared_6243_ == 0)
{
lean_ctor_set_tag(v___x_6242_, 0);
v___x_6245_ = v___x_6242_;
goto v_reusejp_6244_;
}
else
{
lean_object* v_reuseFailAlloc_6246_; 
v_reuseFailAlloc_6246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6246_, 0, v_a_6240_);
v___x_6245_ = v_reuseFailAlloc_6246_;
goto v_reusejp_6244_;
}
v_reusejp_6244_:
{
return v___x_6245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6248_, lean_object* v___y_6249_){
_start:
{
lean_object* v_res_6250_; 
v_res_6250_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6248_);
return v_res_6250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6251_, lean_object* v_opt_6252_){
_start:
{
lean_object* v_name_6253_; lean_object* v_defValue_6254_; lean_object* v_map_6255_; lean_object* v___x_6256_; 
v_name_6253_ = lean_ctor_get(v_opt_6252_, 0);
v_defValue_6254_ = lean_ctor_get(v_opt_6252_, 1);
v_map_6255_ = lean_ctor_get(v_opts_6251_, 0);
v___x_6256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6255_, v_name_6253_);
if (lean_obj_tag(v___x_6256_) == 0)
{
lean_inc(v_defValue_6254_);
return v_defValue_6254_;
}
else
{
lean_object* v_val_6257_; 
v_val_6257_ = lean_ctor_get(v___x_6256_, 0);
lean_inc(v_val_6257_);
lean_dec_ref_known(v___x_6256_, 1);
if (lean_obj_tag(v_val_6257_) == 3)
{
lean_object* v_v_6258_; 
v_v_6258_ = lean_ctor_get(v_val_6257_, 0);
lean_inc(v_v_6258_);
lean_dec_ref_known(v_val_6257_, 1);
return v_v_6258_;
}
else
{
lean_dec(v_val_6257_);
lean_inc(v_defValue_6254_);
return v_defValue_6254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6259_, lean_object* v_opt_6260_){
_start:
{
lean_object* v_res_6261_; 
v_res_6261_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6259_, v_opt_6260_);
lean_dec_ref(v_opt_6260_);
lean_dec_ref(v_opts_6259_);
return v_res_6261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6262_, size_t v_i_6263_, lean_object* v_bs_6264_){
_start:
{
uint8_t v___x_6265_; 
v___x_6265_ = lean_usize_dec_lt(v_i_6263_, v_sz_6262_);
if (v___x_6265_ == 0)
{
return v_bs_6264_;
}
else
{
lean_object* v_v_6266_; lean_object* v_msg_6267_; lean_object* v___x_6268_; lean_object* v_bs_x27_6269_; size_t v___x_6270_; size_t v___x_6271_; lean_object* v___x_6272_; 
v_v_6266_ = lean_array_uget_borrowed(v_bs_6264_, v_i_6263_);
v_msg_6267_ = lean_ctor_get(v_v_6266_, 1);
lean_inc_ref(v_msg_6267_);
v___x_6268_ = lean_unsigned_to_nat(0u);
v_bs_x27_6269_ = lean_array_uset(v_bs_6264_, v_i_6263_, v___x_6268_);
v___x_6270_ = ((size_t)1ULL);
v___x_6271_ = lean_usize_add(v_i_6263_, v___x_6270_);
v___x_6272_ = lean_array_uset(v_bs_x27_6269_, v_i_6263_, v_msg_6267_);
v_i_6263_ = v___x_6271_;
v_bs_6264_ = v___x_6272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6274_, lean_object* v_i_6275_, lean_object* v_bs_6276_){
_start:
{
size_t v_sz_boxed_6277_; size_t v_i_boxed_6278_; lean_object* v_res_6279_; 
v_sz_boxed_6277_ = lean_unbox_usize(v_sz_6274_);
lean_dec(v_sz_6274_);
v_i_boxed_6278_ = lean_unbox_usize(v_i_6275_);
lean_dec(v_i_6275_);
v_res_6279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6277_, v_i_boxed_6278_, v_bs_6276_);
return v_res_6279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6280_, lean_object* v_data_6281_, lean_object* v_ref_6282_, lean_object* v_msg_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_){
_start:
{
lean_object* v_toCold_6289_; lean_object* v_currRecDepth_6290_; lean_object* v_ref_6291_; uint16_t v_optionFlags_6292_; uint8_t v_suppressElabErrors_6293_; uint8_t v_isRecordingDeps_6294_; lean_object* v_ref_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v_traceState_6298_; lean_object* v_traces_6299_; lean_object* v___x_6300_; size_t v_sz_6301_; size_t v___x_6302_; lean_object* v___x_6303_; lean_object* v_msg_6304_; lean_object* v___x_6305_; lean_object* v_a_6306_; lean_object* v___x_6308_; uint8_t v_isShared_6309_; uint8_t v_isSharedCheck_6344_; 
v_toCold_6289_ = lean_ctor_get(v___y_6286_, 0);
v_currRecDepth_6290_ = lean_ctor_get(v___y_6286_, 1);
v_ref_6291_ = lean_ctor_get(v___y_6286_, 2);
v_optionFlags_6292_ = lean_ctor_get_uint16(v___y_6286_, sizeof(void*)*3);
v_suppressElabErrors_6293_ = lean_ctor_get_uint8(v___y_6286_, sizeof(void*)*3 + 2);
v_isRecordingDeps_6294_ = lean_ctor_get_uint8(v___y_6286_, sizeof(void*)*3 + 3);
v_ref_6295_ = l_Lean_replaceRef(v_ref_6282_, v_ref_6291_);
lean_inc(v_currRecDepth_6290_);
lean_inc_ref(v_toCold_6289_);
v___x_6296_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_6296_, 0, v_toCold_6289_);
lean_ctor_set(v___x_6296_, 1, v_currRecDepth_6290_);
lean_ctor_set(v___x_6296_, 2, v_ref_6295_);
lean_ctor_set_uint16(v___x_6296_, sizeof(void*)*3, v_optionFlags_6292_);
lean_ctor_set_uint8(v___x_6296_, sizeof(void*)*3 + 2, v_suppressElabErrors_6293_);
lean_ctor_set_uint8(v___x_6296_, sizeof(void*)*3 + 3, v_isRecordingDeps_6294_);
v___x_6297_ = lean_st_ref_get(v___y_6287_);
v_traceState_6298_ = lean_ctor_get(v___x_6297_, 4);
lean_inc_ref(v_traceState_6298_);
lean_dec(v___x_6297_);
v_traces_6299_ = lean_ctor_get(v_traceState_6298_, 0);
lean_inc_ref(v_traces_6299_);
lean_dec_ref(v_traceState_6298_);
v___x_6300_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6299_);
lean_dec_ref(v_traces_6299_);
v_sz_6301_ = lean_array_size(v___x_6300_);
v___x_6302_ = ((size_t)0ULL);
v___x_6303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6301_, v___x_6302_, v___x_6300_);
v_msg_6304_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6304_, 0, v_data_6281_);
lean_ctor_set(v_msg_6304_, 1, v_msg_6283_);
lean_ctor_set(v_msg_6304_, 2, v___x_6303_);
v___x_6305_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6304_, v___y_6284_, v___y_6285_, v___x_6296_, v___y_6287_);
lean_dec_ref_known(v___x_6296_, 3);
v_a_6306_ = lean_ctor_get(v___x_6305_, 0);
v_isSharedCheck_6344_ = !lean_is_exclusive(v___x_6305_);
if (v_isSharedCheck_6344_ == 0)
{
v___x_6308_ = v___x_6305_;
v_isShared_6309_ = v_isSharedCheck_6344_;
goto v_resetjp_6307_;
}
else
{
lean_inc(v_a_6306_);
lean_dec(v___x_6305_);
v___x_6308_ = lean_box(0);
v_isShared_6309_ = v_isSharedCheck_6344_;
goto v_resetjp_6307_;
}
v_resetjp_6307_:
{
lean_object* v___x_6310_; lean_object* v_traceState_6311_; lean_object* v_env_6312_; lean_object* v_nextMacroScope_6313_; lean_object* v_ngen_6314_; lean_object* v_auxDeclNGen_6315_; lean_object* v_cache_6316_; lean_object* v_recordedDeps_6317_; lean_object* v_messages_6318_; lean_object* v_infoState_6319_; lean_object* v_snapshotTasks_6320_; lean_object* v___x_6322_; uint8_t v_isShared_6323_; uint8_t v_isSharedCheck_6343_; 
v___x_6310_ = lean_st_ref_take(v___y_6287_);
v_traceState_6311_ = lean_ctor_get(v___x_6310_, 4);
v_env_6312_ = lean_ctor_get(v___x_6310_, 0);
v_nextMacroScope_6313_ = lean_ctor_get(v___x_6310_, 1);
v_ngen_6314_ = lean_ctor_get(v___x_6310_, 2);
v_auxDeclNGen_6315_ = lean_ctor_get(v___x_6310_, 3);
v_cache_6316_ = lean_ctor_get(v___x_6310_, 5);
v_recordedDeps_6317_ = lean_ctor_get(v___x_6310_, 6);
v_messages_6318_ = lean_ctor_get(v___x_6310_, 7);
v_infoState_6319_ = lean_ctor_get(v___x_6310_, 8);
v_snapshotTasks_6320_ = lean_ctor_get(v___x_6310_, 9);
v_isSharedCheck_6343_ = !lean_is_exclusive(v___x_6310_);
if (v_isSharedCheck_6343_ == 0)
{
v___x_6322_ = v___x_6310_;
v_isShared_6323_ = v_isSharedCheck_6343_;
goto v_resetjp_6321_;
}
else
{
lean_inc(v_snapshotTasks_6320_);
lean_inc(v_infoState_6319_);
lean_inc(v_messages_6318_);
lean_inc(v_recordedDeps_6317_);
lean_inc(v_cache_6316_);
lean_inc(v_traceState_6311_);
lean_inc(v_auxDeclNGen_6315_);
lean_inc(v_ngen_6314_);
lean_inc(v_nextMacroScope_6313_);
lean_inc(v_env_6312_);
lean_dec(v___x_6310_);
v___x_6322_ = lean_box(0);
v_isShared_6323_ = v_isSharedCheck_6343_;
goto v_resetjp_6321_;
}
v_resetjp_6321_:
{
uint64_t v_tid_6324_; lean_object* v___x_6326_; uint8_t v_isShared_6327_; uint8_t v_isSharedCheck_6341_; 
v_tid_6324_ = lean_ctor_get_uint64(v_traceState_6311_, sizeof(void*)*1);
v_isSharedCheck_6341_ = !lean_is_exclusive(v_traceState_6311_);
if (v_isSharedCheck_6341_ == 0)
{
lean_object* v_unused_6342_; 
v_unused_6342_ = lean_ctor_get(v_traceState_6311_, 0);
lean_dec(v_unused_6342_);
v___x_6326_ = v_traceState_6311_;
v_isShared_6327_ = v_isSharedCheck_6341_;
goto v_resetjp_6325_;
}
else
{
lean_dec(v_traceState_6311_);
v___x_6326_ = lean_box(0);
v_isShared_6327_ = v_isSharedCheck_6341_;
goto v_resetjp_6325_;
}
v_resetjp_6325_:
{
lean_object* v___x_6328_; lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6332_; 
v___x_6328_ = lean_box(0);
v___x_6329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6329_, 0, v_ref_6282_);
lean_ctor_set(v___x_6329_, 1, v_a_6306_);
v___x_6330_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6280_, v___x_6329_);
if (v_isShared_6327_ == 0)
{
lean_ctor_set(v___x_6326_, 0, v___x_6330_);
v___x_6332_ = v___x_6326_;
goto v_reusejp_6331_;
}
else
{
lean_object* v_reuseFailAlloc_6340_; 
v_reuseFailAlloc_6340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6340_, 0, v___x_6330_);
lean_ctor_set_uint64(v_reuseFailAlloc_6340_, sizeof(void*)*1, v_tid_6324_);
v___x_6332_ = v_reuseFailAlloc_6340_;
goto v_reusejp_6331_;
}
v_reusejp_6331_:
{
lean_object* v___x_6334_; 
if (v_isShared_6323_ == 0)
{
lean_ctor_set(v___x_6322_, 4, v___x_6332_);
v___x_6334_ = v___x_6322_;
goto v_reusejp_6333_;
}
else
{
lean_object* v_reuseFailAlloc_6339_; 
v_reuseFailAlloc_6339_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_env_6312_);
lean_ctor_set(v_reuseFailAlloc_6339_, 1, v_nextMacroScope_6313_);
lean_ctor_set(v_reuseFailAlloc_6339_, 2, v_ngen_6314_);
lean_ctor_set(v_reuseFailAlloc_6339_, 3, v_auxDeclNGen_6315_);
lean_ctor_set(v_reuseFailAlloc_6339_, 4, v___x_6332_);
lean_ctor_set(v_reuseFailAlloc_6339_, 5, v_cache_6316_);
lean_ctor_set(v_reuseFailAlloc_6339_, 6, v_recordedDeps_6317_);
lean_ctor_set(v_reuseFailAlloc_6339_, 7, v_messages_6318_);
lean_ctor_set(v_reuseFailAlloc_6339_, 8, v_infoState_6319_);
lean_ctor_set(v_reuseFailAlloc_6339_, 9, v_snapshotTasks_6320_);
v___x_6334_ = v_reuseFailAlloc_6339_;
goto v_reusejp_6333_;
}
v_reusejp_6333_:
{
lean_object* v___x_6335_; lean_object* v___x_6337_; 
v___x_6335_ = lean_st_ref_put(v___y_6287_, v___x_6334_);
if (v_isShared_6309_ == 0)
{
lean_ctor_set(v___x_6308_, 0, v___x_6328_);
v___x_6337_ = v___x_6308_;
goto v_reusejp_6336_;
}
else
{
lean_object* v_reuseFailAlloc_6338_; 
v_reuseFailAlloc_6338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6338_, 0, v___x_6328_);
v___x_6337_ = v_reuseFailAlloc_6338_;
goto v_reusejp_6336_;
}
v_reusejp_6336_:
{
return v___x_6337_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6345_, lean_object* v_data_6346_, lean_object* v_ref_6347_, lean_object* v_msg_6348_, lean_object* v___y_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_){
_start:
{
lean_object* v_res_6354_; 
v_res_6354_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6345_, v_data_6346_, v_ref_6347_, v_msg_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_);
lean_dec(v___y_6352_);
lean_dec_ref(v___y_6351_);
lean_dec(v___y_6350_);
lean_dec_ref(v___y_6349_);
return v_res_6354_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6356_; lean_object* v___x_6357_; 
v___x_6356_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6357_ = l_Lean_stringToMessageData(v___x_6356_);
return v___x_6357_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6358_; double v___x_6359_; 
v___x_6358_ = lean_unsigned_to_nat(1000u);
v___x_6359_ = lean_float_of_nat(v___x_6358_);
return v___x_6359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6360_, uint8_t v_collapsed_6361_, lean_object* v_tag_6362_, lean_object* v_opts_6363_, uint8_t v_clsEnabled_6364_, lean_object* v_oldTraces_6365_, lean_object* v_msg_6366_, lean_object* v_resStartStop_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_){
_start:
{
lean_object* v_fst_6380_; lean_object* v_snd_6381_; lean_object* v___y_6383_; lean_object* v___y_6384_; lean_object* v_data_6385_; lean_object* v_fst_6396_; lean_object* v_snd_6397_; lean_object* v___x_6398_; uint8_t v___x_6399_; lean_object* v___y_6401_; lean_object* v_a_6402_; uint8_t v___y_6417_; double v___y_6449_; 
v_fst_6380_ = lean_ctor_get(v_resStartStop_6367_, 0);
lean_inc(v_fst_6380_);
v_snd_6381_ = lean_ctor_get(v_resStartStop_6367_, 1);
lean_inc(v_snd_6381_);
lean_dec_ref(v_resStartStop_6367_);
v_fst_6396_ = lean_ctor_get(v_snd_6381_, 0);
lean_inc(v_fst_6396_);
v_snd_6397_ = lean_ctor_get(v_snd_6381_, 1);
lean_inc(v_snd_6397_);
lean_dec(v_snd_6381_);
v___x_6398_ = l_Lean_trace_profiler;
v___x_6399_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6363_, v___x_6398_);
if (v___x_6399_ == 0)
{
v___y_6417_ = v___x_6399_;
goto v___jp_6416_;
}
else
{
lean_object* v___x_6454_; uint8_t v___x_6455_; 
v___x_6454_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6455_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6363_, v___x_6454_);
if (v___x_6455_ == 0)
{
lean_object* v___x_6456_; lean_object* v___x_6457_; double v___x_6458_; double v___x_6459_; double v___x_6460_; 
v___x_6456_ = l_Lean_trace_profiler_threshold;
v___x_6457_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6363_, v___x_6456_);
v___x_6458_ = lean_float_of_nat(v___x_6457_);
v___x_6459_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6460_ = lean_float_div(v___x_6458_, v___x_6459_);
v___y_6449_ = v___x_6460_;
goto v___jp_6448_;
}
else
{
lean_object* v___x_6461_; lean_object* v___x_6462_; double v___x_6463_; 
v___x_6461_ = l_Lean_trace_profiler_threshold;
v___x_6462_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6363_, v___x_6461_);
v___x_6463_ = lean_float_of_nat(v___x_6462_);
v___y_6449_ = v___x_6463_;
goto v___jp_6448_;
}
}
v___jp_6382_:
{
lean_object* v___x_6386_; 
lean_inc(v___y_6384_);
v___x_6386_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6365_, v_data_6385_, v___y_6384_, v___y_6383_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_);
if (lean_obj_tag(v___x_6386_) == 0)
{
lean_object* v___x_6387_; 
lean_dec_ref_known(v___x_6386_, 1);
v___x_6387_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6380_);
return v___x_6387_;
}
else
{
lean_object* v_a_6388_; lean_object* v___x_6390_; uint8_t v_isShared_6391_; uint8_t v_isSharedCheck_6395_; 
lean_dec(v_fst_6380_);
v_a_6388_ = lean_ctor_get(v___x_6386_, 0);
v_isSharedCheck_6395_ = !lean_is_exclusive(v___x_6386_);
if (v_isSharedCheck_6395_ == 0)
{
v___x_6390_ = v___x_6386_;
v_isShared_6391_ = v_isSharedCheck_6395_;
goto v_resetjp_6389_;
}
else
{
lean_inc(v_a_6388_);
lean_dec(v___x_6386_);
v___x_6390_ = lean_box(0);
v_isShared_6391_ = v_isSharedCheck_6395_;
goto v_resetjp_6389_;
}
v_resetjp_6389_:
{
lean_object* v___x_6393_; 
if (v_isShared_6391_ == 0)
{
v___x_6393_ = v___x_6390_;
goto v_reusejp_6392_;
}
else
{
lean_object* v_reuseFailAlloc_6394_; 
v_reuseFailAlloc_6394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6394_, 0, v_a_6388_);
v___x_6393_ = v_reuseFailAlloc_6394_;
goto v_reusejp_6392_;
}
v_reusejp_6392_:
{
return v___x_6393_;
}
}
}
}
v___jp_6400_:
{
uint8_t v_result_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; double v___x_6406_; lean_object* v_data_6407_; 
v_result_6403_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6380_);
v___x_6404_ = lean_box(v_result_6403_);
v___x_6405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6405_, 0, v___x_6404_);
v___x_6406_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6362_);
lean_inc_ref(v___x_6405_);
lean_inc(v_cls_6360_);
v_data_6407_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6407_, 0, v_cls_6360_);
lean_ctor_set(v_data_6407_, 1, v___x_6405_);
lean_ctor_set(v_data_6407_, 2, v_tag_6362_);
lean_ctor_set_float(v_data_6407_, sizeof(void*)*3, v___x_6406_);
lean_ctor_set_float(v_data_6407_, sizeof(void*)*3 + 8, v___x_6406_);
lean_ctor_set_uint8(v_data_6407_, sizeof(void*)*3 + 16, v_collapsed_6361_);
if (v___x_6399_ == 0)
{
lean_dec_ref_known(v___x_6405_, 1);
lean_dec(v_snd_6397_);
lean_dec(v_fst_6396_);
lean_dec_ref(v_tag_6362_);
lean_dec(v_cls_6360_);
v___y_6383_ = v_a_6402_;
v___y_6384_ = v___y_6401_;
v_data_6385_ = v_data_6407_;
goto v___jp_6382_;
}
else
{
lean_object* v_data_6408_; double v___x_6409_; double v___x_6410_; 
lean_dec_ref_known(v_data_6407_, 3);
v_data_6408_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6408_, 0, v_cls_6360_);
lean_ctor_set(v_data_6408_, 1, v___x_6405_);
lean_ctor_set(v_data_6408_, 2, v_tag_6362_);
v___x_6409_ = lean_unbox_float(v_fst_6396_);
lean_dec(v_fst_6396_);
lean_ctor_set_float(v_data_6408_, sizeof(void*)*3, v___x_6409_);
v___x_6410_ = lean_unbox_float(v_snd_6397_);
lean_dec(v_snd_6397_);
lean_ctor_set_float(v_data_6408_, sizeof(void*)*3 + 8, v___x_6410_);
lean_ctor_set_uint8(v_data_6408_, sizeof(void*)*3 + 16, v_collapsed_6361_);
v___y_6383_ = v_a_6402_;
v___y_6384_ = v___y_6401_;
v_data_6385_ = v_data_6408_;
goto v___jp_6382_;
}
}
v___jp_6411_:
{
lean_object* v_ref_6412_; lean_object* v___x_6413_; 
v_ref_6412_ = lean_ctor_get(v___y_6377_, 2);
lean_inc(v___y_6378_);
lean_inc_ref(v___y_6377_);
lean_inc(v___y_6376_);
lean_inc_ref(v___y_6375_);
lean_inc(v___y_6374_);
lean_inc_ref(v___y_6373_);
lean_inc(v___y_6372_);
lean_inc_ref(v___y_6371_);
lean_inc(v___y_6370_);
lean_inc(v___y_6369_);
lean_inc_ref(v___y_6368_);
lean_inc(v_fst_6380_);
v___x_6413_ = lean_apply_13(v_msg_6366_, v_fst_6380_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_, lean_box(0));
if (lean_obj_tag(v___x_6413_) == 0)
{
lean_object* v_a_6414_; 
v_a_6414_ = lean_ctor_get(v___x_6413_, 0);
lean_inc(v_a_6414_);
lean_dec_ref_known(v___x_6413_, 1);
v___y_6401_ = v_ref_6412_;
v_a_6402_ = v_a_6414_;
goto v___jp_6400_;
}
else
{
lean_object* v___x_6415_; 
lean_dec_ref_known(v___x_6413_, 1);
v___x_6415_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6401_ = v_ref_6412_;
v_a_6402_ = v___x_6415_;
goto v___jp_6400_;
}
}
v___jp_6416_:
{
if (v_clsEnabled_6364_ == 0)
{
if (v___y_6417_ == 0)
{
lean_object* v___x_6418_; lean_object* v_traceState_6419_; lean_object* v_env_6420_; lean_object* v_nextMacroScope_6421_; lean_object* v_ngen_6422_; lean_object* v_auxDeclNGen_6423_; lean_object* v_cache_6424_; lean_object* v_recordedDeps_6425_; lean_object* v_messages_6426_; lean_object* v_infoState_6427_; lean_object* v_snapshotTasks_6428_; lean_object* v___x_6430_; uint8_t v_isShared_6431_; uint8_t v_isSharedCheck_6447_; 
lean_dec(v_snd_6397_);
lean_dec(v_fst_6396_);
lean_dec_ref(v_msg_6366_);
lean_dec_ref(v_tag_6362_);
lean_dec(v_cls_6360_);
v___x_6418_ = lean_st_ref_take(v___y_6378_);
v_traceState_6419_ = lean_ctor_get(v___x_6418_, 4);
v_env_6420_ = lean_ctor_get(v___x_6418_, 0);
v_nextMacroScope_6421_ = lean_ctor_get(v___x_6418_, 1);
v_ngen_6422_ = lean_ctor_get(v___x_6418_, 2);
v_auxDeclNGen_6423_ = lean_ctor_get(v___x_6418_, 3);
v_cache_6424_ = lean_ctor_get(v___x_6418_, 5);
v_recordedDeps_6425_ = lean_ctor_get(v___x_6418_, 6);
v_messages_6426_ = lean_ctor_get(v___x_6418_, 7);
v_infoState_6427_ = lean_ctor_get(v___x_6418_, 8);
v_snapshotTasks_6428_ = lean_ctor_get(v___x_6418_, 9);
v_isSharedCheck_6447_ = !lean_is_exclusive(v___x_6418_);
if (v_isSharedCheck_6447_ == 0)
{
v___x_6430_ = v___x_6418_;
v_isShared_6431_ = v_isSharedCheck_6447_;
goto v_resetjp_6429_;
}
else
{
lean_inc(v_snapshotTasks_6428_);
lean_inc(v_infoState_6427_);
lean_inc(v_messages_6426_);
lean_inc(v_recordedDeps_6425_);
lean_inc(v_cache_6424_);
lean_inc(v_traceState_6419_);
lean_inc(v_auxDeclNGen_6423_);
lean_inc(v_ngen_6422_);
lean_inc(v_nextMacroScope_6421_);
lean_inc(v_env_6420_);
lean_dec(v___x_6418_);
v___x_6430_ = lean_box(0);
v_isShared_6431_ = v_isSharedCheck_6447_;
goto v_resetjp_6429_;
}
v_resetjp_6429_:
{
uint64_t v_tid_6432_; lean_object* v_traces_6433_; lean_object* v___x_6435_; uint8_t v_isShared_6436_; uint8_t v_isSharedCheck_6446_; 
v_tid_6432_ = lean_ctor_get_uint64(v_traceState_6419_, sizeof(void*)*1);
v_traces_6433_ = lean_ctor_get(v_traceState_6419_, 0);
v_isSharedCheck_6446_ = !lean_is_exclusive(v_traceState_6419_);
if (v_isSharedCheck_6446_ == 0)
{
v___x_6435_ = v_traceState_6419_;
v_isShared_6436_ = v_isSharedCheck_6446_;
goto v_resetjp_6434_;
}
else
{
lean_inc(v_traces_6433_);
lean_dec(v_traceState_6419_);
v___x_6435_ = lean_box(0);
v_isShared_6436_ = v_isSharedCheck_6446_;
goto v_resetjp_6434_;
}
v_resetjp_6434_:
{
lean_object* v___x_6437_; lean_object* v___x_6439_; 
v___x_6437_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6365_, v_traces_6433_);
lean_dec_ref(v_traces_6433_);
if (v_isShared_6436_ == 0)
{
lean_ctor_set(v___x_6435_, 0, v___x_6437_);
v___x_6439_ = v___x_6435_;
goto v_reusejp_6438_;
}
else
{
lean_object* v_reuseFailAlloc_6445_; 
v_reuseFailAlloc_6445_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6445_, 0, v___x_6437_);
lean_ctor_set_uint64(v_reuseFailAlloc_6445_, sizeof(void*)*1, v_tid_6432_);
v___x_6439_ = v_reuseFailAlloc_6445_;
goto v_reusejp_6438_;
}
v_reusejp_6438_:
{
lean_object* v___x_6441_; 
if (v_isShared_6431_ == 0)
{
lean_ctor_set(v___x_6430_, 4, v___x_6439_);
v___x_6441_ = v___x_6430_;
goto v_reusejp_6440_;
}
else
{
lean_object* v_reuseFailAlloc_6444_; 
v_reuseFailAlloc_6444_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_env_6420_);
lean_ctor_set(v_reuseFailAlloc_6444_, 1, v_nextMacroScope_6421_);
lean_ctor_set(v_reuseFailAlloc_6444_, 2, v_ngen_6422_);
lean_ctor_set(v_reuseFailAlloc_6444_, 3, v_auxDeclNGen_6423_);
lean_ctor_set(v_reuseFailAlloc_6444_, 4, v___x_6439_);
lean_ctor_set(v_reuseFailAlloc_6444_, 5, v_cache_6424_);
lean_ctor_set(v_reuseFailAlloc_6444_, 6, v_recordedDeps_6425_);
lean_ctor_set(v_reuseFailAlloc_6444_, 7, v_messages_6426_);
lean_ctor_set(v_reuseFailAlloc_6444_, 8, v_infoState_6427_);
lean_ctor_set(v_reuseFailAlloc_6444_, 9, v_snapshotTasks_6428_);
v___x_6441_ = v_reuseFailAlloc_6444_;
goto v_reusejp_6440_;
}
v_reusejp_6440_:
{
lean_object* v___x_6442_; lean_object* v___x_6443_; 
v___x_6442_ = lean_st_ref_put(v___y_6378_, v___x_6441_);
v___x_6443_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6380_);
return v___x_6443_;
}
}
}
}
}
else
{
goto v___jp_6411_;
}
}
else
{
goto v___jp_6411_;
}
}
v___jp_6448_:
{
double v___x_6450_; double v___x_6451_; double v___x_6452_; uint8_t v___x_6453_; 
v___x_6450_ = lean_unbox_float(v_snd_6397_);
v___x_6451_ = lean_unbox_float(v_fst_6396_);
v___x_6452_ = lean_float_sub(v___x_6450_, v___x_6451_);
v___x_6453_ = lean_float_decLt(v___y_6449_, v___x_6452_);
v___y_6417_ = v___x_6453_;
goto v___jp_6416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6464_ = _args[0];
lean_object* v_collapsed_6465_ = _args[1];
lean_object* v_tag_6466_ = _args[2];
lean_object* v_opts_6467_ = _args[3];
lean_object* v_clsEnabled_6468_ = _args[4];
lean_object* v_oldTraces_6469_ = _args[5];
lean_object* v_msg_6470_ = _args[6];
lean_object* v_resStartStop_6471_ = _args[7];
lean_object* v___y_6472_ = _args[8];
lean_object* v___y_6473_ = _args[9];
lean_object* v___y_6474_ = _args[10];
lean_object* v___y_6475_ = _args[11];
lean_object* v___y_6476_ = _args[12];
lean_object* v___y_6477_ = _args[13];
lean_object* v___y_6478_ = _args[14];
lean_object* v___y_6479_ = _args[15];
lean_object* v___y_6480_ = _args[16];
lean_object* v___y_6481_ = _args[17];
lean_object* v___y_6482_ = _args[18];
lean_object* v___y_6483_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6484_; uint8_t v_clsEnabled_boxed_6485_; lean_object* v_res_6486_; 
v_collapsed_boxed_6484_ = lean_unbox(v_collapsed_6465_);
v_clsEnabled_boxed_6485_ = lean_unbox(v_clsEnabled_6468_);
v_res_6486_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6464_, v_collapsed_boxed_6484_, v_tag_6466_, v_opts_6467_, v_clsEnabled_boxed_6485_, v_oldTraces_6469_, v_msg_6470_, v_resStartStop_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
lean_dec(v___y_6482_);
lean_dec_ref(v___y_6481_);
lean_dec(v___y_6480_);
lean_dec_ref(v___y_6479_);
lean_dec(v___y_6478_);
lean_dec_ref(v___y_6477_);
lean_dec(v___y_6476_);
lean_dec_ref(v___y_6475_);
lean_dec(v___y_6474_);
lean_dec(v___y_6473_);
lean_dec_ref(v___y_6472_);
lean_dec_ref(v_opts_6467_);
return v_res_6486_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; 
v___x_6491_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6492_ = l_Lean_stringToMessageData(v___x_6491_);
return v___x_6492_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6493_, lean_object* v_b_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_){
_start:
{
if (lean_obj_tag(v_as_x27_6493_) == 0)
{
lean_object* v___x_6507_; 
v___x_6507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6507_, 0, v_b_6494_);
return v___x_6507_;
}
else
{
lean_object* v_head_6508_; lean_object* v_toCold_6509_; lean_object* v_options_6510_; lean_object* v_tail_6511_; lean_object* v_name_6512_; lean_object* v_run_x27_6513_; lean_object* v_inheritedTraceOptions_6514_; uint8_t v_hasTrace_6515_; lean_object* v___x_6516_; uint8_t v___y_6518_; lean_object* v___x_6523_; lean_object* v___y_6525_; 
lean_dec_ref(v_b_6494_);
v_head_6508_ = lean_ctor_get(v_as_x27_6493_, 0);
v_toCold_6509_ = lean_ctor_get(v___y_6504_, 0);
v_options_6510_ = lean_ctor_get(v_toCold_6509_, 2);
v_tail_6511_ = lean_ctor_get(v_as_x27_6493_, 1);
v_name_6512_ = lean_ctor_get(v_head_6508_, 0);
v_run_x27_6513_ = lean_ctor_get(v_head_6508_, 1);
v_inheritedTraceOptions_6514_ = lean_ctor_get(v_toCold_6509_, 11);
v_hasTrace_6515_ = lean_ctor_get_uint8(v_options_6510_, sizeof(void*)*1);
v___x_6516_ = lean_box(0);
v___x_6523_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6515_ == 0)
{
lean_object* v___x_6553_; 
lean_inc_ref(v_run_x27_6513_);
lean_inc(v___y_6505_);
lean_inc_ref(v___y_6504_);
lean_inc(v___y_6503_);
lean_inc_ref(v___y_6502_);
lean_inc(v___y_6501_);
lean_inc_ref(v___y_6500_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
lean_inc(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc_ref(v___y_6495_);
v___x_6553_ = lean_apply_12(v_run_x27_6513_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, lean_box(0));
v___y_6525_ = v___x_6553_;
goto v___jp_6524_;
}
else
{
lean_object* v___f_6554_; lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; uint8_t v___x_6558_; lean_object* v___y_6560_; lean_object* v___y_6561_; lean_object* v_a_6562_; lean_object* v___y_6575_; lean_object* v___y_6576_; lean_object* v_a_6577_; 
lean_inc(v_name_6512_);
v___f_6554_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6554_, 0, v_name_6512_);
v___x_6555_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6556_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6557_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6514_, v_options_6510_, v___x_6557_);
if (v___x_6558_ == 0)
{
lean_object* v___x_6627_; uint8_t v___x_6628_; 
v___x_6627_ = l_Lean_trace_profiler;
v___x_6628_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6510_, v___x_6627_);
if (v___x_6628_ == 0)
{
lean_object* v___x_6629_; 
lean_dec_ref(v___f_6554_);
lean_inc_ref(v_run_x27_6513_);
lean_inc(v___y_6505_);
lean_inc_ref(v___y_6504_);
lean_inc(v___y_6503_);
lean_inc_ref(v___y_6502_);
lean_inc(v___y_6501_);
lean_inc_ref(v___y_6500_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
lean_inc(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc_ref(v___y_6495_);
v___x_6629_ = lean_apply_12(v_run_x27_6513_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, lean_box(0));
v___y_6525_ = v___x_6629_;
goto v___jp_6524_;
}
else
{
goto v___jp_6586_;
}
}
else
{
goto v___jp_6586_;
}
v___jp_6559_:
{
lean_object* v___x_6563_; double v___x_6564_; double v___x_6565_; double v___x_6566_; double v___x_6567_; double v___x_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; 
v___x_6563_ = lean_io_mono_nanos_now();
v___x_6564_ = lean_float_of_nat(v___y_6561_);
v___x_6565_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6566_ = lean_float_div(v___x_6564_, v___x_6565_);
v___x_6567_ = lean_float_of_nat(v___x_6563_);
v___x_6568_ = lean_float_div(v___x_6567_, v___x_6565_);
v___x_6569_ = lean_box_float(v___x_6566_);
v___x_6570_ = lean_box_float(v___x_6568_);
v___x_6571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6571_, 0, v___x_6569_);
lean_ctor_set(v___x_6571_, 1, v___x_6570_);
v___x_6572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6572_, 0, v_a_6562_);
lean_ctor_set(v___x_6572_, 1, v___x_6571_);
v___x_6573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6555_, v_hasTrace_6515_, v___x_6556_, v_options_6510_, v___x_6558_, v___y_6560_, v___f_6554_, v___x_6572_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_);
v___y_6525_ = v___x_6573_;
goto v___jp_6524_;
}
v___jp_6574_:
{
lean_object* v___x_6578_; double v___x_6579_; double v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; lean_object* v___x_6584_; lean_object* v___x_6585_; 
v___x_6578_ = lean_io_get_num_heartbeats();
v___x_6579_ = lean_float_of_nat(v___y_6576_);
v___x_6580_ = lean_float_of_nat(v___x_6578_);
v___x_6581_ = lean_box_float(v___x_6579_);
v___x_6582_ = lean_box_float(v___x_6580_);
v___x_6583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6583_, 0, v___x_6581_);
lean_ctor_set(v___x_6583_, 1, v___x_6582_);
v___x_6584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6584_, 0, v_a_6577_);
lean_ctor_set(v___x_6584_, 1, v___x_6583_);
v___x_6585_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6555_, v_hasTrace_6515_, v___x_6556_, v_options_6510_, v___x_6558_, v___y_6575_, v___f_6554_, v___x_6584_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_);
v___y_6525_ = v___x_6585_;
goto v___jp_6524_;
}
v___jp_6586_:
{
lean_object* v___x_6587_; lean_object* v_a_6588_; lean_object* v___x_6589_; uint8_t v___x_6590_; 
v___x_6587_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6505_);
v_a_6588_ = lean_ctor_get(v___x_6587_, 0);
lean_inc(v_a_6588_);
lean_dec_ref(v___x_6587_);
v___x_6589_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6590_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6510_, v___x_6589_);
if (v___x_6590_ == 0)
{
lean_object* v___x_6591_; lean_object* v___x_6592_; 
v___x_6591_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_6513_);
lean_inc(v___y_6505_);
lean_inc_ref(v___y_6504_);
lean_inc(v___y_6503_);
lean_inc_ref(v___y_6502_);
lean_inc(v___y_6501_);
lean_inc_ref(v___y_6500_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
lean_inc(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc_ref(v___y_6495_);
v___x_6592_ = lean_apply_12(v_run_x27_6513_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, lean_box(0));
if (lean_obj_tag(v___x_6592_) == 0)
{
lean_object* v_a_6593_; lean_object* v___x_6595_; uint8_t v_isShared_6596_; uint8_t v_isSharedCheck_6600_; 
v_a_6593_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6600_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6600_ == 0)
{
v___x_6595_ = v___x_6592_;
v_isShared_6596_ = v_isSharedCheck_6600_;
goto v_resetjp_6594_;
}
else
{
lean_inc(v_a_6593_);
lean_dec(v___x_6592_);
v___x_6595_ = lean_box(0);
v_isShared_6596_ = v_isSharedCheck_6600_;
goto v_resetjp_6594_;
}
v_resetjp_6594_:
{
lean_object* v___x_6598_; 
if (v_isShared_6596_ == 0)
{
lean_ctor_set_tag(v___x_6595_, 1);
v___x_6598_ = v___x_6595_;
goto v_reusejp_6597_;
}
else
{
lean_object* v_reuseFailAlloc_6599_; 
v_reuseFailAlloc_6599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6599_, 0, v_a_6593_);
v___x_6598_ = v_reuseFailAlloc_6599_;
goto v_reusejp_6597_;
}
v_reusejp_6597_:
{
v___y_6560_ = v_a_6588_;
v___y_6561_ = v___x_6591_;
v_a_6562_ = v___x_6598_;
goto v___jp_6559_;
}
}
}
else
{
lean_object* v_a_6601_; lean_object* v___x_6603_; uint8_t v_isShared_6604_; uint8_t v_isSharedCheck_6608_; 
v_a_6601_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6608_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6608_ == 0)
{
v___x_6603_ = v___x_6592_;
v_isShared_6604_ = v_isSharedCheck_6608_;
goto v_resetjp_6602_;
}
else
{
lean_inc(v_a_6601_);
lean_dec(v___x_6592_);
v___x_6603_ = lean_box(0);
v_isShared_6604_ = v_isSharedCheck_6608_;
goto v_resetjp_6602_;
}
v_resetjp_6602_:
{
lean_object* v___x_6606_; 
if (v_isShared_6604_ == 0)
{
lean_ctor_set_tag(v___x_6603_, 0);
v___x_6606_ = v___x_6603_;
goto v_reusejp_6605_;
}
else
{
lean_object* v_reuseFailAlloc_6607_; 
v_reuseFailAlloc_6607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6607_, 0, v_a_6601_);
v___x_6606_ = v_reuseFailAlloc_6607_;
goto v_reusejp_6605_;
}
v_reusejp_6605_:
{
v___y_6560_ = v_a_6588_;
v___y_6561_ = v___x_6591_;
v_a_6562_ = v___x_6606_;
goto v___jp_6559_;
}
}
}
}
else
{
lean_object* v___x_6609_; lean_object* v___x_6610_; 
v___x_6609_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_6513_);
lean_inc(v___y_6505_);
lean_inc_ref(v___y_6504_);
lean_inc(v___y_6503_);
lean_inc_ref(v___y_6502_);
lean_inc(v___y_6501_);
lean_inc_ref(v___y_6500_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
lean_inc(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc_ref(v___y_6495_);
v___x_6610_ = lean_apply_12(v_run_x27_6513_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, lean_box(0));
if (lean_obj_tag(v___x_6610_) == 0)
{
lean_object* v_a_6611_; lean_object* v___x_6613_; uint8_t v_isShared_6614_; uint8_t v_isSharedCheck_6618_; 
v_a_6611_ = lean_ctor_get(v___x_6610_, 0);
v_isSharedCheck_6618_ = !lean_is_exclusive(v___x_6610_);
if (v_isSharedCheck_6618_ == 0)
{
v___x_6613_ = v___x_6610_;
v_isShared_6614_ = v_isSharedCheck_6618_;
goto v_resetjp_6612_;
}
else
{
lean_inc(v_a_6611_);
lean_dec(v___x_6610_);
v___x_6613_ = lean_box(0);
v_isShared_6614_ = v_isSharedCheck_6618_;
goto v_resetjp_6612_;
}
v_resetjp_6612_:
{
lean_object* v___x_6616_; 
if (v_isShared_6614_ == 0)
{
lean_ctor_set_tag(v___x_6613_, 1);
v___x_6616_ = v___x_6613_;
goto v_reusejp_6615_;
}
else
{
lean_object* v_reuseFailAlloc_6617_; 
v_reuseFailAlloc_6617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6617_, 0, v_a_6611_);
v___x_6616_ = v_reuseFailAlloc_6617_;
goto v_reusejp_6615_;
}
v_reusejp_6615_:
{
v___y_6575_ = v_a_6588_;
v___y_6576_ = v___x_6609_;
v_a_6577_ = v___x_6616_;
goto v___jp_6574_;
}
}
}
else
{
lean_object* v_a_6619_; lean_object* v___x_6621_; uint8_t v_isShared_6622_; uint8_t v_isSharedCheck_6626_; 
v_a_6619_ = lean_ctor_get(v___x_6610_, 0);
v_isSharedCheck_6626_ = !lean_is_exclusive(v___x_6610_);
if (v_isSharedCheck_6626_ == 0)
{
v___x_6621_ = v___x_6610_;
v_isShared_6622_ = v_isSharedCheck_6626_;
goto v_resetjp_6620_;
}
else
{
lean_inc(v_a_6619_);
lean_dec(v___x_6610_);
v___x_6621_ = lean_box(0);
v_isShared_6622_ = v_isSharedCheck_6626_;
goto v_resetjp_6620_;
}
v_resetjp_6620_:
{
lean_object* v___x_6624_; 
if (v_isShared_6622_ == 0)
{
lean_ctor_set_tag(v___x_6621_, 0);
v___x_6624_ = v___x_6621_;
goto v_reusejp_6623_;
}
else
{
lean_object* v_reuseFailAlloc_6625_; 
v_reuseFailAlloc_6625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6625_, 0, v_a_6619_);
v___x_6624_ = v_reuseFailAlloc_6625_;
goto v_reusejp_6623_;
}
v_reusejp_6623_:
{
v___y_6575_ = v_a_6588_;
v___y_6576_ = v___x_6609_;
v_a_6577_ = v___x_6624_;
goto v___jp_6574_;
}
}
}
}
}
}
v___jp_6517_:
{
lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; 
v___x_6519_ = lean_box(v___y_6518_);
v___x_6520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6520_, 0, v___x_6519_);
v___x_6521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6521_, 0, v___x_6520_);
lean_ctor_set(v___x_6521_, 1, v___x_6516_);
v___x_6522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6522_, 0, v___x_6521_);
return v___x_6522_;
}
v___jp_6524_:
{
if (lean_obj_tag(v___y_6525_) == 0)
{
lean_object* v_a_6526_; uint8_t v___x_6527_; 
v_a_6526_ = lean_ctor_get(v___y_6525_, 0);
lean_inc(v_a_6526_);
lean_dec_ref_known(v___y_6525_, 1);
v___x_6527_ = lean_unbox(v_a_6526_);
if (v___x_6527_ == 0)
{
lean_dec(v_a_6526_);
v_as_x27_6493_ = v_tail_6511_;
v_b_6494_ = v___x_6523_;
goto _start;
}
else
{
if (v_hasTrace_6515_ == 0)
{
uint8_t v___x_6529_; 
v___x_6529_ = lean_unbox(v_a_6526_);
lean_dec(v_a_6526_);
v___y_6518_ = v___x_6529_;
goto v___jp_6517_;
}
else
{
lean_object* v___x_6530_; lean_object* v___x_6531_; uint8_t v___x_6532_; 
v___x_6530_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6531_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6514_, v_options_6510_, v___x_6531_);
if (v___x_6532_ == 0)
{
uint8_t v___x_6533_; 
v___x_6533_ = lean_unbox(v_a_6526_);
lean_dec(v_a_6526_);
v___y_6518_ = v___x_6533_;
goto v___jp_6517_;
}
else
{
lean_object* v___x_6534_; lean_object* v___x_6535_; 
v___x_6534_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_6535_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6530_, v___x_6534_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_);
if (lean_obj_tag(v___x_6535_) == 0)
{
uint8_t v___x_6536_; 
lean_dec_ref_known(v___x_6535_, 1);
v___x_6536_ = lean_unbox(v_a_6526_);
lean_dec(v_a_6526_);
v___y_6518_ = v___x_6536_;
goto v___jp_6517_;
}
else
{
lean_object* v_a_6537_; lean_object* v___x_6539_; uint8_t v_isShared_6540_; uint8_t v_isSharedCheck_6544_; 
lean_dec(v_a_6526_);
v_a_6537_ = lean_ctor_get(v___x_6535_, 0);
v_isSharedCheck_6544_ = !lean_is_exclusive(v___x_6535_);
if (v_isSharedCheck_6544_ == 0)
{
v___x_6539_ = v___x_6535_;
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
else
{
lean_inc(v_a_6537_);
lean_dec(v___x_6535_);
v___x_6539_ = lean_box(0);
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
v_resetjp_6538_:
{
lean_object* v___x_6542_; 
if (v_isShared_6540_ == 0)
{
v___x_6542_ = v___x_6539_;
goto v_reusejp_6541_;
}
else
{
lean_object* v_reuseFailAlloc_6543_; 
v_reuseFailAlloc_6543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6537_);
v___x_6542_ = v_reuseFailAlloc_6543_;
goto v_reusejp_6541_;
}
v_reusejp_6541_:
{
return v___x_6542_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6545_; lean_object* v___x_6547_; uint8_t v_isShared_6548_; uint8_t v_isSharedCheck_6552_; 
v_a_6545_ = lean_ctor_get(v___y_6525_, 0);
v_isSharedCheck_6552_ = !lean_is_exclusive(v___y_6525_);
if (v_isSharedCheck_6552_ == 0)
{
v___x_6547_ = v___y_6525_;
v_isShared_6548_ = v_isSharedCheck_6552_;
goto v_resetjp_6546_;
}
else
{
lean_inc(v_a_6545_);
lean_dec(v___y_6525_);
v___x_6547_ = lean_box(0);
v_isShared_6548_ = v_isSharedCheck_6552_;
goto v_resetjp_6546_;
}
v_resetjp_6546_:
{
lean_object* v___x_6550_; 
if (v_isShared_6548_ == 0)
{
v___x_6550_ = v___x_6547_;
goto v_reusejp_6549_;
}
else
{
lean_object* v_reuseFailAlloc_6551_; 
v_reuseFailAlloc_6551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6551_, 0, v_a_6545_);
v___x_6550_ = v_reuseFailAlloc_6551_;
goto v_reusejp_6549_;
}
v_reusejp_6549_:
{
return v___x_6550_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_6630_, lean_object* v_b_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_, lean_object* v___y_6640_, lean_object* v___y_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_){
_start:
{
lean_object* v_res_6644_; 
v_res_6644_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6630_, v_b_6631_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_, v___y_6642_);
lean_dec(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec(v___y_6640_);
lean_dec_ref(v___y_6639_);
lean_dec(v___y_6638_);
lean_dec_ref(v___y_6637_);
lean_dec(v___y_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec(v___y_6633_);
lean_dec_ref(v___y_6632_);
lean_dec(v_as_x27_6630_);
return v_res_6644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_6647_; lean_object* v___x_6648_; 
v___x_6647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_6648_ = l_Lean_stringToMessageData(v___x_6647_);
return v___x_6648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_6650_; lean_object* v___x_6651_; 
v___x_6650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_6651_ = l_Lean_stringToMessageData(v___x_6650_);
return v___x_6651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_6652_, lean_object* v_a_6653_, lean_object* v_a_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_, lean_object* v_a_6657_, lean_object* v_a_6658_, lean_object* v_a_6659_, lean_object* v_a_6660_, lean_object* v_a_6661_, lean_object* v_a_6662_, lean_object* v_a_6663_){
_start:
{
lean_object* v___x_6665_; lean_object* v___x_6666_; 
v___x_6665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_6666_ = l_Lean_Core_checkSystem(v___x_6665_, v_a_6662_, v_a_6663_);
if (lean_obj_tag(v___x_6666_) == 0)
{
lean_object* v___x_6667_; lean_object* v_caches_6668_; lean_object* v_typeAnalysis_6669_; lean_object* v_target_6670_; lean_object* v_hypotheses_6671_; lean_object* v___x_6673_; uint8_t v_isShared_6674_; uint8_t v_isSharedCheck_6756_; 
lean_dec_ref_known(v___x_6666_, 1);
v___x_6667_ = lean_st_ref_take(v_a_6654_);
v_caches_6668_ = lean_ctor_get(v___x_6667_, 0);
v_typeAnalysis_6669_ = lean_ctor_get(v___x_6667_, 1);
v_target_6670_ = lean_ctor_get(v___x_6667_, 2);
v_hypotheses_6671_ = lean_ctor_get(v___x_6667_, 3);
v_isSharedCheck_6756_ = !lean_is_exclusive(v___x_6667_);
if (v_isSharedCheck_6756_ == 0)
{
v___x_6673_ = v___x_6667_;
v_isShared_6674_ = v_isSharedCheck_6756_;
goto v_resetjp_6672_;
}
else
{
lean_inc(v_hypotheses_6671_);
lean_inc(v_target_6670_);
lean_inc(v_typeAnalysis_6669_);
lean_inc(v_caches_6668_);
lean_dec(v___x_6667_);
v___x_6673_ = lean_box(0);
v_isShared_6674_ = v_isSharedCheck_6756_;
goto v_resetjp_6672_;
}
v_resetjp_6672_:
{
uint8_t v___x_6675_; lean_object* v___x_6677_; 
v___x_6675_ = 0;
if (v_isShared_6674_ == 0)
{
v___x_6677_ = v___x_6673_;
goto v_reusejp_6676_;
}
else
{
lean_object* v_reuseFailAlloc_6755_; 
v_reuseFailAlloc_6755_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6755_, 0, v_caches_6668_);
lean_ctor_set(v_reuseFailAlloc_6755_, 1, v_typeAnalysis_6669_);
lean_ctor_set(v_reuseFailAlloc_6755_, 2, v_target_6670_);
lean_ctor_set(v_reuseFailAlloc_6755_, 3, v_hypotheses_6671_);
v___x_6677_ = v_reuseFailAlloc_6755_;
goto v_reusejp_6676_;
}
v_reusejp_6676_:
{
lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; 
lean_ctor_set_uint8(v___x_6677_, sizeof(void*)*4, v___x_6675_);
v___x_6678_ = lean_st_ref_put(v_a_6654_, v___x_6677_);
v___x_6679_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_6680_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_6652_, v___x_6679_, v_a_6653_, v_a_6654_, v_a_6655_, v_a_6656_, v_a_6657_, v_a_6658_, v_a_6659_, v_a_6660_, v_a_6661_, v_a_6662_, v_a_6663_);
if (lean_obj_tag(v___x_6680_) == 0)
{
lean_object* v_a_6681_; lean_object* v___x_6683_; uint8_t v_isShared_6684_; uint8_t v_isSharedCheck_6746_; 
v_a_6681_ = lean_ctor_get(v___x_6680_, 0);
v_isSharedCheck_6746_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6746_ == 0)
{
v___x_6683_ = v___x_6680_;
v_isShared_6684_ = v_isSharedCheck_6746_;
goto v_resetjp_6682_;
}
else
{
lean_inc(v_a_6681_);
lean_dec(v___x_6680_);
v___x_6683_ = lean_box(0);
v_isShared_6684_ = v_isSharedCheck_6746_;
goto v_resetjp_6682_;
}
v_resetjp_6682_:
{
lean_object* v_fst_6685_; 
v_fst_6685_ = lean_ctor_get(v_a_6681_, 0);
lean_inc(v_fst_6685_);
lean_dec(v_a_6681_);
if (lean_obj_tag(v_fst_6685_) == 0)
{
lean_object* v___x_6686_; uint8_t v_didChange_6687_; 
v___x_6686_ = lean_st_ref_get(v_a_6654_);
v_didChange_6687_ = lean_ctor_get_uint8(v___x_6686_, sizeof(void*)*4);
lean_dec(v___x_6686_);
if (v_didChange_6687_ == 0)
{
lean_object* v_toCold_6688_; lean_object* v_options_6689_; uint8_t v_hasTrace_6690_; 
v_toCold_6688_ = lean_ctor_get(v_a_6662_, 0);
v_options_6689_ = lean_ctor_get(v_toCold_6688_, 2);
v_hasTrace_6690_ = lean_ctor_get_uint8(v_options_6689_, sizeof(void*)*1);
if (v_hasTrace_6690_ == 0)
{
lean_object* v___x_6691_; lean_object* v___x_6693_; 
v___x_6691_ = lean_box(v_didChange_6687_);
if (v_isShared_6684_ == 0)
{
lean_ctor_set(v___x_6683_, 0, v___x_6691_);
v___x_6693_ = v___x_6683_;
goto v_reusejp_6692_;
}
else
{
lean_object* v_reuseFailAlloc_6694_; 
v_reuseFailAlloc_6694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6694_, 0, v___x_6691_);
v___x_6693_ = v_reuseFailAlloc_6694_;
goto v_reusejp_6692_;
}
v_reusejp_6692_:
{
return v___x_6693_;
}
}
else
{
lean_object* v_inheritedTraceOptions_6695_; lean_object* v___x_6696_; lean_object* v___x_6697_; uint8_t v___x_6698_; 
v_inheritedTraceOptions_6695_ = lean_ctor_get(v_toCold_6688_, 11);
v___x_6696_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6697_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6698_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6695_, v_options_6689_, v___x_6697_);
if (v___x_6698_ == 0)
{
lean_object* v___x_6699_; lean_object* v___x_6701_; 
v___x_6699_ = lean_box(v_didChange_6687_);
if (v_isShared_6684_ == 0)
{
lean_ctor_set(v___x_6683_, 0, v___x_6699_);
v___x_6701_ = v___x_6683_;
goto v_reusejp_6700_;
}
else
{
lean_object* v_reuseFailAlloc_6702_; 
v_reuseFailAlloc_6702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6702_, 0, v___x_6699_);
v___x_6701_ = v_reuseFailAlloc_6702_;
goto v_reusejp_6700_;
}
v_reusejp_6700_:
{
return v___x_6701_;
}
}
else
{
lean_object* v___x_6703_; lean_object* v___x_6704_; 
lean_del_object(v___x_6683_);
v___x_6703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6704_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6696_, v___x_6703_, v_a_6660_, v_a_6661_, v_a_6662_, v_a_6663_);
if (lean_obj_tag(v___x_6704_) == 0)
{
lean_object* v___x_6706_; uint8_t v_isShared_6707_; uint8_t v_isSharedCheck_6712_; 
v_isSharedCheck_6712_ = !lean_is_exclusive(v___x_6704_);
if (v_isSharedCheck_6712_ == 0)
{
lean_object* v_unused_6713_; 
v_unused_6713_ = lean_ctor_get(v___x_6704_, 0);
lean_dec(v_unused_6713_);
v___x_6706_ = v___x_6704_;
v_isShared_6707_ = v_isSharedCheck_6712_;
goto v_resetjp_6705_;
}
else
{
lean_dec(v___x_6704_);
v___x_6706_ = lean_box(0);
v_isShared_6707_ = v_isSharedCheck_6712_;
goto v_resetjp_6705_;
}
v_resetjp_6705_:
{
lean_object* v___x_6708_; lean_object* v___x_6710_; 
v___x_6708_ = lean_box(v_didChange_6687_);
if (v_isShared_6707_ == 0)
{
lean_ctor_set(v___x_6706_, 0, v___x_6708_);
v___x_6710_ = v___x_6706_;
goto v_reusejp_6709_;
}
else
{
lean_object* v_reuseFailAlloc_6711_; 
v_reuseFailAlloc_6711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6711_, 0, v___x_6708_);
v___x_6710_ = v_reuseFailAlloc_6711_;
goto v_reusejp_6709_;
}
v_reusejp_6709_:
{
return v___x_6710_;
}
}
}
else
{
lean_object* v_a_6714_; lean_object* v___x_6716_; uint8_t v_isShared_6717_; uint8_t v_isSharedCheck_6721_; 
v_a_6714_ = lean_ctor_get(v___x_6704_, 0);
v_isSharedCheck_6721_ = !lean_is_exclusive(v___x_6704_);
if (v_isSharedCheck_6721_ == 0)
{
v___x_6716_ = v___x_6704_;
v_isShared_6717_ = v_isSharedCheck_6721_;
goto v_resetjp_6715_;
}
else
{
lean_inc(v_a_6714_);
lean_dec(v___x_6704_);
v___x_6716_ = lean_box(0);
v_isShared_6717_ = v_isSharedCheck_6721_;
goto v_resetjp_6715_;
}
v_resetjp_6715_:
{
lean_object* v___x_6719_; 
if (v_isShared_6717_ == 0)
{
v___x_6719_ = v___x_6716_;
goto v_reusejp_6718_;
}
else
{
lean_object* v_reuseFailAlloc_6720_; 
v_reuseFailAlloc_6720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6720_, 0, v_a_6714_);
v___x_6719_ = v_reuseFailAlloc_6720_;
goto v_reusejp_6718_;
}
v_reusejp_6718_:
{
return v___x_6719_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_6722_; lean_object* v_options_6723_; uint8_t v_hasTrace_6724_; 
lean_del_object(v___x_6683_);
v_toCold_6722_ = lean_ctor_get(v_a_6662_, 0);
v_options_6723_ = lean_ctor_get(v_toCold_6722_, 2);
v_hasTrace_6724_ = lean_ctor_get_uint8(v_options_6723_, sizeof(void*)*1);
if (v_hasTrace_6724_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; uint8_t v___x_6729_; 
v_inheritedTraceOptions_6726_ = lean_ctor_get(v_toCold_6722_, 11);
v___x_6727_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6728_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6729_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6726_, v_options_6723_, v___x_6728_);
if (v___x_6729_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6731_; lean_object* v___x_6732_; 
v___x_6731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6732_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6727_, v___x_6731_, v_a_6660_, v_a_6661_, v_a_6662_, v_a_6663_);
if (lean_obj_tag(v___x_6732_) == 0)
{
lean_dec_ref_known(v___x_6732_, 1);
goto _start;
}
else
{
lean_object* v_a_6734_; lean_object* v___x_6736_; uint8_t v_isShared_6737_; uint8_t v_isSharedCheck_6741_; 
v_a_6734_ = lean_ctor_get(v___x_6732_, 0);
v_isSharedCheck_6741_ = !lean_is_exclusive(v___x_6732_);
if (v_isSharedCheck_6741_ == 0)
{
v___x_6736_ = v___x_6732_;
v_isShared_6737_ = v_isSharedCheck_6741_;
goto v_resetjp_6735_;
}
else
{
lean_inc(v_a_6734_);
lean_dec(v___x_6732_);
v___x_6736_ = lean_box(0);
v_isShared_6737_ = v_isSharedCheck_6741_;
goto v_resetjp_6735_;
}
v_resetjp_6735_:
{
lean_object* v___x_6739_; 
if (v_isShared_6737_ == 0)
{
v___x_6739_ = v___x_6736_;
goto v_reusejp_6738_;
}
else
{
lean_object* v_reuseFailAlloc_6740_; 
v_reuseFailAlloc_6740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6740_, 0, v_a_6734_);
v___x_6739_ = v_reuseFailAlloc_6740_;
goto v_reusejp_6738_;
}
v_reusejp_6738_:
{
return v___x_6739_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_6742_; lean_object* v___x_6744_; 
v_val_6742_ = lean_ctor_get(v_fst_6685_, 0);
lean_inc(v_val_6742_);
lean_dec_ref_known(v_fst_6685_, 1);
if (v_isShared_6684_ == 0)
{
lean_ctor_set(v___x_6683_, 0, v_val_6742_);
v___x_6744_ = v___x_6683_;
goto v_reusejp_6743_;
}
else
{
lean_object* v_reuseFailAlloc_6745_; 
v_reuseFailAlloc_6745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6745_, 0, v_val_6742_);
v___x_6744_ = v_reuseFailAlloc_6745_;
goto v_reusejp_6743_;
}
v_reusejp_6743_:
{
return v___x_6744_;
}
}
}
}
else
{
lean_object* v_a_6747_; lean_object* v___x_6749_; uint8_t v_isShared_6750_; uint8_t v_isSharedCheck_6754_; 
v_a_6747_ = lean_ctor_get(v___x_6680_, 0);
v_isSharedCheck_6754_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6754_ == 0)
{
v___x_6749_ = v___x_6680_;
v_isShared_6750_ = v_isSharedCheck_6754_;
goto v_resetjp_6748_;
}
else
{
lean_inc(v_a_6747_);
lean_dec(v___x_6680_);
v___x_6749_ = lean_box(0);
v_isShared_6750_ = v_isSharedCheck_6754_;
goto v_resetjp_6748_;
}
v_resetjp_6748_:
{
lean_object* v___x_6752_; 
if (v_isShared_6750_ == 0)
{
v___x_6752_ = v___x_6749_;
goto v_reusejp_6751_;
}
else
{
lean_object* v_reuseFailAlloc_6753_; 
v_reuseFailAlloc_6753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6753_, 0, v_a_6747_);
v___x_6752_ = v_reuseFailAlloc_6753_;
goto v_reusejp_6751_;
}
v_reusejp_6751_:
{
return v___x_6752_;
}
}
}
}
}
}
else
{
lean_object* v_a_6757_; lean_object* v___x_6759_; uint8_t v_isShared_6760_; uint8_t v_isSharedCheck_6764_; 
v_a_6757_ = lean_ctor_get(v___x_6666_, 0);
v_isSharedCheck_6764_ = !lean_is_exclusive(v___x_6666_);
if (v_isSharedCheck_6764_ == 0)
{
v___x_6759_ = v___x_6666_;
v_isShared_6760_ = v_isSharedCheck_6764_;
goto v_resetjp_6758_;
}
else
{
lean_inc(v_a_6757_);
lean_dec(v___x_6666_);
v___x_6759_ = lean_box(0);
v_isShared_6760_ = v_isSharedCheck_6764_;
goto v_resetjp_6758_;
}
v_resetjp_6758_:
{
lean_object* v___x_6762_; 
if (v_isShared_6760_ == 0)
{
v___x_6762_ = v___x_6759_;
goto v_reusejp_6761_;
}
else
{
lean_object* v_reuseFailAlloc_6763_; 
v_reuseFailAlloc_6763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6763_, 0, v_a_6757_);
v___x_6762_ = v_reuseFailAlloc_6763_;
goto v_reusejp_6761_;
}
v_reusejp_6761_:
{
return v___x_6762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6765_, lean_object* v_a_6766_, lean_object* v_a_6767_, lean_object* v_a_6768_, lean_object* v_a_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_, lean_object* v_a_6773_, lean_object* v_a_6774_, lean_object* v_a_6775_, lean_object* v_a_6776_, lean_object* v_a_6777_){
_start:
{
lean_object* v_res_6778_; 
v_res_6778_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6765_, v_a_6766_, v_a_6767_, v_a_6768_, v_a_6769_, v_a_6770_, v_a_6771_, v_a_6772_, v_a_6773_, v_a_6774_, v_a_6775_, v_a_6776_);
lean_dec(v_a_6776_);
lean_dec_ref(v_a_6775_);
lean_dec(v_a_6774_);
lean_dec_ref(v_a_6773_);
lean_dec(v_a_6772_);
lean_dec_ref(v_a_6771_);
lean_dec(v_a_6770_);
lean_dec_ref(v_a_6769_);
lean_dec(v_a_6768_);
lean_dec(v_a_6767_);
lean_dec_ref(v_a_6766_);
lean_dec(v_passes_6765_);
return v_res_6778_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6779_, lean_object* v_msg_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_, lean_object* v___y_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_){
_start:
{
lean_object* v___x_6793_; 
v___x_6793_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6779_, v_msg_6780_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_);
return v___x_6793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6794_, lean_object* v_msg_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_, lean_object* v___y_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_, lean_object* v___y_6807_){
_start:
{
lean_object* v_res_6808_; 
v_res_6808_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6794_, v_msg_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_);
lean_dec(v___y_6806_);
lean_dec_ref(v___y_6805_);
lean_dec(v___y_6804_);
lean_dec_ref(v___y_6803_);
lean_dec(v___y_6802_);
lean_dec_ref(v___y_6801_);
lean_dec(v___y_6800_);
lean_dec_ref(v___y_6799_);
lean_dec(v___y_6798_);
lean_dec(v___y_6797_);
lean_dec_ref(v___y_6796_);
return v_res_6808_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6809_, lean_object* v_x_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_, lean_object* v___y_6816_, lean_object* v___y_6817_, lean_object* v___y_6818_, lean_object* v___y_6819_, lean_object* v___y_6820_, lean_object* v___y_6821_){
_start:
{
lean_object* v___x_6823_; 
v___x_6823_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6810_);
return v___x_6823_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6824_, lean_object* v_x_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_, lean_object* v___y_6834_, lean_object* v___y_6835_, lean_object* v___y_6836_, lean_object* v___y_6837_){
_start:
{
lean_object* v_res_6838_; 
v_res_6838_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6824_, v_x_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_, v___y_6836_);
lean_dec(v___y_6836_);
lean_dec_ref(v___y_6835_);
lean_dec(v___y_6834_);
lean_dec_ref(v___y_6833_);
lean_dec(v___y_6832_);
lean_dec_ref(v___y_6831_);
lean_dec(v___y_6830_);
lean_dec_ref(v___y_6829_);
lean_dec(v___y_6828_);
lean_dec(v___y_6827_);
lean_dec_ref(v___y_6826_);
return v_res_6838_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6839_, lean_object* v_as_x27_6840_, lean_object* v_b_6841_, lean_object* v_a_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_, lean_object* v___y_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_, lean_object* v___y_6850_, lean_object* v___y_6851_, lean_object* v___y_6852_, lean_object* v___y_6853_){
_start:
{
lean_object* v___x_6855_; 
v___x_6855_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6840_, v_b_6841_, v___y_6843_, v___y_6844_, v___y_6845_, v___y_6846_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_);
return v___x_6855_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6856_, lean_object* v_as_x27_6857_, lean_object* v_b_6858_, lean_object* v_a_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_, lean_object* v___y_6868_, lean_object* v___y_6869_, lean_object* v___y_6870_, lean_object* v___y_6871_){
_start:
{
lean_object* v_res_6872_; 
v_res_6872_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6856_, v_as_x27_6857_, v_b_6858_, v_a_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_, v___y_6869_, v___y_6870_);
lean_dec(v___y_6870_);
lean_dec_ref(v___y_6869_);
lean_dec(v___y_6868_);
lean_dec_ref(v___y_6867_);
lean_dec(v___y_6866_);
lean_dec_ref(v___y_6865_);
lean_dec(v___y_6864_);
lean_dec_ref(v___y_6863_);
lean_dec(v___y_6862_);
lean_dec(v___y_6861_);
lean_dec_ref(v___y_6860_);
lean_dec(v_as_x27_6857_);
lean_dec(v_as_6856_);
return v_res_6872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6873_, lean_object* v_data_6874_, lean_object* v_ref_6875_, lean_object* v_msg_6876_, lean_object* v___y_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_, lean_object* v___y_6880_, lean_object* v___y_6881_, lean_object* v___y_6882_, lean_object* v___y_6883_, lean_object* v___y_6884_, lean_object* v___y_6885_, lean_object* v___y_6886_, lean_object* v___y_6887_){
_start:
{
lean_object* v___x_6889_; 
v___x_6889_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6873_, v_data_6874_, v_ref_6875_, v_msg_6876_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_);
return v___x_6889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6890_, lean_object* v_data_6891_, lean_object* v_ref_6892_, lean_object* v_msg_6893_, lean_object* v___y_6894_, lean_object* v___y_6895_, lean_object* v___y_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_, lean_object* v___y_6899_, lean_object* v___y_6900_, lean_object* v___y_6901_, lean_object* v___y_6902_, lean_object* v___y_6903_, lean_object* v___y_6904_, lean_object* v___y_6905_){
_start:
{
lean_object* v_res_6906_; 
v_res_6906_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6890_, v_data_6891_, v_ref_6892_, v_msg_6893_, v___y_6894_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_, v___y_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_);
lean_dec(v___y_6904_);
lean_dec_ref(v___y_6903_);
lean_dec(v___y_6902_);
lean_dec_ref(v___y_6901_);
lean_dec(v___y_6900_);
lean_dec_ref(v___y_6899_);
lean_dec(v___y_6898_);
lean_dec_ref(v___y_6897_);
lean_dec(v___y_6896_);
lean_dec(v___y_6895_);
lean_dec_ref(v___y_6894_);
return v_res_6906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6907_, lean_object* v_a_6908_, lean_object* v_a_6909_, lean_object* v_a_6910_, lean_object* v_a_6911_, lean_object* v_a_6912_, lean_object* v_a_6913_, lean_object* v_a_6914_, lean_object* v_a_6915_, lean_object* v_a_6916_, lean_object* v_a_6917_, lean_object* v_a_6918_){
_start:
{
lean_object* v___x_6920_; 
v___x_6920_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6907_, v_a_6908_, v_a_6909_, v_a_6910_, v_a_6911_, v_a_6912_, v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_, v_a_6917_, v_a_6918_);
if (lean_obj_tag(v___x_6920_) == 0)
{
lean_object* v_a_6921_; lean_object* v___x_6922_; lean_object* v___x_6924_; uint8_t v_isShared_6925_; uint8_t v_isSharedCheck_6929_; 
v_a_6921_ = lean_ctor_get(v___x_6920_, 0);
lean_inc(v_a_6921_);
lean_dec_ref_known(v___x_6920_, 1);
v___x_6922_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_6908_, v_a_6909_);
v_isSharedCheck_6929_ = !lean_is_exclusive(v___x_6922_);
if (v_isSharedCheck_6929_ == 0)
{
lean_object* v_unused_6930_; 
v_unused_6930_ = lean_ctor_get(v___x_6922_, 0);
lean_dec(v_unused_6930_);
v___x_6924_ = v___x_6922_;
v_isShared_6925_ = v_isSharedCheck_6929_;
goto v_resetjp_6923_;
}
else
{
lean_dec(v___x_6922_);
v___x_6924_ = lean_box(0);
v_isShared_6925_ = v_isSharedCheck_6929_;
goto v_resetjp_6923_;
}
v_resetjp_6923_:
{
lean_object* v___x_6927_; 
if (v_isShared_6925_ == 0)
{
lean_ctor_set(v___x_6924_, 0, v_a_6921_);
v___x_6927_ = v___x_6924_;
goto v_reusejp_6926_;
}
else
{
lean_object* v_reuseFailAlloc_6928_; 
v_reuseFailAlloc_6928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6928_, 0, v_a_6921_);
v___x_6927_ = v_reuseFailAlloc_6928_;
goto v_reusejp_6926_;
}
v_reusejp_6926_:
{
return v___x_6927_;
}
}
}
else
{
return v___x_6920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6931_, lean_object* v_a_6932_, lean_object* v_a_6933_, lean_object* v_a_6934_, lean_object* v_a_6935_, lean_object* v_a_6936_, lean_object* v_a_6937_, lean_object* v_a_6938_, lean_object* v_a_6939_, lean_object* v_a_6940_, lean_object* v_a_6941_, lean_object* v_a_6942_, lean_object* v_a_6943_){
_start:
{
lean_object* v_res_6944_; 
v_res_6944_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6931_, v_a_6932_, v_a_6933_, v_a_6934_, v_a_6935_, v_a_6936_, v_a_6937_, v_a_6938_, v_a_6939_, v_a_6940_, v_a_6941_, v_a_6942_);
lean_dec(v_a_6942_);
lean_dec_ref(v_a_6941_);
lean_dec(v_a_6940_);
lean_dec_ref(v_a_6939_);
lean_dec(v_a_6938_);
lean_dec_ref(v_a_6937_);
lean_dec(v_a_6936_);
lean_dec_ref(v_a_6935_);
lean_dec(v_a_6934_);
lean_dec(v_a_6933_);
lean_dec_ref(v_a_6932_);
lean_dec(v_passes_6931_);
return v_res_6944_;
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
