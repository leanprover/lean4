// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Attr public import Std.Tactic.BVDecide.Syntax public import Lean.Meta.Sym.ExprPtr public import Lean.Meta.Sym.SymM public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.Result public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.BVDecide.Types
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*);
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
default: 
{
lean_object* v___x_148_; 
v___x_148_ = lean_unsigned_to_nat(4u);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___boxed(lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(v_x_149_);
lean_dec(v_x_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object* v_t_151_, lean_object* v_k_152_){
_start:
{
switch(lean_obj_tag(v_t_151_))
{
case 2:
{
lean_object* v_e_153_; lean_object* v___x_154_; 
v_e_153_ = lean_ctor_get(v_t_151_, 0);
lean_inc_ref(v_e_153_);
lean_dec_ref_known(v_t_151_, 1);
v___x_154_ = lean_apply_1(v_k_152_, v_e_153_);
return v___x_154_;
}
case 4:
{
return v_k_152_;
}
default: 
{
lean_object* v_fvar_155_; lean_object* v___x_156_; 
v_fvar_155_ = lean_ctor_get(v_t_151_, 0);
lean_inc(v_fvar_155_);
lean_dec(v_t_151_);
v___x_156_ = lean_apply_1(v_k_152_, v_fvar_155_);
return v___x_156_;
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
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object* v_x_213_){
_start:
{
switch(lean_obj_tag(v_x_213_))
{
case 0:
{
lean_object* v_fvar_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; 
v_fvar_214_ = lean_ctor_get(v_x_213_, 0);
v___x_215_ = 0ULL;
v___x_216_ = l_Lean_instHashableFVarId_hash(v_fvar_214_);
v___x_217_ = lean_uint64_mix_hash(v___x_215_, v___x_216_);
return v___x_217_;
}
case 1:
{
lean_object* v_n_218_; uint64_t v___x_219_; 
v_n_218_ = lean_ctor_get(v_x_213_, 0);
v___x_219_ = 1ULL;
if (lean_obj_tag(v_n_218_) == 0)
{
uint64_t v___x_220_; 
v___x_220_ = 13067028307566252276ULL;
return v___x_220_;
}
else
{
uint64_t v_hash_221_; uint64_t v___x_222_; 
v_hash_221_ = lean_ctor_get_uint64(v_n_218_, sizeof(void*)*2);
v___x_222_ = lean_uint64_mix_hash(v___x_219_, v_hash_221_);
return v___x_222_;
}
}
case 2:
{
lean_object* v_e_223_; uint64_t v___x_224_; uint64_t v___x_225_; uint64_t v___x_226_; 
v_e_223_ = lean_ctor_get(v_x_213_, 0);
v___x_224_ = 2ULL;
v___x_225_ = l_Lean_Expr_hash(v_e_223_);
v___x_226_ = lean_uint64_mix_hash(v___x_224_, v___x_225_);
return v___x_226_;
}
case 3:
{
lean_object* v_s_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; 
v_s_227_ = lean_ctor_get(v_x_213_, 0);
v___x_228_ = 3ULL;
v___x_229_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_s_227_);
v___x_230_ = lean_uint64_mix_hash(v___x_228_, v___x_229_);
return v___x_230_;
}
default: 
{
uint64_t v___x_231_; 
v___x_231_ = 4ULL;
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object* v_x_232_){
_start:
{
uint64_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_232_);
lean_dec(v_x_232_);
v_r_234_ = lean_box_uint64(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
switch(lean_obj_tag(v_x_237_))
{
case 0:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_object* v_fvar_239_; lean_object* v_fvar_240_; uint8_t v___x_241_; 
v_fvar_239_ = lean_ctor_get(v_x_237_, 0);
v_fvar_240_ = lean_ctor_get(v_x_238_, 0);
v___x_241_ = l_Lean_instBEqFVarId_beq(v_fvar_239_, v_fvar_240_);
return v___x_241_;
}
else
{
uint8_t v___x_242_; 
v___x_242_ = 0;
return v___x_242_;
}
}
case 1:
{
if (lean_obj_tag(v_x_238_) == 1)
{
lean_object* v_n_243_; lean_object* v_n_244_; uint8_t v___x_245_; 
v_n_243_ = lean_ctor_get(v_x_237_, 0);
v_n_244_ = lean_ctor_get(v_x_238_, 0);
v___x_245_ = lean_name_eq(v_n_243_, v_n_244_);
return v___x_245_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 0;
return v___x_246_;
}
}
case 2:
{
if (lean_obj_tag(v_x_238_) == 2)
{
lean_object* v_e_247_; lean_object* v_e_248_; uint8_t v___x_249_; 
v_e_247_ = lean_ctor_get(v_x_237_, 0);
v_e_248_ = lean_ctor_get(v_x_238_, 0);
v___x_249_ = lean_expr_eqv(v_e_247_, v_e_248_);
return v___x_249_;
}
else
{
uint8_t v___x_250_; 
v___x_250_ = 0;
return v___x_250_;
}
}
case 3:
{
if (lean_obj_tag(v_x_238_) == 3)
{
lean_object* v_s_251_; lean_object* v_s_252_; 
v_s_251_ = lean_ctor_get(v_x_237_, 0);
v_s_252_ = lean_ctor_get(v_x_238_, 0);
v_x_237_ = v_s_251_;
v_x_238_ = v_s_252_;
goto _start;
}
else
{
uint8_t v___x_254_; 
v___x_254_ = 0;
return v___x_254_;
}
}
default: 
{
if (lean_obj_tag(v_x_238_) == 4)
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_257_, v_x_258_);
lean_dec(v_x_258_);
lean_dec(v_x_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object* v_s_263_){
_start:
{
if (lean_obj_tag(v_s_263_) == 3)
{
lean_object* v_s_264_; 
v_s_264_ = lean_ctor_get(v_s_263_, 0);
v_s_263_ = v_s_264_;
goto _start;
}
else
{
lean_inc(v_s_263_);
return v_s_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object* v_s_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_266_);
lean_dec(v_s_266_);
return v_res_267_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0));
v___x_270_ = l_Lean_stringToMessageData(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4));
v___x_276_ = l_Lean_stringToMessageData(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8));
v___x_282_ = l_Lean_stringToMessageData(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object* v_s_283_){
_start:
{
switch(lean_obj_tag(v_s_283_))
{
case 0:
{
lean_object* v_fvar_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_fvar_284_ = lean_ctor_get(v_s_283_, 0);
lean_inc(v_fvar_284_);
lean_dec_ref_known(v_s_283_, 1);
v___x_285_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1);
v___x_286_ = l_Lean_mkFVar(v_fvar_284_);
v___x_287_ = l_Lean_MessageData_ofExpr(v___x_286_);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
return v___x_288_;
}
case 1:
{
lean_object* v_n_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_n_289_ = lean_ctor_get(v_s_283_, 0);
lean_inc(v_n_289_);
lean_dec_ref_known(v_s_283_, 1);
v___x_290_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3);
v___x_291_ = l_Lean_MessageData_ofName(v_n_289_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
case 2:
{
lean_object* v_e_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_e_293_ = lean_ctor_get(v_s_283_, 0);
lean_inc_ref(v_e_293_);
lean_dec_ref_known(v_s_283_, 1);
v___x_294_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5);
v___x_295_ = l_Lean_MessageData_ofExpr(v_e_293_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
return v___x_296_;
}
case 3:
{
lean_object* v_s_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_s_297_ = lean_ctor_get(v_s_283_, 0);
lean_inc(v_s_297_);
lean_dec_ref_known(v_s_283_, 1);
v___x_298_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7);
v___x_299_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_297_);
lean_dec(v_s_297_);
v___x_300_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v___x_299_);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_298_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
return v___x_301_;
}
default: 
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9);
return v___x_302_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_box(0);
v___x_309_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1));
v___x_310_ = l_Lean_Expr_const___override(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default));
v___x_312_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
lean_ctor_set(v___x_314_, 2, v___x_312_);
lean_ctor_set(v___x_314_, 3, v___x_311_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp(void){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
return v___x_316_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object* v_lhs_317_, lean_object* v_rhs_318_){
_start:
{
lean_object* v_type_319_; lean_object* v_type_320_; uint8_t v___x_321_; 
v_type_319_ = lean_ctor_get(v_lhs_317_, 1);
v_type_320_ = lean_ctor_get(v_rhs_318_, 1);
v___x_321_ = lean_expr_eqv(v_type_319_, v_type_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object* v_lhs_322_, lean_object* v_rhs_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_322_, v_rhs_323_);
lean_dec_ref(v_rhs_323_);
lean_dec_ref(v_lhs_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object* v_hyp_328_){
_start:
{
lean_object* v_type_329_; uint64_t v___x_330_; 
v_type_329_ = lean_ctor_get(v_hyp_328_, 1);
v___x_330_ = l_Lean_Expr_hash(v_type_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object* v_hyp_331_){
_start:
{
uint64_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_331_);
lean_dec_ref(v_hyp_331_);
v_r_333_ = lean_box_uint64(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object* v_hyp_336_){
_start:
{
lean_object* v_type_337_; lean_object* v___x_338_; 
v_type_337_ = lean_ctor_get(v_hyp_336_, 1);
lean_inc_ref(v_type_337_);
lean_dec_ref(v_hyp_336_);
v___x_338_ = l_Lean_MessageData_ofExpr(v_type_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx(lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_unsigned_to_nat(0u);
return v___x_342_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_unsigned_to_nat(1u);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___boxed(lean_object* v_x_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx(v_x_344_);
lean_dec(v_x_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(lean_object* v_t_346_, lean_object* v_k_347_){
_start:
{
if (lean_obj_tag(v_t_346_) == 0)
{
lean_object* v_restrictedTypes_348_; lean_object* v___x_349_; 
v_restrictedTypes_348_ = lean_ctor_get(v_t_346_, 0);
lean_inc(v_restrictedTypes_348_);
lean_dec_ref_known(v_t_346_, 1);
v___x_349_ = lean_apply_1(v_k_347_, v_restrictedTypes_348_);
return v___x_349_;
}
else
{
return v_k_347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(lean_object* v_motive_350_, lean_object* v_ctorIdx_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_k_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_352_, v_k_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___boxed(lean_object* v_motive_356_, lean_object* v_ctorIdx_357_, lean_object* v_t_358_, lean_object* v_h_359_, lean_object* v_k_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(v_motive_356_, v_ctorIdx_357_, v_t_358_, v_h_359_, v_k_360_);
lean_dec(v_ctorIdx_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim___redArg(lean_object* v_t_362_, lean_object* v_solve_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_362_, v_solve_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim(lean_object* v_motive_365_, lean_object* v_t_366_, lean_object* v_h_367_, lean_object* v_solve_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_366_, v_solve_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim___redArg(lean_object* v_t_370_, lean_object* v_push_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_370_, v_push_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim(lean_object* v_motive_373_, lean_object* v_t_374_, lean_object* v_h_375_, lean_object* v_push_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_374_, v_push_376_);
return v___x_377_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
uint8_t v___x_379_; 
v___x_379_ = 0;
return v___x_379_;
}
else
{
uint8_t v___x_380_; 
v___x_380_ = 1;
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush___boxed(lean_object* v_x_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_x_381_);
lean_dec(v_x_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v_restrictedTypes_385_; 
v_restrictedTypes_385_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_restrictedTypes_385_);
return v_restrictedTypes_385_;
}
else
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes___boxed(lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_x_387_);
lean_dec(v_x_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(lean_object* v_mode_389_, lean_object* v_config_390_){
_start:
{
if (lean_obj_tag(v_mode_389_) == 0)
{
return v_config_390_;
}
else
{
lean_object* v_timeout_391_; uint8_t v_trimProofs_392_; uint8_t v_binaryProofs_393_; uint8_t v_acNf_394_; uint8_t v_graphviz_395_; lean_object* v_maxSteps_396_; uint8_t v_shortCircuit_397_; uint8_t v_solverMode_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_timeout_391_ = lean_ctor_get(v_config_390_, 0);
v_trimProofs_392_ = lean_ctor_get_uint8(v_config_390_, sizeof(void*)*2);
v_binaryProofs_393_ = lean_ctor_get_uint8(v_config_390_, sizeof(void*)*2 + 1);
v_acNf_394_ = lean_ctor_get_uint8(v_config_390_, sizeof(void*)*2 + 2);
v_graphviz_395_ = lean_ctor_get_uint8(v_config_390_, sizeof(void*)*2 + 8);
v_maxSteps_396_ = lean_ctor_get(v_config_390_, 1);
v_shortCircuit_397_ = lean_ctor_get_uint8(v_config_390_, sizeof(void*)*2 + 9);
v_solverMode_398_ = lean_ctor_get_uint8(v_config_390_, sizeof(void*)*2 + 10);
v_isSharedCheck_406_ = !lean_is_exclusive(v_config_390_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v_config_390_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_maxSteps_396_);
lean_inc(v_timeout_391_);
lean_dec(v_config_390_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
uint8_t v___x_402_; lean_object* v___x_404_; 
v___x_402_ = 0;
if (v_isShared_401_ == 0)
{
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_timeout_391_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_maxSteps_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*2, v_trimProofs_392_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*2 + 1, v_binaryProofs_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*2 + 2, v_acNf_394_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*2 + 8, v_graphviz_395_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*2 + 9, v_shortCircuit_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*2 + 10, v_solverMode_398_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*2 + 3, v___x_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*2 + 4, v___x_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*2 + 5, v___x_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*2 + 6, v___x_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*2 + 7, v___x_402_);
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig___boxed(lean_object* v_mode_407_, lean_object* v_config_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_407_, v_config_408_);
lean_dec(v_mode_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object* v_mode_410_, lean_object* v_config_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_410_, v_config_411_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_mode_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx(uint8_t v_x_414_){
_start:
{
if (v_x_414_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_unsigned_to_nat(0u);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = lean_unsigned_to_nat(1u);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___boxed(lean_object* v_x_417_){
_start:
{
uint8_t v_x_boxed_418_; lean_object* v_res_419_; 
v_x_boxed_418_ = lean_unbox(v_x_417_);
v_res_419_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx(v_x_boxed_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(lean_object* v_k_420_){
_start:
{
lean_inc(v_k_420_);
return v_k_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(v_k_421_);
lean_dec(v_k_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(lean_object* v_motive_423_, lean_object* v_ctorIdx_424_, uint8_t v_t_425_, lean_object* v_h_426_, lean_object* v_k_427_){
_start:
{
lean_inc(v_k_427_);
return v_k_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___boxed(lean_object* v_motive_428_, lean_object* v_ctorIdx_429_, lean_object* v_t_430_, lean_object* v_h_431_, lean_object* v_k_432_){
_start:
{
uint8_t v_t_boxed_433_; lean_object* v_res_434_; 
v_t_boxed_433_ = lean_unbox(v_t_430_);
v_res_434_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(v_motive_428_, v_ctorIdx_429_, v_t_boxed_433_, v_h_431_, v_k_432_);
lean_dec(v_k_432_);
lean_dec(v_ctorIdx_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_435_){
_start:
{
lean_inc(v_rewrite_435_);
return v_rewrite_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(v_rewrite_436_);
lean_dec(v_rewrite_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(lean_object* v_motive_438_, uint8_t v_t_439_, lean_object* v_h_440_, lean_object* v_rewrite_441_){
_start:
{
lean_inc(v_rewrite_441_);
return v_rewrite_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___boxed(lean_object* v_motive_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_rewrite_445_){
_start:
{
uint8_t v_t_boxed_446_; lean_object* v_res_447_; 
v_t_boxed_446_ = lean_unbox(v_t_443_);
v_res_447_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(v_motive_442_, v_t_boxed_446_, v_h_444_, v_rewrite_445_);
lean_dec(v_rewrite_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(lean_object* v_ac_448_){
_start:
{
lean_inc(v_ac_448_);
return v_ac_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg___boxed(lean_object* v_ac_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(v_ac_449_);
lean_dec(v_ac_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(lean_object* v_motive_451_, uint8_t v_t_452_, lean_object* v_h_453_, lean_object* v_ac_454_){
_start:
{
lean_inc(v_ac_454_);
return v_ac_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___boxed(lean_object* v_motive_455_, lean_object* v_t_456_, lean_object* v_h_457_, lean_object* v_ac_458_){
_start:
{
uint8_t v_t_boxed_459_; lean_object* v_res_460_; 
v_t_boxed_459_ = lean_unbox(v_t_456_);
v_res_460_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(v_motive_455_, v_t_boxed_459_, v_h_457_, v_ac_458_);
lean_dec(v_ac_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx(uint8_t v_x_461_){
_start:
{
if (v_x_461_ == 0)
{
lean_object* v___x_462_; 
v___x_462_ = lean_unsigned_to_nat(0u);
return v___x_462_;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = lean_unsigned_to_nat(1u);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___boxed(lean_object* v_x_464_){
_start:
{
uint8_t v_x_boxed_465_; lean_object* v_res_466_; 
v_x_boxed_465_ = lean_unbox(v_x_464_);
v_res_466_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx(v_x_boxed_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(lean_object* v_k_467_){
_start:
{
lean_inc(v_k_467_);
return v_k_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(v_k_468_);
lean_dec(v_k_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(lean_object* v_motive_470_, lean_object* v_ctorIdx_471_, uint8_t v_t_472_, lean_object* v_h_473_, lean_object* v_k_474_){
_start:
{
lean_inc(v_k_474_);
return v_k_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___boxed(lean_object* v_motive_475_, lean_object* v_ctorIdx_476_, lean_object* v_t_477_, lean_object* v_h_478_, lean_object* v_k_479_){
_start:
{
uint8_t v_t_boxed_480_; lean_object* v_res_481_; 
v_t_boxed_480_ = lean_unbox(v_t_477_);
v_res_481_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(v_motive_475_, v_ctorIdx_476_, v_t_boxed_480_, v_h_478_, v_k_479_);
lean_dec(v_k_479_);
lean_dec(v_ctorIdx_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_482_){
_start:
{
lean_inc(v_rewrite_482_);
return v_rewrite_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(v_rewrite_483_);
lean_dec(v_rewrite_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(lean_object* v_motive_485_, uint8_t v_t_486_, lean_object* v_h_487_, lean_object* v_rewrite_488_){
_start:
{
lean_inc(v_rewrite_488_);
return v_rewrite_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___boxed(lean_object* v_motive_489_, lean_object* v_t_490_, lean_object* v_h_491_, lean_object* v_rewrite_492_){
_start:
{
uint8_t v_t_boxed_493_; lean_object* v_res_494_; 
v_t_boxed_493_ = lean_unbox(v_t_490_);
v_res_494_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(v_motive_489_, v_t_boxed_493_, v_h_491_, v_rewrite_492_);
lean_dec(v_rewrite_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(lean_object* v_reduction_495_){
_start:
{
lean_inc(v_reduction_495_);
return v_reduction_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg___boxed(lean_object* v_reduction_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(v_reduction_496_);
lean_dec(v_reduction_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(lean_object* v_motive_498_, uint8_t v_t_499_, lean_object* v_h_500_, lean_object* v_reduction_501_){
_start:
{
lean_inc(v_reduction_501_);
return v_reduction_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___boxed(lean_object* v_motive_502_, lean_object* v_t_503_, lean_object* v_h_504_, lean_object* v_reduction_505_){
_start:
{
uint8_t v_t_boxed_506_; lean_object* v_res_507_; 
v_t_boxed_506_ = lean_unbox(v_t_503_);
v_res_507_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(v_motive_502_, v_t_boxed_506_, v_h_504_, v_reduction_505_);
lean_dec(v_reduction_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(uint8_t v_x_508_, lean_object* v_x_509_){
_start:
{
if (v_x_508_ == 0)
{
lean_object* v_rewriteSimp_510_; 
v_rewriteSimp_510_ = lean_ctor_get(v_x_509_, 1);
lean_inc_ref(v_rewriteSimp_510_);
return v_rewriteSimp_510_;
}
else
{
lean_object* v_ac_511_; 
v_ac_511_ = lean_ctor_get(v_x_509_, 3);
lean_inc_ref(v_ac_511_);
return v_ac_511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get___boxed(lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
uint8_t v_x_15__boxed_514_; lean_object* v_res_515_; 
v_x_15__boxed_514_ = lean_unbox(v_x_512_);
v_res_515_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_x_15__boxed_514_, v_x_513_);
lean_dec_ref(v_x_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(uint8_t v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
if (v_x_516_ == 0)
{
lean_object* v_reduction_519_; lean_object* v_rewriteDSimp_520_; lean_object* v_ac_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v_reduction_519_ = lean_ctor_get(v_x_518_, 0);
v_rewriteDSimp_520_ = lean_ctor_get(v_x_518_, 2);
v_ac_521_ = lean_ctor_get(v_x_518_, 3);
v_isSharedCheck_528_ = !lean_is_exclusive(v_x_518_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_x_518_, 1);
lean_dec(v_unused_529_);
v___x_523_ = v_x_518_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_ac_521_);
lean_inc(v_rewriteDSimp_520_);
lean_inc(v_reduction_519_);
lean_dec(v_x_518_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_x_517_);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_reduction_519_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_x_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_rewriteDSimp_520_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_ac_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_reduction_530_; lean_object* v_rewriteSimp_531_; lean_object* v_rewriteDSimp_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_reduction_530_ = lean_ctor_get(v_x_518_, 0);
v_rewriteSimp_531_ = lean_ctor_get(v_x_518_, 1);
v_rewriteDSimp_532_ = lean_ctor_get(v_x_518_, 2);
v_isSharedCheck_539_ = !lean_is_exclusive(v_x_518_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_x_518_, 3);
lean_dec(v_unused_540_);
v___x_534_ = v_x_518_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_rewriteDSimp_532_);
lean_inc(v_rewriteSimp_531_);
lean_inc(v_reduction_530_);
lean_dec(v_x_518_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 3, v_x_517_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_reduction_530_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_rewriteSimp_531_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_rewriteDSimp_532_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_x_517_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set___boxed(lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
uint8_t v_x_28__boxed_544_; lean_object* v_res_545_; 
v_x_28__boxed_544_ = lean_unbox(v_x_541_);
v_res_545_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_x_28__boxed_544_, v_x_542_, v_x_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(uint8_t v_x_546_, lean_object* v_x_547_){
_start:
{
if (v_x_546_ == 0)
{
lean_object* v_rewriteDSimp_548_; 
v_rewriteDSimp_548_ = lean_ctor_get(v_x_547_, 2);
lean_inc_ref(v_rewriteDSimp_548_);
return v_rewriteDSimp_548_;
}
else
{
lean_object* v_reduction_549_; 
v_reduction_549_ = lean_ctor_get(v_x_547_, 0);
lean_inc_ref(v_reduction_549_);
return v_reduction_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get___boxed(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
uint8_t v_x_15__boxed_552_; lean_object* v_res_553_; 
v_x_15__boxed_552_ = lean_unbox(v_x_550_);
v_res_553_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_x_15__boxed_552_, v_x_551_);
lean_dec_ref(v_x_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(uint8_t v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
if (v_x_554_ == 0)
{
lean_object* v_reduction_557_; lean_object* v_rewriteSimp_558_; lean_object* v_ac_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_reduction_557_ = lean_ctor_get(v_x_556_, 0);
v_rewriteSimp_558_ = lean_ctor_get(v_x_556_, 1);
v_ac_559_ = lean_ctor_get(v_x_556_, 3);
v_isSharedCheck_566_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_x_556_, 2);
lean_dec(v_unused_567_);
v___x_561_ = v_x_556_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_ac_559_);
lean_inc(v_rewriteSimp_558_);
lean_inc(v_reduction_557_);
lean_dec(v_x_556_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 2, v_x_555_);
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_reduction_557_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_rewriteSimp_558_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_x_555_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_ac_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
else
{
lean_object* v_rewriteSimp_568_; lean_object* v_rewriteDSimp_569_; lean_object* v_ac_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_rewriteSimp_568_ = lean_ctor_get(v_x_556_, 1);
v_rewriteDSimp_569_ = lean_ctor_get(v_x_556_, 2);
v_ac_570_ = lean_ctor_get(v_x_556_, 3);
v_isSharedCheck_577_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v_x_556_, 0);
lean_dec(v_unused_578_);
v___x_572_ = v_x_556_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_ac_570_);
lean_inc(v_rewriteDSimp_569_);
lean_inc(v_rewriteSimp_568_);
lean_dec(v_x_556_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_x_555_);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_x_555_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_rewriteSimp_568_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_rewriteDSimp_569_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_ac_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set___boxed(lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
uint8_t v_x_28__boxed_582_; lean_object* v_res_583_; 
v_x_28__boxed_582_ = lean_unbox(v_x_579_);
v_res_583_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_x_28__boxed_582_, v_x_580_, v_x_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object* v_hyp_589_, lean_object* v_result_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
if (lean_obj_tag(v_result_590_) == 0)
{
lean_object* v___x_597_; 
lean_dec_ref_known(v_result_590_, 0);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v_hyp_589_);
return v___x_597_;
}
else
{
lean_object* v_e_x27_598_; lean_object* v_proof_599_; lean_object* v_name_600_; lean_object* v_type_601_; lean_object* v_value_602_; lean_object* v_source_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_632_; 
v_e_x27_598_ = lean_ctor_get(v_result_590_, 0);
lean_inc_ref(v_e_x27_598_);
v_proof_599_ = lean_ctor_get(v_result_590_, 1);
lean_inc_ref(v_proof_599_);
lean_dec_ref_known(v_result_590_, 2);
v_name_600_ = lean_ctor_get(v_hyp_589_, 0);
v_type_601_ = lean_ctor_get(v_hyp_589_, 1);
v_value_602_ = lean_ctor_get(v_hyp_589_, 2);
v_source_603_ = lean_ctor_get(v_hyp_589_, 3);
v_isSharedCheck_632_ = !lean_is_exclusive(v_hyp_589_);
if (v_isSharedCheck_632_ == 0)
{
v___x_605_ = v_hyp_589_;
v_isShared_606_ = v_isSharedCheck_632_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_source_603_);
lean_inc(v_value_602_);
lean_inc(v_type_601_);
lean_inc(v_name_600_);
lean_dec(v_hyp_589_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_632_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; 
lean_inc_ref(v_type_601_);
v___x_607_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_601_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_623_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_623_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_623_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_623_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_612_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2));
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v_a_608_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = l_Lean_mkConst(v___x_612_, v___x_614_);
lean_inc_ref(v_e_x27_598_);
v___x_616_ = l_Lean_mkApp4(v___x_615_, v_type_601_, v_e_x27_598_, v_proof_599_, v_value_602_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 2, v___x_616_);
lean_ctor_set(v___x_605_, 1, v_e_x27_598_);
v___x_618_ = v___x_605_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_name_600_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_e_x27_598_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_source_603_);
v___x_618_ = v_reuseFailAlloc_622_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_618_);
v___x_620_ = v___x_610_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_del_object(v___x_605_);
lean_dec(v_source_603_);
lean_dec_ref(v_value_602_);
lean_dec_ref(v_type_601_);
lean_dec(v_name_600_);
lean_dec_ref(v_proof_599_);
lean_dec_ref(v_e_x27_598_);
v_a_624_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_607_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_607_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object* v_hyp_633_, lean_object* v_result_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_633_, v_result_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object* v_hyp_642_, lean_object* v_result_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_642_, v_result_643_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object* v_hyp_652_, lean_object* v_result_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_652_, v_result_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object* v_hyp_662_, lean_object* v_result_663_){
_start:
{
lean_object* v_name_665_; lean_object* v_type_666_; lean_object* v_value_667_; lean_object* v_source_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_677_; 
v_name_665_ = lean_ctor_get(v_hyp_662_, 0);
v_type_666_ = lean_ctor_get(v_hyp_662_, 1);
v_value_667_ = lean_ctor_get(v_hyp_662_, 2);
v_source_668_ = lean_ctor_get(v_hyp_662_, 3);
v_isSharedCheck_677_ = !lean_is_exclusive(v_hyp_662_);
if (v_isSharedCheck_677_ == 0)
{
v___x_670_ = v_hyp_662_;
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_source_668_);
lean_inc(v_value_667_);
lean_inc(v_type_666_);
lean_inc(v_name_665_);
lean_dec(v_hyp_662_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_type_666_, v_result_663_);
lean_dec_ref(v_type_666_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_name_665_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_value_667_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_source_668_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object* v_hyp_678_, lean_object* v_result_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_678_, v_result_679_);
lean_dec_ref(v_result_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object* v_hyp_682_, lean_object* v_result_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_682_, v_result_683_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object* v_hyp_692_, lean_object* v_result_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_692_, v_result_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec_ref(v_result_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_702_){
_start:
{
lean_object* v_config_704_; lean_object* v___x_705_; 
v_config_704_ = lean_ctor_get(v_a_702_, 0);
lean_inc_ref(v_config_704_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v_config_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_706_);
lean_dec_ref(v_a_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_config_721_; lean_object* v___x_722_; 
v_config_721_ = lean_ctor_get(v_a_709_, 0);
lean_inc_ref(v_config_721_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_config_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(lean_object* v_a_736_){
_start:
{
lean_object* v_mode_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_mode_738_ = lean_ctor_get(v_a_736_, 1);
v___x_739_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_738_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg___boxed(lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(v_a_741_);
lean_dec_ref(v_a_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_mode_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_mode_756_ = lean_ctor_get(v_a_744_, 1);
v___x_757_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___boxed(lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(lean_object* v_a_772_){
_start:
{
lean_object* v_mode_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_mode_774_ = lean_ctor_get(v_a_772_, 1);
v___x_775_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_774_);
v___x_776_ = lean_box(v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg___boxed(lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(v_a_778_);
lean_dec_ref(v_a_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_mode_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_mode_793_ = lean_ctor_get(v_a_781_, 1);
v___x_794_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_793_);
v___x_795_ = lean_box(v___x_794_);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___boxed(lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(lean_object* v_a_810_){
_start:
{
lean_object* v___x_812_; lean_object* v_target_813_; lean_object* v___x_814_; 
v___x_812_ = lean_st_ref_get(v_a_810_);
v_target_813_ = lean_ctor_get(v___x_812_, 2);
lean_inc_ref(v_target_813_);
lean_dec(v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v_target_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg___boxed(lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(v_a_815_);
lean_dec(v_a_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_target_831_; lean_object* v___x_832_; 
v___x_830_ = lean_st_ref_get(v_a_819_);
v_target_831_ = lean_ctor_get(v___x_830_, 2);
lean_inc_ref(v_target_831_);
lean_dec(v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v_target_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___boxed(lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; lean_object* v_target_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_st_ref_get(v_a_846_);
v_target_849_ = lean_ctor_get(v___x_848_, 2);
lean_inc_ref(v_target_849_);
lean_dec(v___x_848_);
v___x_850_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_849_);
lean_dec_ref(v_target_849_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg___boxed(lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(v_a_852_);
lean_dec(v_a_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_target_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = lean_st_ref_get(v_a_856_);
v_target_868_ = lean_ctor_get(v___x_867_, 2);
lean_inc_ref(v_target_868_);
lean_dec(v___x_867_);
v___x_869_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_868_);
lean_dec_ref(v_target_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed(lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(lean_object* v_target_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; lean_object* v_caches_888_; lean_object* v_typeAnalysis_889_; lean_object* v_hypotheses_890_; uint8_t v_didChange_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_901_; 
v___x_887_ = lean_st_ref_take(v_a_885_);
v_caches_888_ = lean_ctor_get(v___x_887_, 0);
v_typeAnalysis_889_ = lean_ctor_get(v___x_887_, 1);
v_hypotheses_890_ = lean_ctor_get(v___x_887_, 3);
v_didChange_891_ = lean_ctor_get_uint8(v___x_887_, sizeof(void*)*4);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v___x_887_, 2);
lean_dec(v_unused_902_);
v___x_893_ = v___x_887_;
v_isShared_894_ = v_isSharedCheck_901_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_hypotheses_890_);
lean_inc(v_typeAnalysis_889_);
lean_inc(v_caches_888_);
lean_dec(v___x_887_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_901_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 2, v_target_884_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_caches_888_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_typeAnalysis_889_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_target_884_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v_hypotheses_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*4, v_didChange_891_);
v___x_897_ = v_reuseFailAlloc_900_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_st_ref_put(v_a_885_, v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_895_);
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg___boxed(lean_object* v_target_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(v_target_903_, v_a_904_);
lean_dec(v_a_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(lean_object* v_target_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_caches_921_; lean_object* v_typeAnalysis_922_; lean_object* v_hypotheses_923_; uint8_t v_didChange_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_934_; 
v___x_920_ = lean_st_ref_take(v_a_909_);
v_caches_921_ = lean_ctor_get(v___x_920_, 0);
v_typeAnalysis_922_ = lean_ctor_get(v___x_920_, 1);
v_hypotheses_923_ = lean_ctor_get(v___x_920_, 3);
v_didChange_924_ = lean_ctor_get_uint8(v___x_920_, sizeof(void*)*4);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v___x_920_, 2);
lean_dec(v_unused_935_);
v___x_926_ = v___x_920_;
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_hypotheses_923_);
lean_inc(v_typeAnalysis_922_);
lean_inc(v_caches_921_);
lean_dec(v___x_920_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = lean_box(0);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 2, v_target_907_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_caches_921_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_typeAnalysis_922_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_target_907_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_hypotheses_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_933_, sizeof(void*)*4, v_didChange_924_);
v___x_930_ = v_reuseFailAlloc_933_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_st_ref_put(v_a_909_, v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_928_);
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___boxed(lean_object* v_target_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(v_target_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
return v_res_949_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0(void){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_instMonadControlReaderT___redArg();
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2(void){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_instMonadEIO___redArg();
return v___x_952_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2);
v___x_954_ = l_StateRefT_x27_instMonad___redArg(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(lean_object* v_x_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v___x_971_; lean_object* v_target_972_; 
v___x_971_ = lean_st_ref_get(v_a_960_);
v_target_972_ = lean_ctor_get(v___x_971_, 2);
lean_inc_ref(v_target_972_);
lean_dec(v___x_971_);
if (lean_obj_tag(v_target_972_) == 1)
{
lean_object* v_goal_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1101_; 
v_goal_973_ = lean_ctor_get(v_target_972_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_target_972_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_975_ = v_target_972_;
v_isShared_976_ = v_isSharedCheck_1101_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_goal_973_);
lean_dec(v_target_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1101_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_toApplicative_980_; lean_object* v_toFunctor_981_; lean_object* v_toSeq_982_; lean_object* v_toSeqLeft_983_; lean_object* v_toSeqRight_984_; lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___x_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v_toApplicative_1013_; lean_object* v_toFunctor_1014_; lean_object* v_toSeq_1015_; lean_object* v_toSeqLeft_1016_; lean_object* v_toSeqRight_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_toApplicative_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1099_; 
v___x_977_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_978_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_979_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_980_ = lean_ctor_get(v___x_979_, 0);
v_toFunctor_981_ = lean_ctor_get(v_toApplicative_980_, 0);
v_toSeq_982_ = lean_ctor_get(v_toApplicative_980_, 2);
v_toSeqLeft_983_ = lean_ctor_get(v_toApplicative_980_, 3);
v_toSeqRight_984_ = lean_ctor_get(v_toApplicative_980_, 4);
v___f_985_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_986_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_981_, 2);
v___f_987_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_987_, 0, v_toFunctor_981_);
v___f_988_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_988_, 0, v_toFunctor_981_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v___f_987_);
lean_ctor_set(v___x_989_, 1, v___f_988_);
lean_inc(v_toSeqRight_984_);
v___f_990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_990_, 0, v_toSeqRight_984_);
lean_inc(v_toSeqLeft_983_);
v___f_991_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_991_, 0, v_toSeqLeft_983_);
lean_inc(v_toSeq_982_);
v___f_992_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_992_, 0, v_toSeq_982_);
v___x_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_993_, 0, v___x_989_);
lean_ctor_set(v___x_993_, 1, v___f_985_);
lean_ctor_set(v___x_993_, 2, v___f_992_);
lean_ctor_set(v___x_993_, 3, v___f_991_);
lean_ctor_set(v___x_993_, 4, v___f_990_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___f_986_);
v___x_995_ = l_StateRefT_x27_instMonad___redArg(v___x_994_);
v___x_996_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_996_, 0, lean_box(0));
lean_closure_set(v___x_996_, 1, lean_box(0));
lean_closure_set(v___x_996_, 2, v___x_995_);
v___x_997_ = l_instMonadControlTOfPure___redArg(v___x_996_);
lean_inc_ref(v___x_997_);
v___f_998_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_998_, 0, v___x_978_);
lean_closure_set(v___f_998_, 1, v___x_997_);
v___f_999_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_999_, 0, v___x_978_);
lean_closure_set(v___f_999_, 1, v___x_997_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___f_998_);
lean_ctor_set(v___x_1000_, 1, v___f_999_);
lean_inc_ref(v___x_1000_);
v___f_1001_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1001_, 0, v___x_977_);
lean_closure_set(v___f_1001_, 1, v___x_1000_);
v___f_1002_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1002_, 0, v___x_977_);
lean_closure_set(v___f_1002_, 1, v___x_1000_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___f_1001_);
lean_ctor_set(v___x_1003_, 1, v___f_1002_);
lean_inc_ref(v___x_1003_);
v___f_1004_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1004_, 0, v___x_978_);
lean_closure_set(v___f_1004_, 1, v___x_1003_);
v___f_1005_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1005_, 0, v___x_978_);
lean_closure_set(v___f_1005_, 1, v___x_1003_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___f_1004_);
lean_ctor_set(v___x_1006_, 1, v___f_1005_);
lean_inc_ref(v___x_1006_);
v___f_1007_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1007_, 0, v___x_977_);
lean_closure_set(v___f_1007_, 1, v___x_1006_);
v___f_1008_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1008_, 0, v___x_977_);
lean_closure_set(v___f_1008_, 1, v___x_1006_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___f_1007_);
lean_ctor_set(v___x_1009_, 1, v___f_1008_);
lean_inc_ref(v___x_1009_);
v___f_1010_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1010_, 0, v___x_977_);
lean_closure_set(v___f_1010_, 1, v___x_1009_);
v___f_1011_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1011_, 0, v___x_977_);
lean_closure_set(v___f_1011_, 1, v___x_1009_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___f_1010_);
lean_ctor_set(v___x_1012_, 1, v___f_1011_);
v_toApplicative_1013_ = lean_ctor_get(v___x_979_, 0);
v_toFunctor_1014_ = lean_ctor_get(v_toApplicative_1013_, 0);
v_toSeq_1015_ = lean_ctor_get(v_toApplicative_1013_, 2);
v_toSeqLeft_1016_ = lean_ctor_get(v_toApplicative_1013_, 3);
v_toSeqRight_1017_ = lean_ctor_get(v_toApplicative_1013_, 4);
lean_inc_ref_n(v_toFunctor_1014_, 2);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toFunctor_1014_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toFunctor_1014_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___f_1018_);
lean_ctor_set(v___x_1020_, 1, v___f_1019_);
lean_inc(v_toSeqRight_1017_);
v___f_1021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1021_, 0, v_toSeqRight_1017_);
lean_inc(v_toSeqLeft_1016_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toSeqLeft_1016_);
lean_inc(v_toSeq_1015_);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toSeq_1015_);
v___x_1024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1020_);
lean_ctor_set(v___x_1024_, 1, v___f_985_);
lean_ctor_set(v___x_1024_, 2, v___f_1023_);
lean_ctor_set(v___x_1024_, 3, v___f_1022_);
lean_ctor_set(v___x_1024_, 4, v___f_1021_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___f_986_);
v___x_1026_ = l_StateRefT_x27_instMonad___redArg(v___x_1025_);
v_toApplicative_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1026_, 1);
lean_dec(v_unused_1100_);
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1099_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_toApplicative_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1099_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_toFunctor_1031_; lean_object* v_toSeq_1032_; lean_object* v_toSeqLeft_1033_; lean_object* v_toSeqRight_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1097_; 
v_toFunctor_1031_ = lean_ctor_get(v_toApplicative_1027_, 0);
v_toSeq_1032_ = lean_ctor_get(v_toApplicative_1027_, 2);
v_toSeqLeft_1033_ = lean_ctor_get(v_toApplicative_1027_, 3);
v_toSeqRight_1034_ = lean_ctor_get(v_toApplicative_1027_, 4);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_toApplicative_1027_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v_toApplicative_1027_, 1);
lean_dec(v_unused_1098_);
v___x_1036_ = v_toApplicative_1027_;
v_isShared_1037_ = v_isSharedCheck_1097_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_toSeqRight_1034_);
lean_inc(v_toSeqLeft_1033_);
lean_inc(v_toSeq_1032_);
lean_inc(v_toFunctor_1031_);
lean_dec(v_toApplicative_1027_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1097_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___x_1047_; 
v___f_1038_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1039_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1031_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toFunctor_1031_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toFunctor_1031_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___f_1040_);
lean_ctor_set(v___x_1042_, 1, v___f_1041_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toSeqRight_1034_);
v___f_1044_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1044_, 0, v_toSeqLeft_1033_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toSeq_1032_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___f_1043_);
lean_ctor_set(v___x_1036_, 3, v___f_1044_);
lean_ctor_set(v___x_1036_, 2, v___f_1045_);
lean_ctor_set(v___x_1036_, 1, v___f_1038_);
lean_ctor_set(v___x_1036_, 0, v___x_1042_);
v___x_1047_ = v___x_1036_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___f_1038_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v___f_1045_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v___f_1044_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v___f_1043_);
v___x_1047_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 1, v___f_1039_);
lean_ctor_set(v___x_1029_, 0, v___x_1047_);
v___x_1049_ = v___x_1029_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___f_1039_);
v___x_1049_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_mvarId_1055_; lean_object* v___x_1056_; lean_object* v___x_5100__overap_1057_; lean_object* v___x_1058_; 
v___x_1050_ = l_StateRefT_x27_instMonad___redArg(v___x_1049_);
v___x_1051_ = l_ReaderT_instMonad___redArg(v___x_1050_);
v___x_1052_ = l_StateRefT_x27_instMonad___redArg(v___x_1051_);
v___x_1053_ = l_ReaderT_instMonad___redArg(v___x_1052_);
v___x_1054_ = l_ReaderT_instMonad___redArg(v___x_1053_);
v_mvarId_1055_ = lean_ctor_get(v_goal_973_, 1);
lean_inc(v_mvarId_1055_);
v___x_1056_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1056_, 0, lean_box(0));
lean_closure_set(v___x_1056_, 1, v_goal_973_);
lean_closure_set(v___x_1056_, 2, v_x_959_);
v___x_5100__overap_1057_ = l_Lean_MVarId_withContext___redArg(v___x_1012_, v___x_1054_, v_mvarId_1055_, v___x_1056_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v_a_967_);
lean_inc_ref(v_a_966_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v_a_961_);
v___x_1058_ = lean_apply_10(v___x_5100__overap_1057_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, lean_box(0));
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1086_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1086_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1086_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1066_; 
v_fst_1063_ = lean_ctor_get(v_a_1059_, 0);
lean_inc(v_fst_1063_);
v_snd_1064_ = lean_ctor_get(v_a_1059_, 1);
lean_inc(v_snd_1064_);
lean_dec(v_a_1059_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_snd_1064_);
v___x_1066_ = v___x_975_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_snd_1064_);
v___x_1066_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v_caches_1068_; lean_object* v_typeAnalysis_1069_; lean_object* v_hypotheses_1070_; uint8_t v_didChange_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1083_; 
v___x_1067_ = lean_st_ref_take(v_a_960_);
v_caches_1068_ = lean_ctor_get(v___x_1067_, 0);
v_typeAnalysis_1069_ = lean_ctor_get(v___x_1067_, 1);
v_hypotheses_1070_ = lean_ctor_get(v___x_1067_, 3);
v_didChange_1071_ = lean_ctor_get_uint8(v___x_1067_, sizeof(void*)*4);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v___x_1067_, 2);
lean_dec(v_unused_1084_);
v___x_1073_ = v___x_1067_;
v_isShared_1074_ = v_isSharedCheck_1083_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_hypotheses_1070_);
lean_inc(v_typeAnalysis_1069_);
lean_inc(v_caches_1068_);
lean_dec(v___x_1067_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1083_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 2, v___x_1066_);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_caches_1068_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_typeAnalysis_1069_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_hypotheses_1070_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*4, v_didChange_1071_);
v___x_1076_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = lean_st_ref_put(v_a_960_, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_fst_1063_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1078_);
v___x_1080_ = v___x_1061_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_del_object(v___x_975_);
v_a_1087_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1058_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1058_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
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
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec_ref(v_target_972_);
lean_dec_ref(v_x_959_);
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___boxed(lean_object* v_x_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(v_x_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec(v_a_1105_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(lean_object* v_00_u03b1_1117_, lean_object* v_x_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_target_1132_; 
v___x_1131_ = lean_st_ref_get(v_a_1120_);
v_target_1132_ = lean_ctor_get(v___x_1131_, 2);
lean_inc_ref(v_target_1132_);
lean_dec(v___x_1131_);
if (lean_obj_tag(v_target_1132_) == 1)
{
lean_object* v_goal_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1261_; 
v_goal_1133_ = lean_ctor_get(v_target_1132_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_target_1132_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1135_ = v_target_1132_;
v_isShared_1136_ = v_isSharedCheck_1261_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_goal_1133_);
lean_dec(v_target_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1261_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_toApplicative_1140_; lean_object* v_toFunctor_1141_; lean_object* v_toSeq_1142_; lean_object* v_toSeqLeft_1143_; lean_object* v_toSeqRight_1144_; lean_object* v___f_1145_; lean_object* v___f_1146_; lean_object* v___f_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v_toApplicative_1173_; lean_object* v_toFunctor_1174_; lean_object* v_toSeq_1175_; lean_object* v_toSeqLeft_1176_; lean_object* v_toSeqRight_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_toApplicative_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1259_; 
v___x_1137_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_1138_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_1139_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_1140_ = lean_ctor_get(v___x_1139_, 0);
v_toFunctor_1141_ = lean_ctor_get(v_toApplicative_1140_, 0);
v_toSeq_1142_ = lean_ctor_get(v_toApplicative_1140_, 2);
v_toSeqLeft_1143_ = lean_ctor_get(v_toApplicative_1140_, 3);
v_toSeqRight_1144_ = lean_ctor_get(v_toApplicative_1140_, 4);
v___f_1145_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_1146_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_1141_, 2);
v___f_1147_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1147_, 0, v_toFunctor_1141_);
v___f_1148_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1148_, 0, v_toFunctor_1141_);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___f_1147_);
lean_ctor_set(v___x_1149_, 1, v___f_1148_);
lean_inc(v_toSeqRight_1144_);
v___f_1150_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1150_, 0, v_toSeqRight_1144_);
lean_inc(v_toSeqLeft_1143_);
v___f_1151_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1151_, 0, v_toSeqLeft_1143_);
lean_inc(v_toSeq_1142_);
v___f_1152_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1152_, 0, v_toSeq_1142_);
v___x_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1149_);
lean_ctor_set(v___x_1153_, 1, v___f_1145_);
lean_ctor_set(v___x_1153_, 2, v___f_1152_);
lean_ctor_set(v___x_1153_, 3, v___f_1151_);
lean_ctor_set(v___x_1153_, 4, v___f_1150_);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___f_1146_);
v___x_1155_ = l_StateRefT_x27_instMonad___redArg(v___x_1154_);
v___x_1156_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1156_, 0, lean_box(0));
lean_closure_set(v___x_1156_, 1, lean_box(0));
lean_closure_set(v___x_1156_, 2, v___x_1155_);
v___x_1157_ = l_instMonadControlTOfPure___redArg(v___x_1156_);
lean_inc_ref(v___x_1157_);
v___f_1158_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1158_, 0, v___x_1138_);
lean_closure_set(v___f_1158_, 1, v___x_1157_);
v___f_1159_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1159_, 0, v___x_1138_);
lean_closure_set(v___f_1159_, 1, v___x_1157_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___f_1158_);
lean_ctor_set(v___x_1160_, 1, v___f_1159_);
lean_inc_ref(v___x_1160_);
v___f_1161_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1161_, 0, v___x_1137_);
lean_closure_set(v___f_1161_, 1, v___x_1160_);
v___f_1162_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1162_, 0, v___x_1137_);
lean_closure_set(v___f_1162_, 1, v___x_1160_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___f_1161_);
lean_ctor_set(v___x_1163_, 1, v___f_1162_);
lean_inc_ref(v___x_1163_);
v___f_1164_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1164_, 0, v___x_1138_);
lean_closure_set(v___f_1164_, 1, v___x_1163_);
v___f_1165_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1165_, 0, v___x_1138_);
lean_closure_set(v___f_1165_, 1, v___x_1163_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___f_1164_);
lean_ctor_set(v___x_1166_, 1, v___f_1165_);
lean_inc_ref(v___x_1166_);
v___f_1167_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1167_, 0, v___x_1137_);
lean_closure_set(v___f_1167_, 1, v___x_1166_);
v___f_1168_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1168_, 0, v___x_1137_);
lean_closure_set(v___f_1168_, 1, v___x_1166_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___f_1167_);
lean_ctor_set(v___x_1169_, 1, v___f_1168_);
lean_inc_ref(v___x_1169_);
v___f_1170_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1170_, 0, v___x_1137_);
lean_closure_set(v___f_1170_, 1, v___x_1169_);
v___f_1171_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1171_, 0, v___x_1137_);
lean_closure_set(v___f_1171_, 1, v___x_1169_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___f_1170_);
lean_ctor_set(v___x_1172_, 1, v___f_1171_);
v_toApplicative_1173_ = lean_ctor_get(v___x_1139_, 0);
v_toFunctor_1174_ = lean_ctor_get(v_toApplicative_1173_, 0);
v_toSeq_1175_ = lean_ctor_get(v_toApplicative_1173_, 2);
v_toSeqLeft_1176_ = lean_ctor_get(v_toApplicative_1173_, 3);
v_toSeqRight_1177_ = lean_ctor_get(v_toApplicative_1173_, 4);
lean_inc_ref_n(v_toFunctor_1174_, 2);
v___f_1178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1178_, 0, v_toFunctor_1174_);
v___f_1179_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1179_, 0, v_toFunctor_1174_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___f_1178_);
lean_ctor_set(v___x_1180_, 1, v___f_1179_);
lean_inc(v_toSeqRight_1177_);
v___f_1181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1181_, 0, v_toSeqRight_1177_);
lean_inc(v_toSeqLeft_1176_);
v___f_1182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1182_, 0, v_toSeqLeft_1176_);
lean_inc(v_toSeq_1175_);
v___f_1183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1183_, 0, v_toSeq_1175_);
v___x_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1180_);
lean_ctor_set(v___x_1184_, 1, v___f_1145_);
lean_ctor_set(v___x_1184_, 2, v___f_1183_);
lean_ctor_set(v___x_1184_, 3, v___f_1182_);
lean_ctor_set(v___x_1184_, 4, v___f_1181_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___f_1146_);
v___x_1186_ = l_StateRefT_x27_instMonad___redArg(v___x_1185_);
v_toApplicative_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1186_, 1);
lean_dec(v_unused_1260_);
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1259_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_toApplicative_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1259_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_toFunctor_1191_; lean_object* v_toSeq_1192_; lean_object* v_toSeqLeft_1193_; lean_object* v_toSeqRight_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1257_; 
v_toFunctor_1191_ = lean_ctor_get(v_toApplicative_1187_, 0);
v_toSeq_1192_ = lean_ctor_get(v_toApplicative_1187_, 2);
v_toSeqLeft_1193_ = lean_ctor_get(v_toApplicative_1187_, 3);
v_toSeqRight_1194_ = lean_ctor_get(v_toApplicative_1187_, 4);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_toApplicative_1187_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v_toApplicative_1187_, 1);
lean_dec(v_unused_1258_);
v___x_1196_ = v_toApplicative_1187_;
v_isShared_1197_ = v_isSharedCheck_1257_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_toSeqRight_1194_);
lean_inc(v_toSeqLeft_1193_);
lean_inc(v_toSeq_1192_);
lean_inc(v_toFunctor_1191_);
lean_dec(v_toApplicative_1187_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1257_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___x_1207_; 
v___f_1198_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1199_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1191_);
v___f_1200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1200_, 0, v_toFunctor_1191_);
v___f_1201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1201_, 0, v_toFunctor_1191_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___f_1200_);
lean_ctor_set(v___x_1202_, 1, v___f_1201_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toSeqRight_1194_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toSeqLeft_1193_);
v___f_1205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1205_, 0, v_toSeq_1192_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 4, v___f_1203_);
lean_ctor_set(v___x_1196_, 3, v___f_1204_);
lean_ctor_set(v___x_1196_, 2, v___f_1205_);
lean_ctor_set(v___x_1196_, 1, v___f_1198_);
lean_ctor_set(v___x_1196_, 0, v___x_1202_);
v___x_1207_ = v___x_1196_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v___f_1198_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v___f_1205_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v___f_1204_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v___f_1203_);
v___x_1207_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___f_1199_);
lean_ctor_set(v___x_1189_, 0, v___x_1207_);
v___x_1209_ = v___x_1189_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___f_1199_);
v___x_1209_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_mvarId_1215_; lean_object* v___x_1216_; lean_object* v___x_5171__overap_1217_; lean_object* v___x_1218_; 
v___x_1210_ = l_StateRefT_x27_instMonad___redArg(v___x_1209_);
v___x_1211_ = l_ReaderT_instMonad___redArg(v___x_1210_);
v___x_1212_ = l_StateRefT_x27_instMonad___redArg(v___x_1211_);
v___x_1213_ = l_ReaderT_instMonad___redArg(v___x_1212_);
v___x_1214_ = l_ReaderT_instMonad___redArg(v___x_1213_);
v_mvarId_1215_ = lean_ctor_get(v_goal_1133_, 1);
lean_inc(v_mvarId_1215_);
v___x_1216_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1216_, 0, lean_box(0));
lean_closure_set(v___x_1216_, 1, v_goal_1133_);
lean_closure_set(v___x_1216_, 2, v_x_1118_);
v___x_5171__overap_1217_ = l_Lean_MVarId_withContext___redArg(v___x_1172_, v___x_1214_, v_mvarId_1215_, v___x_1216_);
lean_inc(v_a_1129_);
lean_inc_ref(v_a_1128_);
lean_inc(v_a_1127_);
lean_inc_ref(v_a_1126_);
lean_inc(v_a_1125_);
lean_inc_ref(v_a_1124_);
lean_inc(v_a_1123_);
lean_inc_ref(v_a_1122_);
lean_inc(v_a_1121_);
v___x_1218_ = lean_apply_10(v___x_5171__overap_1217_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, lean_box(0));
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1246_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1246_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1246_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1226_; 
v_fst_1223_ = lean_ctor_get(v_a_1219_, 0);
lean_inc(v_fst_1223_);
v_snd_1224_ = lean_ctor_get(v_a_1219_, 1);
lean_inc(v_snd_1224_);
lean_dec(v_a_1219_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_snd_1224_);
v___x_1226_ = v___x_1135_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_snd_1224_);
v___x_1226_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v_caches_1228_; lean_object* v_typeAnalysis_1229_; lean_object* v_hypotheses_1230_; uint8_t v_didChange_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1243_; 
v___x_1227_ = lean_st_ref_take(v_a_1120_);
v_caches_1228_ = lean_ctor_get(v___x_1227_, 0);
v_typeAnalysis_1229_ = lean_ctor_get(v___x_1227_, 1);
v_hypotheses_1230_ = lean_ctor_get(v___x_1227_, 3);
v_didChange_1231_ = lean_ctor_get_uint8(v___x_1227_, sizeof(void*)*4);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v___x_1227_, 2);
lean_dec(v_unused_1244_);
v___x_1233_ = v___x_1227_;
v_isShared_1234_ = v_isSharedCheck_1243_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_hypotheses_1230_);
lean_inc(v_typeAnalysis_1229_);
lean_inc(v_caches_1228_);
lean_dec(v___x_1227_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1243_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 2, v___x_1226_);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_caches_1228_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_typeAnalysis_1229_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_hypotheses_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*4, v_didChange_1231_);
v___x_1236_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1237_ = lean_st_ref_put(v_a_1120_, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_fst_1223_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1238_);
v___x_1240_ = v___x_1221_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_del_object(v___x_1135_);
v_a_1247_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1218_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1218_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
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
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v_target_1132_);
lean_dec_ref(v_x_1118_);
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___boxed(lean_object* v_00_u03b1_1264_, lean_object* v_x_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(v_00_u03b1_1264_, v_x_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(lean_object* v_x_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1282_);
lean_inc_ref(v___y_1281_);
lean_inc(v___y_1280_);
v___x_1290_ = lean_apply_10(v_x_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, lean_box(0));
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed(lean_object* v_x_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(v_x_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(lean_object* v_mvarId_1303_, lean_object* v_x_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___f_1315_; lean_object* v___x_1316_; 
lean_inc(v___y_1309_);
lean_inc_ref(v___y_1308_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
v___f_1315_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1315_, 0, v_x_1304_);
lean_closure_set(v___f_1315_, 1, v___y_1305_);
lean_closure_set(v___f_1315_, 2, v___y_1306_);
lean_closure_set(v___f_1315_, 3, v___y_1307_);
lean_closure_set(v___f_1315_, 4, v___y_1308_);
lean_closure_set(v___f_1315_, 5, v___y_1309_);
v___x_1316_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1303_, v___f_1315_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1316_) == 0)
{
return v___x_1316_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___boxed(lean_object* v_mvarId_1325_, lean_object* v_x_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1325_, v_x_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(lean_object* v_00_u03b1_1338_, lean_object* v_mvarId_1339_, lean_object* v_x_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1339_, v_x_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___boxed(lean_object* v_00_u03b1_1352_, lean_object* v_mvarId_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(v_00_u03b1_1352_, v_mvarId_1353_, v_x_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(lean_object* v_goal_1366_, lean_object* v_falseProof_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_st_mk_ref(v_goal_1366_);
v___x_1379_ = l_Lean_Meta_Grind_closeGoal(v_falseProof_1367_, v___x_1378_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1389_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1384_ = lean_st_ref_get(v___x_1378_);
lean_dec(v___x_1378_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_a_1380_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v___x_1378_);
v_a_1390_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1379_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1379_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed(lean_object* v_goal_1398_, lean_object* v_falseProof_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(v_goal_1398_, v_falseProof_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object* v_falseProof_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1423_; lean_object* v_target_1424_; 
v___x_1423_ = lean_st_ref_get(v_a_1412_);
v_target_1424_ = lean_ctor_get(v___x_1423_, 2);
lean_inc_ref(v_target_1424_);
lean_dec(v___x_1423_);
if (lean_obj_tag(v_target_1424_) == 0)
{
lean_object* v_mvar_1425_; lean_object* v___x_1426_; 
v_mvar_1425_ = lean_ctor_get(v_target_1424_, 0);
lean_inc(v_mvar_1425_);
lean_dec_ref_known(v_target_1424_, 1);
v___x_1426_ = l_Lean_MVarId_assignFalseProof(v_mvar_1425_, v_falseProof_1411_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
return v___x_1426_;
}
else
{
lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1478_; 
v_isSharedCheck_1478_ = !lean_is_exclusive(v_target_1424_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_target_1424_, 0);
lean_dec(v_unused_1479_);
v___x_1428_ = v_target_1424_;
v_isShared_1429_ = v_isSharedCheck_1478_;
goto v_resetjp_1427_;
}
else
{
lean_dec(v_target_1424_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1478_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_target_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_st_ref_get(v_a_1412_);
v_target_1432_ = lean_ctor_get(v___x_1431_, 2);
lean_inc_ref(v_target_1432_);
lean_dec(v___x_1431_);
if (lean_obj_tag(v_target_1432_) == 1)
{
lean_object* v_goal_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1474_; 
lean_del_object(v___x_1428_);
v_goal_1433_ = lean_ctor_get(v_target_1432_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_target_1432_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1435_ = v_target_1432_;
v_isShared_1436_ = v_isSharedCheck_1474_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_goal_1433_);
lean_dec(v_target_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1474_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_mvarId_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; 
v_mvarId_1437_ = lean_ctor_get(v_goal_1433_, 1);
lean_inc(v_mvarId_1437_);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1438_, 0, v_goal_1433_);
lean_closure_set(v___f_1438_, 1, v_falseProof_1411_);
v___x_1439_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1437_, v___f_1438_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1465_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1465_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1465_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_snd_1444_; lean_object* v___x_1446_; 
v_snd_1444_ = lean_ctor_get(v_a_1440_, 1);
lean_inc(v_snd_1444_);
lean_dec(v_a_1440_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_snd_1444_);
v___x_1446_ = v___x_1435_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_snd_1444_);
v___x_1446_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v_caches_1448_; lean_object* v_typeAnalysis_1449_; lean_object* v_hypotheses_1450_; uint8_t v_didChange_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1462_; 
v___x_1447_ = lean_st_ref_take(v_a_1412_);
v_caches_1448_ = lean_ctor_get(v___x_1447_, 0);
v_typeAnalysis_1449_ = lean_ctor_get(v___x_1447_, 1);
v_hypotheses_1450_ = lean_ctor_get(v___x_1447_, 3);
v_didChange_1451_ = lean_ctor_get_uint8(v___x_1447_, sizeof(void*)*4);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1447_, 2);
lean_dec(v_unused_1463_);
v___x_1453_ = v___x_1447_;
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_hypotheses_1450_);
lean_inc(v_typeAnalysis_1449_);
lean_inc(v_caches_1448_);
lean_dec(v___x_1447_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 2, v___x_1446_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_caches_1448_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_typeAnalysis_1449_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_hypotheses_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*4, v_didChange_1451_);
v___x_1456_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1457_ = lean_st_ref_put(v_a_1412_, v___x_1456_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1430_);
v___x_1459_ = v___x_1442_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1430_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_del_object(v___x_1435_);
v_a_1466_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1439_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1439_);
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
else
{
lean_object* v___x_1476_; 
lean_dec_ref(v_target_1432_);
lean_dec_ref(v_falseProof_1411_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1430_);
v___x_1476_ = v___x_1428_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1430_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___boxed(lean_object* v_falseProof_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec(v_a_1481_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(lean_object* v_falseProof_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1493_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed(lean_object* v_falseProof_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(v_falseProof_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; uint8_t v_didChange_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_st_ref_get(v_a_1521_);
v_didChange_1524_ = lean_ctor_get_uint8(v___x_1523_, sizeof(void*)*4);
lean_dec(v___x_1523_);
v___x_1525_ = lean_box(v_didChange_1524_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_1527_);
lean_dec(v_a_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1542_; uint8_t v_didChange_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1542_ = lean_st_ref_get(v_a_1531_);
v_didChange_1543_ = lean_ctor_get_uint8(v___x_1542_, sizeof(void*)*4);
lean_dec(v___x_1542_);
v___x_1544_ = lean_box(v_didChange_1543_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v_caches_1562_; lean_object* v_typeAnalysis_1563_; lean_object* v_target_1564_; lean_object* v_hypotheses_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1576_; 
v___x_1561_ = lean_st_ref_take(v_a_1559_);
v_caches_1562_ = lean_ctor_get(v___x_1561_, 0);
v_typeAnalysis_1563_ = lean_ctor_get(v___x_1561_, 1);
v_target_1564_ = lean_ctor_get(v___x_1561_, 2);
v_hypotheses_1565_ = lean_ctor_get(v___x_1561_, 3);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1567_ = v___x_1561_;
v_isShared_1568_ = v_isSharedCheck_1576_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_hypotheses_1565_);
lean_inc(v_target_1564_);
lean_inc(v_typeAnalysis_1563_);
lean_inc(v_caches_1562_);
lean_dec(v___x_1561_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1576_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; lean_object* v___x_1572_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = 0;
if (v_isShared_1568_ == 0)
{
v___x_1572_ = v___x_1567_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_caches_1562_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_typeAnalysis_1563_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_target_1564_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_hypotheses_1565_);
v___x_1572_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_ctor_set_uint8(v___x_1572_, sizeof(void*)*4, v___x_1570_);
v___x_1573_ = lean_st_ref_put(v_a_1559_, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1569_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_1577_);
lean_dec(v_a_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v_caches_1593_; lean_object* v_typeAnalysis_1594_; lean_object* v_target_1595_; lean_object* v_hypotheses_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1607_; 
v___x_1592_ = lean_st_ref_take(v_a_1581_);
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
v___x_1604_ = lean_st_ref_put(v_a_1581_, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1600_);
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
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
lean_dec_ref(v_a_1608_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v_caches_1624_; lean_object* v_typeAnalysis_1625_; lean_object* v_target_1626_; lean_object* v_hypotheses_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1638_; 
v___x_1623_ = lean_st_ref_take(v_a_1621_);
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
v___x_1632_ = 1;
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
v___x_1635_ = lean_st_ref_put(v_a_1621_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1631_);
return v___x_1636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_1639_);
lean_dec(v_a_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v_caches_1655_; lean_object* v_typeAnalysis_1656_; lean_object* v_target_1657_; lean_object* v_hypotheses_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1669_; 
v___x_1654_ = lean_st_ref_take(v_a_1643_);
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
v___x_1666_ = lean_st_ref_put(v_a_1643_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1662_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v_caches_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_st_ref_get(v_a_1683_);
v_caches_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc_ref(v_caches_1686_);
lean_dec(v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_caches_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg___boxed(lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(v_a_1688_);
lean_dec(v_a_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v_caches_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_st_ref_get(v_a_1692_);
v_caches_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc_ref(v_caches_1704_);
lean_dec(v___x_1703_);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_caches_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___boxed(lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(lean_object* v_caches_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1722_; lean_object* v_typeAnalysis_1723_; lean_object* v_target_1724_; lean_object* v_hypotheses_1725_; uint8_t v_didChange_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1736_; 
v___x_1722_ = lean_st_ref_take(v_a_1720_);
v_typeAnalysis_1723_ = lean_ctor_get(v___x_1722_, 1);
v_target_1724_ = lean_ctor_get(v___x_1722_, 2);
v_hypotheses_1725_ = lean_ctor_get(v___x_1722_, 3);
v_didChange_1726_ = lean_ctor_get_uint8(v___x_1722_, sizeof(void*)*4);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1722_, 0);
lean_dec(v_unused_1737_);
v___x_1728_ = v___x_1722_;
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_hypotheses_1725_);
lean_inc(v_target_1724_);
lean_inc(v_typeAnalysis_1723_);
lean_dec(v___x_1722_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_box(0);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v_caches_1719_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_caches_1719_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_typeAnalysis_1723_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_target_1724_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_hypotheses_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*4, v_didChange_1726_);
v___x_1732_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_st_ref_put(v_a_1720_, v___x_1732_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1730_);
return v___x_1734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg___boxed(lean_object* v_caches_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(v_caches_1738_, v_a_1739_);
lean_dec(v_a_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(lean_object* v_caches_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; lean_object* v_typeAnalysis_1756_; lean_object* v_target_1757_; lean_object* v_hypotheses_1758_; uint8_t v_didChange_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1769_; 
v___x_1755_ = lean_st_ref_take(v_a_1744_);
v_typeAnalysis_1756_ = lean_ctor_get(v___x_1755_, 1);
v_target_1757_ = lean_ctor_get(v___x_1755_, 2);
v_hypotheses_1758_ = lean_ctor_get(v___x_1755_, 3);
v_didChange_1759_ = lean_ctor_get_uint8(v___x_1755_, sizeof(void*)*4);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1755_, 0);
lean_dec(v_unused_1770_);
v___x_1761_ = v___x_1755_;
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_hypotheses_1758_);
lean_inc(v_target_1757_);
lean_inc(v_typeAnalysis_1756_);
lean_dec(v___x_1755_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = lean_box(0);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v_caches_1742_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_caches_1742_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_typeAnalysis_1756_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_target_1757_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_hypotheses_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*4, v_didChange_1759_);
v___x_1765_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_st_ref_put(v_a_1744_, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1763_);
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___boxed(lean_object* v_caches_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(v_caches_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1784_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_1789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
lean_ctor_set(v___x_1789_, 2, v___x_1788_);
lean_ctor_set(v___x_1789_, 3, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_mode_1793_; uint8_t v___x_1794_; 
v_mode_1793_ = lean_ctor_get(v_a_1790_, 1);
v___x_1794_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_typeAnalysis_1797_; lean_object* v_target_1798_; lean_object* v_hypotheses_1799_; uint8_t v_didChange_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1810_; 
v___x_1795_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_1796_ = lean_st_ref_take(v_a_1791_);
v_typeAnalysis_1797_ = lean_ctor_get(v___x_1796_, 1);
v_target_1798_ = lean_ctor_get(v___x_1796_, 2);
v_hypotheses_1799_ = lean_ctor_get(v___x_1796_, 3);
v_didChange_1800_ = lean_ctor_get_uint8(v___x_1796_, sizeof(void*)*4);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v___x_1796_, 0);
lean_dec(v_unused_1811_);
v___x_1802_ = v___x_1796_;
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_hypotheses_1799_);
lean_inc(v_target_1798_);
lean_inc(v_typeAnalysis_1797_);
lean_dec(v___x_1796_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = lean_box(0);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1795_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_typeAnalysis_1797_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v_target_1798_);
lean_ctor_set(v_reuseFailAlloc_1809_, 3, v_hypotheses_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1809_, sizeof(void*)*4, v_didChange_1800_);
v___x_1806_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_st_ref_put(v_a_1791_, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1804_);
return v___x_1808_;
}
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___boxed(lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1814_, v_a_1815_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1818_, v_a_1819_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___boxed(lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_1844_){
_start:
{
lean_object* v___x_1846_; lean_object* v_typeAnalysis_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_st_ref_get(v_a_1844_);
v_typeAnalysis_1847_ = lean_ctor_get(v___x_1846_, 1);
lean_inc_ref(v_typeAnalysis_1847_);
lean_dec(v___x_1846_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_typeAnalysis_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1849_);
lean_dec(v_a_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v_typeAnalysis_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_st_ref_get(v_a_1853_);
v_typeAnalysis_1865_ = lean_ctor_get(v___x_1864_, 1);
lean_inc_ref(v_typeAnalysis_1865_);
lean_dec(v___x_1864_);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_typeAnalysis_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_typeAnalysis_1891_; lean_object* v_interestingStructures_1892_; lean_object* v_uninteresting_1893_; uint8_t v___x_1894_; 
v___x_1888_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1889_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1890_ = lean_st_ref_get(v_a_1886_);
v_typeAnalysis_1891_ = lean_ctor_get(v___x_1890_, 1);
lean_inc_ref(v_typeAnalysis_1891_);
lean_dec(v___x_1890_);
v_interestingStructures_1892_ = lean_ctor_get(v_typeAnalysis_1891_, 0);
lean_inc_ref(v_interestingStructures_1892_);
v_uninteresting_1893_ = lean_ctor_get(v_typeAnalysis_1891_, 3);
lean_inc_ref(v_uninteresting_1893_);
lean_dec_ref(v_typeAnalysis_1891_);
lean_inc(v_n_1885_);
v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1888_, v___x_1889_, v_uninteresting_1893_, v_n_1885_);
lean_dec_ref(v_uninteresting_1893_);
if (v___x_1894_ == 0)
{
uint8_t v___x_1895_; 
v___x_1895_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1888_, v___x_1889_, v_interestingStructures_1892_, v_n_1885_);
lean_dec_ref(v_interestingStructures_1892_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_box(v___x_1895_);
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec_ref(v_interestingStructures_1892_);
lean_dec(v_n_1885_);
v___x_1901_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1903_, v_a_1904_);
lean_dec(v_a_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_typeAnalysis_1923_; lean_object* v_interestingStructures_1924_; lean_object* v_uninteresting_1925_; uint8_t v___x_1926_; 
v___x_1920_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1921_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1922_ = lean_st_ref_get(v_a_1909_);
v_typeAnalysis_1923_ = lean_ctor_get(v___x_1922_, 1);
lean_inc_ref(v_typeAnalysis_1923_);
lean_dec(v___x_1922_);
v_interestingStructures_1924_ = lean_ctor_get(v_typeAnalysis_1923_, 0);
lean_inc_ref(v_interestingStructures_1924_);
v_uninteresting_1925_ = lean_ctor_get(v_typeAnalysis_1923_, 3);
lean_inc_ref(v_uninteresting_1925_);
lean_dec_ref(v_typeAnalysis_1923_);
lean_inc(v_n_1907_);
v___x_1926_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1920_, v___x_1921_, v_uninteresting_1925_, v_n_1907_);
lean_dec_ref(v_uninteresting_1925_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; 
v___x_1927_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1920_, v___x_1921_, v_interestingStructures_1924_, v_n_1907_);
lean_dec_ref(v_interestingStructures_1924_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_box(v___x_1927_);
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_dec_ref(v_interestingStructures_1924_);
lean_dec(v_n_1907_);
v___x_1933_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1952_; lean_object* v_caches_1953_; lean_object* v_typeAnalysis_1954_; lean_object* v_target_1955_; lean_object* v_hypotheses_1956_; uint8_t v_didChange_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1968_; 
v___x_1952_ = lean_st_ref_take(v_a_1950_);
v_caches_1953_ = lean_ctor_get(v___x_1952_, 0);
v_typeAnalysis_1954_ = lean_ctor_get(v___x_1952_, 1);
v_target_1955_ = lean_ctor_get(v___x_1952_, 2);
v_hypotheses_1956_ = lean_ctor_get(v___x_1952_, 3);
v_didChange_1957_ = lean_ctor_get_uint8(v___x_1952_, sizeof(void*)*4);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1959_ = v___x_1952_;
v_isShared_1960_ = v_isSharedCheck_1968_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_hypotheses_1956_);
lean_inc(v_target_1955_);
lean_inc(v_typeAnalysis_1954_);
lean_inc(v_caches_1953_);
lean_dec(v___x_1952_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1968_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_apply_1(v_f_1949_, v_typeAnalysis_1954_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v___x_1962_);
v___x_1964_ = v___x_1959_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_caches_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_target_1955_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_hypotheses_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1967_, sizeof(void*)*4, v_didChange_1957_);
v___x_1964_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_st_ref_put(v_a_1950_, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1961_);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_1969_, v_a_1970_);
lean_dec(v_a_1970_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; lean_object* v_caches_1987_; lean_object* v_typeAnalysis_1988_; lean_object* v_target_1989_; lean_object* v_hypotheses_1990_; uint8_t v_didChange_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2002_; 
v___x_1986_ = lean_st_ref_take(v_a_1975_);
v_caches_1987_ = lean_ctor_get(v___x_1986_, 0);
v_typeAnalysis_1988_ = lean_ctor_get(v___x_1986_, 1);
v_target_1989_ = lean_ctor_get(v___x_1986_, 2);
v_hypotheses_1990_ = lean_ctor_get(v___x_1986_, 3);
v_didChange_1991_ = lean_ctor_get_uint8(v___x_1986_, sizeof(void*)*4);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1993_ = v___x_1986_;
v_isShared_1994_ = v_isSharedCheck_2002_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_hypotheses_1990_);
lean_inc(v_target_1989_);
lean_inc(v_typeAnalysis_1988_);
lean_inc(v_caches_1987_);
lean_dec(v___x_1986_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2002_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1995_ = lean_box(0);
v___x_1996_ = lean_apply_1(v_f_1973_, v_typeAnalysis_1988_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v___x_1996_);
v___x_1998_ = v___x_1993_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_caches_1987_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_target_1989_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v_hypotheses_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2001_, sizeof(void*)*4, v_didChange_1991_);
v___x_1998_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_st_ref_put(v_a_1975_, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1995_);
return v___x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v_typeAnalysis_2023_; lean_object* v_caches_2024_; lean_object* v_target_2025_; lean_object* v_hypotheses_2026_; uint8_t v_didChange_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2049_; 
v___x_2020_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2021_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2022_ = lean_st_ref_take(v_a_2018_);
v_typeAnalysis_2023_ = lean_ctor_get(v___x_2022_, 1);
v_caches_2024_ = lean_ctor_get(v___x_2022_, 0);
v_target_2025_ = lean_ctor_get(v___x_2022_, 2);
v_hypotheses_2026_ = lean_ctor_get(v___x_2022_, 3);
v_didChange_2027_ = lean_ctor_get_uint8(v___x_2022_, sizeof(void*)*4);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2029_ = v___x_2022_;
v_isShared_2030_ = v_isSharedCheck_2049_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_hypotheses_2026_);
lean_inc(v_target_2025_);
lean_inc(v_typeAnalysis_2023_);
lean_inc(v_caches_2024_);
lean_dec(v___x_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2049_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_interestingStructures_2031_; lean_object* v_interestingEnums_2032_; lean_object* v_interestingMatchers_2033_; lean_object* v_uninteresting_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2048_; 
v_interestingStructures_2031_ = lean_ctor_get(v_typeAnalysis_2023_, 0);
v_interestingEnums_2032_ = lean_ctor_get(v_typeAnalysis_2023_, 1);
v_interestingMatchers_2033_ = lean_ctor_get(v_typeAnalysis_2023_, 2);
v_uninteresting_2034_ = lean_ctor_get(v_typeAnalysis_2023_, 3);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_typeAnalysis_2023_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2036_ = v_typeAnalysis_2023_;
v_isShared_2037_ = v_isSharedCheck_2048_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_uninteresting_2034_);
lean_inc(v_interestingMatchers_2033_);
lean_inc(v_interestingEnums_2032_);
lean_inc(v_interestingStructures_2031_);
lean_dec(v_typeAnalysis_2023_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2048_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = lean_box(0);
v___x_2039_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2020_, v___x_2021_, v_interestingStructures_2031_, v_n_2017_, v___x_2038_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2039_);
v___x_2041_ = v___x_2036_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_interestingEnums_2032_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_interestingMatchers_2033_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_uninteresting_2034_);
v___x_2041_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v___x_2041_);
v___x_2043_ = v___x_2029_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_caches_2024_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_target_2025_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_hypotheses_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2046_, sizeof(void*)*4, v_didChange_2027_);
v___x_2043_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_st_ref_put(v_a_2018_, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2038_);
return v___x_2045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_2050_, v_a_2051_);
lean_dec(v_a_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_typeAnalysis_2070_; lean_object* v_caches_2071_; lean_object* v_target_2072_; lean_object* v_hypotheses_2073_; uint8_t v_didChange_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2096_; 
v___x_2067_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2068_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2069_ = lean_st_ref_take(v_a_2056_);
v_typeAnalysis_2070_ = lean_ctor_get(v___x_2069_, 1);
v_caches_2071_ = lean_ctor_get(v___x_2069_, 0);
v_target_2072_ = lean_ctor_get(v___x_2069_, 2);
v_hypotheses_2073_ = lean_ctor_get(v___x_2069_, 3);
v_didChange_2074_ = lean_ctor_get_uint8(v___x_2069_, sizeof(void*)*4);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2076_ = v___x_2069_;
v_isShared_2077_ = v_isSharedCheck_2096_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_hypotheses_2073_);
lean_inc(v_target_2072_);
lean_inc(v_typeAnalysis_2070_);
lean_inc(v_caches_2071_);
lean_dec(v___x_2069_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2096_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_interestingStructures_2078_; lean_object* v_interestingEnums_2079_; lean_object* v_interestingMatchers_2080_; lean_object* v_uninteresting_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2095_; 
v_interestingStructures_2078_ = lean_ctor_get(v_typeAnalysis_2070_, 0);
v_interestingEnums_2079_ = lean_ctor_get(v_typeAnalysis_2070_, 1);
v_interestingMatchers_2080_ = lean_ctor_get(v_typeAnalysis_2070_, 2);
v_uninteresting_2081_ = lean_ctor_get(v_typeAnalysis_2070_, 3);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_typeAnalysis_2070_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2083_ = v_typeAnalysis_2070_;
v_isShared_2084_ = v_isSharedCheck_2095_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_uninteresting_2081_);
lean_inc(v_interestingMatchers_2080_);
lean_inc(v_interestingEnums_2079_);
lean_inc(v_interestingStructures_2078_);
lean_dec(v_typeAnalysis_2070_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2095_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2085_ = lean_box(0);
v___x_2086_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2067_, v___x_2068_, v_interestingStructures_2078_, v_n_2054_, v___x_2085_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2086_);
v___x_2088_ = v___x_2083_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_interestingEnums_2079_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_interestingMatchers_2080_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v_uninteresting_2081_);
v___x_2088_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2088_);
v___x_2090_ = v___x_2076_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_caches_2071_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_target_2072_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_hypotheses_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2093_, sizeof(void*)*4, v_didChange_2074_);
v___x_2090_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_st_ref_put(v_a_2056_, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2085_);
return v___x_2092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_typeAnalysis_2117_; lean_object* v_caches_2118_; lean_object* v_target_2119_; lean_object* v_hypotheses_2120_; uint8_t v_didChange_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2143_; 
v___x_2114_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2115_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2116_ = lean_st_ref_take(v_a_2112_);
v_typeAnalysis_2117_ = lean_ctor_get(v___x_2116_, 1);
v_caches_2118_ = lean_ctor_get(v___x_2116_, 0);
v_target_2119_ = lean_ctor_get(v___x_2116_, 2);
v_hypotheses_2120_ = lean_ctor_get(v___x_2116_, 3);
v_didChange_2121_ = lean_ctor_get_uint8(v___x_2116_, sizeof(void*)*4);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2123_ = v___x_2116_;
v_isShared_2124_ = v_isSharedCheck_2143_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_hypotheses_2120_);
lean_inc(v_target_2119_);
lean_inc(v_typeAnalysis_2117_);
lean_inc(v_caches_2118_);
lean_dec(v___x_2116_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2143_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_interestingStructures_2125_; lean_object* v_interestingEnums_2126_; lean_object* v_interestingMatchers_2127_; lean_object* v_uninteresting_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2142_; 
v_interestingStructures_2125_ = lean_ctor_get(v_typeAnalysis_2117_, 0);
v_interestingEnums_2126_ = lean_ctor_get(v_typeAnalysis_2117_, 1);
v_interestingMatchers_2127_ = lean_ctor_get(v_typeAnalysis_2117_, 2);
v_uninteresting_2128_ = lean_ctor_get(v_typeAnalysis_2117_, 3);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_typeAnalysis_2117_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2130_ = v_typeAnalysis_2117_;
v_isShared_2131_ = v_isSharedCheck_2142_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_uninteresting_2128_);
lean_inc(v_interestingMatchers_2127_);
lean_inc(v_interestingEnums_2126_);
lean_inc(v_interestingStructures_2125_);
lean_dec(v_typeAnalysis_2117_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2142_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2132_ = lean_box(0);
v___x_2133_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2114_, v___x_2115_, v_interestingEnums_2126_, v_n_2111_, v___x_2132_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v___x_2133_);
v___x_2135_ = v___x_2130_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_interestingStructures_2125_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_interestingMatchers_2127_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_uninteresting_2128_);
v___x_2135_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 1, v___x_2135_);
v___x_2137_ = v___x_2123_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_caches_2118_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_target_2119_);
lean_ctor_set(v_reuseFailAlloc_2140_, 3, v_hypotheses_2120_);
lean_ctor_set_uint8(v_reuseFailAlloc_2140_, sizeof(void*)*4, v_didChange_2121_);
v___x_2137_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_st_ref_put(v_a_2112_, v___x_2137_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2132_);
return v___x_2139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_2144_, v_a_2145_);
lean_dec(v_a_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_typeAnalysis_2164_; lean_object* v_caches_2165_; lean_object* v_target_2166_; lean_object* v_hypotheses_2167_; uint8_t v_didChange_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2190_; 
v___x_2161_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2162_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2163_ = lean_st_ref_take(v_a_2150_);
v_typeAnalysis_2164_ = lean_ctor_get(v___x_2163_, 1);
v_caches_2165_ = lean_ctor_get(v___x_2163_, 0);
v_target_2166_ = lean_ctor_get(v___x_2163_, 2);
v_hypotheses_2167_ = lean_ctor_get(v___x_2163_, 3);
v_didChange_2168_ = lean_ctor_get_uint8(v___x_2163_, sizeof(void*)*4);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2170_ = v___x_2163_;
v_isShared_2171_ = v_isSharedCheck_2190_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_hypotheses_2167_);
lean_inc(v_target_2166_);
lean_inc(v_typeAnalysis_2164_);
lean_inc(v_caches_2165_);
lean_dec(v___x_2163_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2190_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v_interestingStructures_2172_; lean_object* v_interestingEnums_2173_; lean_object* v_interestingMatchers_2174_; lean_object* v_uninteresting_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2189_; 
v_interestingStructures_2172_ = lean_ctor_get(v_typeAnalysis_2164_, 0);
v_interestingEnums_2173_ = lean_ctor_get(v_typeAnalysis_2164_, 1);
v_interestingMatchers_2174_ = lean_ctor_get(v_typeAnalysis_2164_, 2);
v_uninteresting_2175_ = lean_ctor_get(v_typeAnalysis_2164_, 3);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_typeAnalysis_2164_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2177_ = v_typeAnalysis_2164_;
v_isShared_2178_ = v_isSharedCheck_2189_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_uninteresting_2175_);
lean_inc(v_interestingMatchers_2174_);
lean_inc(v_interestingEnums_2173_);
lean_inc(v_interestingStructures_2172_);
lean_dec(v_typeAnalysis_2164_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2189_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2161_, v___x_2162_, v_interestingEnums_2173_, v_n_2148_, v___x_2179_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v___x_2180_);
v___x_2182_ = v___x_2177_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_interestingStructures_2172_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_interestingMatchers_2174_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_uninteresting_2175_);
v___x_2182_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v___x_2182_);
v___x_2184_ = v___x_2170_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_caches_2165_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_target_2166_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_hypotheses_2167_);
lean_ctor_set_uint8(v_reuseFailAlloc_2187_, sizeof(void*)*4, v_didChange_2168_);
v___x_2184_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_st_ref_put(v_a_2150_, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2179_);
return v___x_2186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_2205_, lean_object* v_k_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_typeAnalysis_2212_; lean_object* v_caches_2213_; lean_object* v_target_2214_; lean_object* v_hypotheses_2215_; uint8_t v_didChange_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2238_; 
v___x_2209_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2210_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2211_ = lean_st_ref_take(v_a_2207_);
v_typeAnalysis_2212_ = lean_ctor_get(v___x_2211_, 1);
v_caches_2213_ = lean_ctor_get(v___x_2211_, 0);
v_target_2214_ = lean_ctor_get(v___x_2211_, 2);
v_hypotheses_2215_ = lean_ctor_get(v___x_2211_, 3);
v_didChange_2216_ = lean_ctor_get_uint8(v___x_2211_, sizeof(void*)*4);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2218_ = v___x_2211_;
v_isShared_2219_ = v_isSharedCheck_2238_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_hypotheses_2215_);
lean_inc(v_target_2214_);
lean_inc(v_typeAnalysis_2212_);
lean_inc(v_caches_2213_);
lean_dec(v___x_2211_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2238_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_interestingStructures_2220_; lean_object* v_interestingEnums_2221_; lean_object* v_interestingMatchers_2222_; lean_object* v_uninteresting_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2237_; 
v_interestingStructures_2220_ = lean_ctor_get(v_typeAnalysis_2212_, 0);
v_interestingEnums_2221_ = lean_ctor_get(v_typeAnalysis_2212_, 1);
v_interestingMatchers_2222_ = lean_ctor_get(v_typeAnalysis_2212_, 2);
v_uninteresting_2223_ = lean_ctor_get(v_typeAnalysis_2212_, 3);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_typeAnalysis_2212_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2225_ = v_typeAnalysis_2212_;
v_isShared_2226_ = v_isSharedCheck_2237_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_uninteresting_2223_);
lean_inc(v_interestingMatchers_2222_);
lean_inc(v_interestingEnums_2221_);
lean_inc(v_interestingStructures_2220_);
lean_dec(v_typeAnalysis_2212_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2237_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2227_ = lean_box(0);
v___x_2228_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2209_, v___x_2210_, v_interestingMatchers_2222_, v_n_2205_, v_k_2206_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 2, v___x_2228_);
v___x_2230_ = v___x_2225_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_interestingStructures_2220_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_interestingEnums_2221_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_uninteresting_2223_);
v___x_2230_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2232_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2230_);
v___x_2232_ = v___x_2218_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_caches_2213_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_target_2214_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_hypotheses_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2235_, sizeof(void*)*4, v_didChange_2216_);
v___x_2232_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_st_ref_put(v_a_2207_, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2227_);
return v___x_2234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_2239_, lean_object* v_k_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_2239_, v_k_2240_, v_a_2241_);
lean_dec(v_a_2241_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_2244_, lean_object* v_k_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_typeAnalysis_2261_; lean_object* v_caches_2262_; lean_object* v_target_2263_; lean_object* v_hypotheses_2264_; uint8_t v_didChange_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2287_; 
v___x_2258_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2259_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2260_ = lean_st_ref_take(v_a_2247_);
v_typeAnalysis_2261_ = lean_ctor_get(v___x_2260_, 1);
v_caches_2262_ = lean_ctor_get(v___x_2260_, 0);
v_target_2263_ = lean_ctor_get(v___x_2260_, 2);
v_hypotheses_2264_ = lean_ctor_get(v___x_2260_, 3);
v_didChange_2265_ = lean_ctor_get_uint8(v___x_2260_, sizeof(void*)*4);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2267_ = v___x_2260_;
v_isShared_2268_ = v_isSharedCheck_2287_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_hypotheses_2264_);
lean_inc(v_target_2263_);
lean_inc(v_typeAnalysis_2261_);
lean_inc(v_caches_2262_);
lean_dec(v___x_2260_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2287_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_interestingStructures_2269_; lean_object* v_interestingEnums_2270_; lean_object* v_interestingMatchers_2271_; lean_object* v_uninteresting_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2286_; 
v_interestingStructures_2269_ = lean_ctor_get(v_typeAnalysis_2261_, 0);
v_interestingEnums_2270_ = lean_ctor_get(v_typeAnalysis_2261_, 1);
v_interestingMatchers_2271_ = lean_ctor_get(v_typeAnalysis_2261_, 2);
v_uninteresting_2272_ = lean_ctor_get(v_typeAnalysis_2261_, 3);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_typeAnalysis_2261_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2274_ = v_typeAnalysis_2261_;
v_isShared_2275_ = v_isSharedCheck_2286_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_uninteresting_2272_);
lean_inc(v_interestingMatchers_2271_);
lean_inc(v_interestingEnums_2270_);
lean_inc(v_interestingStructures_2269_);
lean_dec(v_typeAnalysis_2261_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2286_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2276_ = lean_box(0);
v___x_2277_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2258_, v___x_2259_, v_interestingMatchers_2271_, v_n_2244_, v_k_2245_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 2, v___x_2277_);
v___x_2279_ = v___x_2274_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_interestingStructures_2269_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_interestingEnums_2270_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_uninteresting_2272_);
v___x_2279_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2279_);
v___x_2281_ = v___x_2267_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_caches_2262_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_target_2263_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_hypotheses_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2284_, sizeof(void*)*4, v_didChange_2265_);
v___x_2281_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_st_ref_put(v_a_2247_, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2276_);
return v___x_2283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_2288_, lean_object* v_k_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_2288_, v_k_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_typeAnalysis_2309_; lean_object* v_caches_2310_; lean_object* v_target_2311_; lean_object* v_hypotheses_2312_; uint8_t v_didChange_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2335_; 
v___x_2306_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2307_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2308_ = lean_st_ref_take(v_a_2304_);
v_typeAnalysis_2309_ = lean_ctor_get(v___x_2308_, 1);
v_caches_2310_ = lean_ctor_get(v___x_2308_, 0);
v_target_2311_ = lean_ctor_get(v___x_2308_, 2);
v_hypotheses_2312_ = lean_ctor_get(v___x_2308_, 3);
v_didChange_2313_ = lean_ctor_get_uint8(v___x_2308_, sizeof(void*)*4);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2315_ = v___x_2308_;
v_isShared_2316_ = v_isSharedCheck_2335_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_hypotheses_2312_);
lean_inc(v_target_2311_);
lean_inc(v_typeAnalysis_2309_);
lean_inc(v_caches_2310_);
lean_dec(v___x_2308_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2335_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v_interestingStructures_2317_; lean_object* v_interestingEnums_2318_; lean_object* v_interestingMatchers_2319_; lean_object* v_uninteresting_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2334_; 
v_interestingStructures_2317_ = lean_ctor_get(v_typeAnalysis_2309_, 0);
v_interestingEnums_2318_ = lean_ctor_get(v_typeAnalysis_2309_, 1);
v_interestingMatchers_2319_ = lean_ctor_get(v_typeAnalysis_2309_, 2);
v_uninteresting_2320_ = lean_ctor_get(v_typeAnalysis_2309_, 3);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_typeAnalysis_2309_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2322_ = v_typeAnalysis_2309_;
v_isShared_2323_ = v_isSharedCheck_2334_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_uninteresting_2320_);
lean_inc(v_interestingMatchers_2319_);
lean_inc(v_interestingEnums_2318_);
lean_inc(v_interestingStructures_2317_);
lean_dec(v_typeAnalysis_2309_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2334_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2306_, v___x_2307_, v_uninteresting_2320_, v_n_2303_, v___x_2324_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 3, v___x_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_interestingStructures_2317_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_interestingEnums_2318_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_interestingMatchers_2319_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v___x_2327_);
v___x_2329_ = v___x_2315_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_caches_2310_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_target_2311_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_hypotheses_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*4, v_didChange_2313_);
v___x_2329_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_st_ref_put(v_a_2304_, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2324_);
return v___x_2331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_2336_, v_a_2337_);
lean_dec(v_a_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v_typeAnalysis_2356_; lean_object* v_caches_2357_; lean_object* v_target_2358_; lean_object* v_hypotheses_2359_; uint8_t v_didChange_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2382_; 
v___x_2353_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2354_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2355_ = lean_st_ref_take(v_a_2342_);
v_typeAnalysis_2356_ = lean_ctor_get(v___x_2355_, 1);
v_caches_2357_ = lean_ctor_get(v___x_2355_, 0);
v_target_2358_ = lean_ctor_get(v___x_2355_, 2);
v_hypotheses_2359_ = lean_ctor_get(v___x_2355_, 3);
v_didChange_2360_ = lean_ctor_get_uint8(v___x_2355_, sizeof(void*)*4);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2362_ = v___x_2355_;
v_isShared_2363_ = v_isSharedCheck_2382_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_hypotheses_2359_);
lean_inc(v_target_2358_);
lean_inc(v_typeAnalysis_2356_);
lean_inc(v_caches_2357_);
lean_dec(v___x_2355_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2382_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_interestingStructures_2364_; lean_object* v_interestingEnums_2365_; lean_object* v_interestingMatchers_2366_; lean_object* v_uninteresting_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2381_; 
v_interestingStructures_2364_ = lean_ctor_get(v_typeAnalysis_2356_, 0);
v_interestingEnums_2365_ = lean_ctor_get(v_typeAnalysis_2356_, 1);
v_interestingMatchers_2366_ = lean_ctor_get(v_typeAnalysis_2356_, 2);
v_uninteresting_2367_ = lean_ctor_get(v_typeAnalysis_2356_, 3);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_typeAnalysis_2356_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2369_ = v_typeAnalysis_2356_;
v_isShared_2370_ = v_isSharedCheck_2381_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_uninteresting_2367_);
lean_inc(v_interestingMatchers_2366_);
lean_inc(v_interestingEnums_2365_);
lean_inc(v_interestingStructures_2364_);
lean_dec(v_typeAnalysis_2356_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2381_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2353_, v___x_2354_, v_uninteresting_2367_, v_n_2340_, v___x_2371_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 3, v___x_2372_);
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_interestingStructures_2364_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_interestingEnums_2365_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_interestingMatchers_2366_);
lean_ctor_set(v_reuseFailAlloc_2380_, 3, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v___x_2374_);
v___x_2376_ = v___x_2362_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_caches_2357_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_target_2358_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v_hypotheses_2359_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*4, v_didChange_2360_);
v___x_2376_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_st_ref_put(v_a_2342_, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2371_);
return v___x_2378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2396_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = lean_box(0);
v___x_2398_ = lean_unsigned_to_nat(16u);
v___x_2399_ = lean_mk_array(v___x_2398_, v___x_2397_);
return v___x_2399_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v___x_2400_);
return v___x_2402_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_2404_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
lean_ctor_set(v___x_2404_, 2, v___x_2403_);
lean_ctor_set(v___x_2404_, 3, v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_ctx_2407_, lean_object* v_target_2408_, lean_object* v_x_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2420_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2421_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2422_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2423_ = 0;
v___x_2424_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2424_, 0, v___x_2420_);
lean_ctor_set(v___x_2424_, 1, v___x_2421_);
lean_ctor_set(v___x_2424_, 2, v_target_2408_);
lean_ctor_set(v___x_2424_, 3, v___x_2422_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*4, v___x_2423_);
v___x_2425_ = lean_st_mk_ref(v___x_2424_);
lean_inc(v_a_2418_);
lean_inc_ref(v_a_2417_);
lean_inc(v_a_2416_);
lean_inc_ref(v_a_2415_);
lean_inc(v_a_2414_);
lean_inc_ref(v_a_2413_);
lean_inc(v_a_2412_);
lean_inc_ref(v_a_2411_);
lean_inc(v_a_2410_);
lean_inc(v___x_2425_);
v___x_2426_ = lean_apply_12(v_x_2409_, v_ctx_2407_, v___x_2425_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, lean_box(0));
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2436_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2436_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2436_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2431_ = lean_st_ref_get(v___x_2425_);
lean_dec(v___x_2425_);
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v_a_2427_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2432_);
v___x_2434_ = v___x_2429_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v___x_2425_);
v_a_2437_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2426_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2426_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_ctx_2445_, lean_object* v_target_2446_, lean_object* v_x_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_ctx_2445_, v_target_2446_, v_x_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_a_2448_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_2459_, lean_object* v_ctx_2460_, lean_object* v_target_2461_, lean_object* v_x_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2473_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2474_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2475_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2476_ = 0;
v___x_2477_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2477_, 0, v___x_2473_);
lean_ctor_set(v___x_2477_, 1, v___x_2474_);
lean_ctor_set(v___x_2477_, 2, v_target_2461_);
lean_ctor_set(v___x_2477_, 3, v___x_2475_);
lean_ctor_set_uint8(v___x_2477_, sizeof(void*)*4, v___x_2476_);
v___x_2478_ = lean_st_mk_ref(v___x_2477_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
lean_inc(v_a_2467_);
lean_inc_ref(v_a_2466_);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc(v___x_2478_);
v___x_2479_ = lean_apply_12(v_x_2462_, v_ctx_2460_, v___x_2478_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, lean_box(0));
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2489_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2489_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2489_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2484_ = lean_st_ref_get(v___x_2478_);
lean_dec(v___x_2478_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v_a_2480_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2485_);
v___x_2487_ = v___x_2482_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v___x_2478_);
v_a_2490_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2479_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2479_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_ctx_2499_, lean_object* v_target_2500_, lean_object* v_x_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_2498_, v_ctx_2499_, v_target_2500_, v_x_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_ctx_2513_, lean_object* v_target_2514_, lean_object* v_x_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2526_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2527_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2528_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2529_ = 0;
v___x_2530_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2530_, 0, v___x_2526_);
lean_ctor_set(v___x_2530_, 1, v___x_2527_);
lean_ctor_set(v___x_2530_, 2, v_target_2514_);
lean_ctor_set(v___x_2530_, 3, v___x_2528_);
lean_ctor_set_uint8(v___x_2530_, sizeof(void*)*4, v___x_2529_);
v___x_2531_ = lean_st_mk_ref(v___x_2530_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
lean_inc(v_a_2518_);
lean_inc_ref(v_a_2517_);
lean_inc(v_a_2516_);
lean_inc(v___x_2531_);
v___x_2532_ = lean_apply_12(v_x_2515_, v_ctx_2513_, v___x_2531_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, lean_box(0));
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2541_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2537_ = lean_st_ref_get(v___x_2531_);
lean_dec(v___x_2531_);
lean_dec(v___x_2537_);
if (v_isShared_2536_ == 0)
{
v___x_2539_ = v___x_2535_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2533_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_dec(v___x_2531_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_ctx_2542_, lean_object* v_target_2543_, lean_object* v_x_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_ctx_2542_, v_target_2543_, v_x_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_2556_, lean_object* v_ctx_2557_, lean_object* v_target_2558_, lean_object* v_x_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2570_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2571_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2572_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2573_ = 0;
v___x_2574_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2574_, 0, v___x_2570_);
lean_ctor_set(v___x_2574_, 1, v___x_2571_);
lean_ctor_set(v___x_2574_, 2, v_target_2558_);
lean_ctor_set(v___x_2574_, 3, v___x_2572_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*4, v___x_2573_);
v___x_2575_ = lean_st_mk_ref(v___x_2574_);
lean_inc(v_a_2568_);
lean_inc_ref(v_a_2567_);
lean_inc(v_a_2566_);
lean_inc_ref(v_a_2565_);
lean_inc(v_a_2564_);
lean_inc_ref(v_a_2563_);
lean_inc(v_a_2562_);
lean_inc_ref(v_a_2561_);
lean_inc(v_a_2560_);
lean_inc(v___x_2575_);
v___x_2576_ = lean_apply_12(v_x_2559_, v_ctx_2557_, v___x_2575_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, lean_box(0));
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2585_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_st_ref_get(v___x_2575_);
lean_dec(v___x_2575_);
lean_dec(v___x_2581_);
if (v_isShared_2580_ == 0)
{
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2577_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_dec(v___x_2575_);
return v___x_2576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_2586_, lean_object* v_ctx_2587_, lean_object* v_target_2588_, lean_object* v_x_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_2586_, v_ctx_2587_, v_target_2588_, v_x_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
return v_res_2600_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2604_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2605_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2604_, v___x_2603_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; 
v___x_2606_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2);
v___f_2607_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2608_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2607_, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3);
v___x_2610_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2611_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2610_, v___x_2609_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4);
v___f_2613_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2614_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2613_, v___x_2612_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5);
v___x_2616_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2617_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2616_, v___x_2615_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6);
v___f_2619_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2620_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7);
v___f_2622_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2623_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2622_, v___x_2621_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___x_2625_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2626_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2625_, v___x_2624_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___f_2628_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2629_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2628_, v___x_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2632_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2633_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2634_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2635_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2634_, v___x_2633_, v___x_2632_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___f_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; 
v___x_2636_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___f_2637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2638_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2639_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2638_, v___f_2637_, v___x_2636_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14);
v___x_2641_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2642_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2643_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2642_, v___x_2641_, v___x_2640_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; 
v___x_2644_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15);
v___f_2645_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2646_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2647_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2646_, v___f_2645_, v___x_2644_);
return v___x_2647_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16);
v___x_2649_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2650_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2651_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2650_, v___x_2649_, v___x_2648_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___f_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; 
v___x_2652_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___f_2653_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2654_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2655_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2654_, v___f_2653_, v___x_2652_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___f_2658_; lean_object* v___x_2659_; 
v___x_2656_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18);
v___f_2657_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2658_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2659_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2658_, v___f_2657_, v___x_2656_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2660_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19);
v___x_2661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2662_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2663_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2662_, v___x_2661_, v___x_2660_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___f_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; 
v___x_2664_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___f_2665_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2666_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2667_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2666_, v___f_2665_, v___x_2664_);
return v___x_2667_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v_cls_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_cls_2678_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2679_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_2680_ = l_Lean_Name_append(v___x_2679_, v_cls_2678_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___f_2683_; 
v___x_2681_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2682_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2683_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2683_, 0, v___x_2682_);
lean_closure_set(v___f_2683_, 1, v___x_2681_);
return v___f_2683_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___f_2684_; lean_object* v___f_2685_; lean_object* v___f_2686_; 
v___f_2684_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2685_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___f_2686_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2686_, 0, v___f_2685_);
lean_closure_set(v___f_2686_, 1, v___f_2684_);
return v___f_2686_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___f_2688_; lean_object* v___f_2689_; 
v___x_2687_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2688_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_2689_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2689_, 0, v___f_2688_);
lean_closure_set(v___f_2689_, 1, v___x_2687_);
return v___f_2689_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___f_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; 
v___f_2690_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2691_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_2692_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2692_, 0, v___f_2691_);
lean_closure_set(v___f_2692_, 1, v___f_2690_);
return v___f_2692_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33(void){
_start:
{
lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; 
v___f_2693_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2694_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2695_, 0, v___f_2694_);
lean_closure_set(v___f_2695_, 1, v___f_2693_);
return v___f_2695_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___f_2697_; lean_object* v___f_2698_; 
v___x_2696_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2697_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33);
v___f_2698_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2698_, 0, v___f_2697_);
lean_closure_set(v___f_2698_, 1, v___x_2696_);
return v___f_2698_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35(void){
_start:
{
lean_object* v___f_2699_; lean_object* v___f_2700_; lean_object* v___f_2701_; 
v___f_2699_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2700_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2701_, 0, v___f_2700_);
lean_closure_set(v___f_2701_, 1, v___f_2699_);
return v___f_2701_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36));
v___x_2704_ = l_Lean_stringToMessageData(v___x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v___y_2719_; lean_object* v___x_2737_; lean_object* v_toApplicative_2738_; lean_object* v_toFunctor_2739_; lean_object* v_toSeq_2740_; lean_object* v_toSeqLeft_2741_; lean_object* v_toSeqRight_2742_; lean_object* v___f_2743_; lean_object* v___f_2744_; lean_object* v___f_2745_; lean_object* v___f_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v___f_2749_; lean_object* v___f_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v_toApplicative_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2805_; 
v___x_2737_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2738_ = lean_ctor_get(v___x_2737_, 0);
v_toFunctor_2739_ = lean_ctor_get(v_toApplicative_2738_, 0);
v_toSeq_2740_ = lean_ctor_get(v_toApplicative_2738_, 2);
v_toSeqLeft_2741_ = lean_ctor_get(v_toApplicative_2738_, 3);
v_toSeqRight_2742_ = lean_ctor_get(v_toApplicative_2738_, 4);
v___f_2743_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2744_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2739_, 2);
v___f_2745_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2745_, 0, v_toFunctor_2739_);
v___f_2746_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2746_, 0, v_toFunctor_2739_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___f_2745_);
lean_ctor_set(v___x_2747_, 1, v___f_2746_);
lean_inc(v_toSeqRight_2742_);
v___f_2748_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2748_, 0, v_toSeqRight_2742_);
lean_inc(v_toSeqLeft_2741_);
v___f_2749_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2749_, 0, v_toSeqLeft_2741_);
lean_inc(v_toSeq_2740_);
v___f_2750_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2750_, 0, v_toSeq_2740_);
v___x_2751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2747_);
lean_ctor_set(v___x_2751_, 1, v___f_2743_);
lean_ctor_set(v___x_2751_, 2, v___f_2750_);
lean_ctor_set(v___x_2751_, 3, v___f_2749_);
lean_ctor_set(v___x_2751_, 4, v___f_2748_);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v___f_2744_);
v___x_2753_ = l_StateRefT_x27_instMonad___redArg(v___x_2752_);
v_toApplicative_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v___x_2753_, 1);
lean_dec(v_unused_2806_);
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2805_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_toApplicative_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2805_;
goto v_resetjp_2755_;
}
v___jp_2718_:
{
lean_object* v___x_2720_; lean_object* v_caches_2721_; lean_object* v_typeAnalysis_2722_; lean_object* v_target_2723_; lean_object* v_hypotheses_2724_; uint8_t v_didChange_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2736_; 
v___x_2720_ = lean_st_ref_take(v___y_2719_);
v_caches_2721_ = lean_ctor_get(v___x_2720_, 0);
v_typeAnalysis_2722_ = lean_ctor_get(v___x_2720_, 1);
v_target_2723_ = lean_ctor_get(v___x_2720_, 2);
v_hypotheses_2724_ = lean_ctor_get(v___x_2720_, 3);
v_didChange_2725_ = lean_ctor_get_uint8(v___x_2720_, sizeof(void*)*4);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2727_ = v___x_2720_;
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_hypotheses_2724_);
lean_inc(v_target_2723_);
lean_inc(v_typeAnalysis_2722_);
lean_inc(v_caches_2721_);
lean_dec(v___x_2720_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_array_push(v_hypotheses_2724_, v_hyp_2705_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 3, v___x_2730_);
v___x_2732_ = v___x_2727_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_caches_2721_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_typeAnalysis_2722_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_target_2723_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v___x_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2735_, sizeof(void*)*4, v_didChange_2725_);
v___x_2732_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_st_ref_put(v___y_2719_, v___x_2732_);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2729_);
return v___x_2734_;
}
}
}
v_resetjp_2755_:
{
lean_object* v_toFunctor_2758_; lean_object* v_toSeq_2759_; lean_object* v_toSeqLeft_2760_; lean_object* v_toSeqRight_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2803_; 
v_toFunctor_2758_ = lean_ctor_get(v_toApplicative_2754_, 0);
v_toSeq_2759_ = lean_ctor_get(v_toApplicative_2754_, 2);
v_toSeqLeft_2760_ = lean_ctor_get(v_toApplicative_2754_, 3);
v_toSeqRight_2761_ = lean_ctor_get(v_toApplicative_2754_, 4);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_toApplicative_2754_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v_toApplicative_2754_, 1);
lean_dec(v_unused_2804_);
v___x_2763_ = v_toApplicative_2754_;
v_isShared_2764_ = v_isSharedCheck_2803_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_toSeqRight_2761_);
lean_inc(v_toSeqLeft_2760_);
lean_inc(v_toSeq_2759_);
lean_inc(v_toFunctor_2758_);
lean_dec(v_toApplicative_2754_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2803_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___f_2765_; lean_object* v___f_2766_; lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; lean_object* v___f_2771_; lean_object* v___f_2772_; lean_object* v___x_2774_; 
v___f_2765_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2766_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2758_);
v___f_2767_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2767_, 0, v_toFunctor_2758_);
v___f_2768_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2768_, 0, v_toFunctor_2758_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___f_2767_);
lean_ctor_set(v___x_2769_, 1, v___f_2768_);
v___f_2770_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2770_, 0, v_toSeqRight_2761_);
v___f_2771_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2771_, 0, v_toSeqLeft_2760_);
v___f_2772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2772_, 0, v_toSeq_2759_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 4, v___f_2770_);
lean_ctor_set(v___x_2763_, 3, v___f_2771_);
lean_ctor_set(v___x_2763_, 2, v___f_2772_);
lean_ctor_set(v___x_2763_, 1, v___f_2765_);
lean_ctor_set(v___x_2763_, 0, v___x_2769_);
v___x_2774_ = v___x_2763_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v___f_2765_);
lean_ctor_set(v_reuseFailAlloc_2802_, 2, v___f_2772_);
lean_ctor_set(v_reuseFailAlloc_2802_, 3, v___f_2771_);
lean_ctor_set(v_reuseFailAlloc_2802_, 4, v___f_2770_);
v___x_2774_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2776_; 
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 1, v___f_2766_);
lean_ctor_set(v___x_2756_, 0, v___x_2774_);
v___x_2776_ = v___x_2756_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___f_2766_);
v___x_2776_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_toCold_2786_; lean_object* v_options_2787_; uint8_t v_hasTrace_2788_; 
v___x_2777_ = l_StateRefT_x27_instMonad___redArg(v___x_2776_);
v___x_2778_ = l_ReaderT_instMonad___redArg(v___x_2777_);
v___x_2779_ = l_StateRefT_x27_instMonad___redArg(v___x_2778_);
v___x_2780_ = l_ReaderT_instMonad___redArg(v___x_2779_);
v___x_2781_ = l_ReaderT_instMonad___redArg(v___x_2780_);
v___x_2782_ = l_StateRefT_x27_instMonad___redArg(v___x_2781_);
v___x_2783_ = l_ReaderT_instMonad___redArg(v___x_2782_);
v___x_2784_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2785_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toCold_2786_ = lean_ctor_get(v_a_2715_, 0);
v_options_2787_ = lean_ctor_get(v_toCold_2786_, 2);
v_hasTrace_2788_ = lean_ctor_get_uint8(v_options_2787_, sizeof(void*)*1);
if (v_hasTrace_2788_ == 0)
{
lean_dec_ref(v___x_2783_);
v___y_2719_ = v_a_2707_;
goto v___jp_2718_;
}
else
{
lean_object* v_toMonadRef_2789_; lean_object* v_inheritedTraceOptions_2790_; lean_object* v_cls_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v_toMonadRef_2789_ = lean_ctor_get(v___x_2785_, 0);
v_inheritedTraceOptions_2790_ = lean_ctor_get(v_toCold_2786_, 11);
v_cls_2791_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2792_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2790_, v_options_2787_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_dec_ref(v___x_2783_);
v___y_2719_ = v_a_2707_;
goto v___jp_2718_;
}
else
{
lean_object* v_type_2794_; lean_object* v___f_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_5398__overap_2799_; lean_object* v___x_2800_; 
v_type_2794_ = lean_ctor_get(v_hyp_2705_, 1);
v___f_2795_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_2796_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_2794_);
v___x_2797_ = l_Lean_MessageData_ofExpr(v_type_2794_);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
lean_inc_ref(v_toMonadRef_2789_);
v___x_5398__overap_2799_ = l_Lean_addTrace___redArg(v___x_2783_, v___x_2784_, v_toMonadRef_2789_, v___f_2795_, v_cls_2791_, v___x_2798_);
lean_inc(v_a_2716_);
lean_inc_ref(v_a_2715_);
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_a_2710_);
lean_inc_ref(v_a_2709_);
lean_inc(v_a_2708_);
lean_inc(v_a_2707_);
lean_inc_ref(v_a_2706_);
v___x_2800_ = lean_apply_12(v___x_5398__overap_2799_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, lean_box(0));
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_dec_ref_known(v___x_2800_, 1);
v___y_2719_ = v_a_2707_;
goto v___jp_2718_;
}
else
{
lean_dec_ref(v_hyp_2705_);
return v___x_2800_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v_toMonadRef_2823_, lean_object* v___f_2824_, lean_object* v_x_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_toCold_2842_; lean_object* v_options_2843_; uint8_t v_hasTrace_2844_; 
v_toCold_2842_ = lean_ctor_get(v___y_2836_, 0);
v_options_2843_ = lean_ctor_get(v_toCold_2842_, 2);
v_hasTrace_2844_ = lean_ctor_get_uint8(v_options_2843_, sizeof(void*)*1);
if (v_hasTrace_2844_ == 0)
{
lean_dec_ref(v___y_2826_);
lean_dec(v___f_2824_);
lean_dec_ref(v_toMonadRef_2823_);
lean_dec_ref(v___x_2822_);
lean_dec_ref(v___x_2821_);
goto v___jp_2839_;
}
else
{
lean_object* v_inheritedTraceOptions_2845_; lean_object* v_cls_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v_inheritedTraceOptions_2845_ = lean_ctor_get(v_toCold_2842_, 11);
v_cls_2846_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2847_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2848_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2845_, v_options_2843_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_dec_ref(v___y_2826_);
lean_dec(v___f_2824_);
lean_dec_ref(v_toMonadRef_2823_);
lean_dec_ref(v___x_2822_);
lean_dec_ref(v___x_2821_);
goto v___jp_2839_;
}
else
{
lean_object* v_type_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_6389__overap_2853_; lean_object* v___x_2854_; 
v_type_2849_ = lean_ctor_get(v___y_2826_, 1);
lean_inc_ref(v_type_2849_);
lean_dec_ref(v___y_2826_);
v___x_2850_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2851_ = l_Lean_MessageData_ofExpr(v_type_2849_);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_6389__overap_2853_ = l_Lean_addTrace___redArg(v___x_2821_, v___x_2822_, v_toMonadRef_2823_, v___f_2824_, v_cls_2846_, v___x_2852_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
lean_inc(v___y_2829_);
lean_inc(v___y_2828_);
lean_inc_ref(v___y_2827_);
v___x_2854_ = lean_apply_12(v___x_6389__overap_2853_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, lean_box(0));
return v___x_2854_;
}
}
v___jp_2839_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_box(0);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2855_ = _args[0];
lean_object* v___x_2856_ = _args[1];
lean_object* v_toMonadRef_2857_ = _args[2];
lean_object* v___f_2858_ = _args[3];
lean_object* v_x_2859_ = _args[4];
lean_object* v___y_2860_ = _args[5];
lean_object* v___y_2861_ = _args[6];
lean_object* v___y_2862_ = _args[7];
lean_object* v___y_2863_ = _args[8];
lean_object* v___y_2864_ = _args[9];
lean_object* v___y_2865_ = _args[10];
lean_object* v___y_2866_ = _args[11];
lean_object* v___y_2867_ = _args[12];
lean_object* v___y_2868_ = _args[13];
lean_object* v___y_2869_ = _args[14];
lean_object* v___y_2870_ = _args[15];
lean_object* v___y_2871_ = _args[16];
lean_object* v___y_2872_ = _args[17];
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2855_, v___x_2856_, v_toMonadRef_2857_, v___f_2858_, v_x_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v___y_2906_; lean_object* v___x_2907_; lean_object* v_toApplicative_2908_; lean_object* v_toFunctor_2909_; lean_object* v_toSeq_2910_; lean_object* v_toSeqLeft_2911_; lean_object* v_toSeqRight_2912_; lean_object* v___f_2913_; lean_object* v___f_2914_; lean_object* v___f_2915_; lean_object* v___f_2916_; lean_object* v___x_2917_; lean_object* v___f_2918_; lean_object* v___f_2919_; lean_object* v___f_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v_toApplicative_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2976_; 
v___x_2907_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2908_ = lean_ctor_get(v___x_2907_, 0);
v_toFunctor_2909_ = lean_ctor_get(v_toApplicative_2908_, 0);
v_toSeq_2910_ = lean_ctor_get(v_toApplicative_2908_, 2);
v_toSeqLeft_2911_ = lean_ctor_get(v_toApplicative_2908_, 3);
v_toSeqRight_2912_ = lean_ctor_get(v_toApplicative_2908_, 4);
v___f_2913_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2914_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2909_, 2);
v___f_2915_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2915_, 0, v_toFunctor_2909_);
v___f_2916_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2916_, 0, v_toFunctor_2909_);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___f_2915_);
lean_ctor_set(v___x_2917_, 1, v___f_2916_);
lean_inc(v_toSeqRight_2912_);
v___f_2918_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2918_, 0, v_toSeqRight_2912_);
lean_inc(v_toSeqLeft_2911_);
v___f_2919_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2919_, 0, v_toSeqLeft_2911_);
lean_inc(v_toSeq_2910_);
v___f_2920_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2920_, 0, v_toSeq_2910_);
v___x_2921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2917_);
lean_ctor_set(v___x_2921_, 1, v___f_2913_);
lean_ctor_set(v___x_2921_, 2, v___f_2920_);
lean_ctor_set(v___x_2921_, 3, v___f_2919_);
lean_ctor_set(v___x_2921_, 4, v___f_2918_);
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
lean_ctor_set(v___x_2922_, 1, v___f_2914_);
v___x_2923_ = l_StateRefT_x27_instMonad___redArg(v___x_2922_);
v_toApplicative_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v___x_2923_, 1);
lean_dec(v_unused_2977_);
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2976_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_toApplicative_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2976_;
goto v_resetjp_2925_;
}
v___jp_2887_:
{
lean_object* v___x_2888_; lean_object* v_caches_2889_; lean_object* v_typeAnalysis_2890_; lean_object* v_target_2891_; lean_object* v_hypotheses_2892_; uint8_t v_didChange_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2904_; 
v___x_2888_ = lean_st_ref_take(v_a_2876_);
v_caches_2889_ = lean_ctor_get(v___x_2888_, 0);
v_typeAnalysis_2890_ = lean_ctor_get(v___x_2888_, 1);
v_target_2891_ = lean_ctor_get(v___x_2888_, 2);
v_hypotheses_2892_ = lean_ctor_get(v___x_2888_, 3);
v_didChange_2893_ = lean_ctor_get_uint8(v___x_2888_, sizeof(void*)*4);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2895_ = v___x_2888_;
v_isShared_2896_ = v_isSharedCheck_2904_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_hypotheses_2892_);
lean_inc(v_target_2891_);
lean_inc(v_typeAnalysis_2890_);
lean_inc(v_caches_2889_);
lean_dec(v___x_2888_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2904_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2897_ = lean_box(0);
v___x_2898_ = l_Array_append___redArg(v_hypotheses_2892_, v_hyps_2874_);
lean_dec_ref(v_hyps_2874_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 3, v___x_2898_);
v___x_2900_ = v___x_2895_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_caches_2889_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_typeAnalysis_2890_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_target_2891_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v___x_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2903_, sizeof(void*)*4, v_didChange_2893_);
v___x_2900_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_st_ref_put(v_a_2876_, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2897_);
return v___x_2902_;
}
}
}
v___jp_2905_:
{
if (lean_obj_tag(v___y_2906_) == 0)
{
lean_dec_ref_known(v___y_2906_, 1);
goto v___jp_2887_;
}
else
{
lean_dec_ref(v_hyps_2874_);
return v___y_2906_;
}
}
v_resetjp_2925_:
{
lean_object* v_toFunctor_2928_; lean_object* v_toSeq_2929_; lean_object* v_toSeqLeft_2930_; lean_object* v_toSeqRight_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2974_; 
v_toFunctor_2928_ = lean_ctor_get(v_toApplicative_2924_, 0);
v_toSeq_2929_ = lean_ctor_get(v_toApplicative_2924_, 2);
v_toSeqLeft_2930_ = lean_ctor_get(v_toApplicative_2924_, 3);
v_toSeqRight_2931_ = lean_ctor_get(v_toApplicative_2924_, 4);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_toApplicative_2924_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; 
v_unused_2975_ = lean_ctor_get(v_toApplicative_2924_, 1);
lean_dec(v_unused_2975_);
v___x_2933_ = v_toApplicative_2924_;
v_isShared_2934_ = v_isSharedCheck_2974_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_toSeqRight_2931_);
lean_inc(v_toSeqLeft_2930_);
lean_inc(v_toSeq_2929_);
lean_inc(v_toFunctor_2928_);
lean_dec(v_toApplicative_2924_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2974_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___f_2935_; lean_object* v___f_2936_; lean_object* v___f_2937_; lean_object* v___f_2938_; lean_object* v___x_2939_; lean_object* v___f_2940_; lean_object* v___f_2941_; lean_object* v___f_2942_; lean_object* v___x_2944_; 
v___f_2935_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2936_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2928_);
v___f_2937_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2937_, 0, v_toFunctor_2928_);
v___f_2938_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2938_, 0, v_toFunctor_2928_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___f_2937_);
lean_ctor_set(v___x_2939_, 1, v___f_2938_);
v___f_2940_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2940_, 0, v_toSeqRight_2931_);
v___f_2941_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2941_, 0, v_toSeqLeft_2930_);
v___f_2942_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2942_, 0, v_toSeq_2929_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 4, v___f_2940_);
lean_ctor_set(v___x_2933_, 3, v___f_2941_);
lean_ctor_set(v___x_2933_, 2, v___f_2942_);
lean_ctor_set(v___x_2933_, 1, v___f_2935_);
lean_ctor_set(v___x_2933_, 0, v___x_2939_);
v___x_2944_ = v___x_2933_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___f_2935_);
lean_ctor_set(v_reuseFailAlloc_2973_, 2, v___f_2942_);
lean_ctor_set(v_reuseFailAlloc_2973_, 3, v___f_2941_);
lean_ctor_set(v_reuseFailAlloc_2973_, 4, v___f_2940_);
v___x_2944_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2946_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v___f_2936_);
lean_ctor_set(v___x_2926_, 0, v___x_2944_);
v___x_2946_ = v___x_2926_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___f_2936_);
v___x_2946_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v_toMonadRef_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2947_ = l_StateRefT_x27_instMonad___redArg(v___x_2946_);
v___x_2948_ = l_ReaderT_instMonad___redArg(v___x_2947_);
v___x_2949_ = l_StateRefT_x27_instMonad___redArg(v___x_2948_);
v___x_2950_ = l_ReaderT_instMonad___redArg(v___x_2949_);
v___x_2951_ = l_ReaderT_instMonad___redArg(v___x_2950_);
v___x_2952_ = l_StateRefT_x27_instMonad___redArg(v___x_2951_);
v___x_2953_ = l_ReaderT_instMonad___redArg(v___x_2952_);
v___x_2954_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2955_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_2956_ = lean_ctor_get(v___x_2955_, 0);
v___x_2957_ = lean_unsigned_to_nat(0u);
v___x_2958_ = lean_array_get_size(v_hyps_2874_);
v___x_2959_ = lean_nat_dec_lt(v___x_2957_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_dec_ref(v___x_2953_);
goto v___jp_2887_;
}
else
{
lean_object* v___f_2960_; lean_object* v___f_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___f_2960_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
lean_inc_ref(v_toMonadRef_2956_);
lean_inc_ref(v___x_2953_);
v___f_2961_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 18, 4);
lean_closure_set(v___f_2961_, 0, v___x_2953_);
lean_closure_set(v___f_2961_, 1, v___x_2954_);
lean_closure_set(v___f_2961_, 2, v_toMonadRef_2956_);
lean_closure_set(v___f_2961_, 3, v___f_2960_);
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_nat_dec_le(v___x_2958_, v___x_2958_);
if (v___x_2963_ == 0)
{
if (v___x_2959_ == 0)
{
lean_dec_ref(v___f_2961_);
lean_dec_ref(v___x_2953_);
goto v___jp_2887_;
}
else
{
size_t v___x_2964_; size_t v___x_2965_; lean_object* v___x_6041__overap_2966_; lean_object* v___x_2967_; 
v___x_2964_ = ((size_t)0ULL);
v___x_2965_ = lean_usize_of_nat(v___x_2958_);
lean_inc_ref(v_hyps_2874_);
v___x_6041__overap_2966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2953_, v___f_2961_, v_hyps_2874_, v___x_2964_, v___x_2965_, v___x_2962_);
lean_inc(v_a_2885_);
lean_inc_ref(v_a_2884_);
lean_inc(v_a_2883_);
lean_inc_ref(v_a_2882_);
lean_inc(v_a_2881_);
lean_inc_ref(v_a_2880_);
lean_inc(v_a_2879_);
lean_inc_ref(v_a_2878_);
lean_inc(v_a_2877_);
lean_inc(v_a_2876_);
lean_inc_ref(v_a_2875_);
v___x_2967_ = lean_apply_12(v___x_6041__overap_2966_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, lean_box(0));
v___y_2906_ = v___x_2967_;
goto v___jp_2905_;
}
}
else
{
size_t v___x_2968_; size_t v___x_2969_; lean_object* v___x_6044__overap_2970_; lean_object* v___x_2971_; 
v___x_2968_ = ((size_t)0ULL);
v___x_2969_ = lean_usize_of_nat(v___x_2958_);
lean_inc_ref(v_hyps_2874_);
v___x_6044__overap_2970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2953_, v___f_2961_, v_hyps_2874_, v___x_2968_, v___x_2969_, v___x_2962_);
lean_inc(v_a_2885_);
lean_inc_ref(v_a_2884_);
lean_inc(v_a_2883_);
lean_inc_ref(v_a_2882_);
lean_inc(v_a_2881_);
lean_inc_ref(v_a_2880_);
lean_inc(v_a_2879_);
lean_inc_ref(v_a_2878_);
lean_inc(v_a_2877_);
lean_inc(v_a_2876_);
lean_inc_ref(v_a_2875_);
v___x_2971_ = lean_apply_12(v___x_6044__overap_2970_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, lean_box(0));
v___y_2906_ = v___x_2971_;
goto v___jp_2905_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_2992_){
_start:
{
lean_object* v___x_2994_; lean_object* v_hypotheses_2995_; lean_object* v___x_2996_; 
v___x_2994_ = lean_st_ref_get(v_a_2992_);
v_hypotheses_2995_ = lean_ctor_get(v___x_2994_, 3);
lean_inc_ref(v_hypotheses_2995_);
lean_dec(v___x_2994_);
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_hypotheses_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_2997_);
lean_dec(v_a_2997_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v___x_3012_; lean_object* v_hypotheses_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_st_ref_get(v_a_3001_);
v_hypotheses_3013_ = lean_ctor_get(v___x_3012_, 3);
lean_inc_ref(v_hypotheses_3013_);
lean_dec(v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_hypotheses_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___x_3041_; lean_object* v_caches_3042_; lean_object* v_typeAnalysis_3043_; lean_object* v_target_3044_; uint8_t v_didChange_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3055_; 
v___x_3041_ = lean_st_ref_take(v___y_3030_);
v_caches_3042_ = lean_ctor_get(v___x_3041_, 0);
v_typeAnalysis_3043_ = lean_ctor_get(v___x_3041_, 1);
v_target_3044_ = lean_ctor_get(v___x_3041_, 2);
v_didChange_3045_ = lean_ctor_get_uint8(v___x_3041_, sizeof(void*)*4);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; 
v_unused_3056_ = lean_ctor_get(v___x_3041_, 3);
lean_dec(v_unused_3056_);
v___x_3047_ = v___x_3041_;
v_isShared_3048_ = v_isSharedCheck_3055_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_target_3044_);
lean_inc(v_typeAnalysis_3043_);
lean_inc(v_caches_3042_);
lean_dec(v___x_3041_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3055_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = lean_box(0);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 3, v_hyps_3028_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_caches_3042_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_typeAnalysis_3043_);
lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_target_3044_);
lean_ctor_set(v_reuseFailAlloc_3054_, 3, v_hyps_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3054_, sizeof(void*)*4, v_didChange_3045_);
v___x_3051_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_st_ref_put(v___y_3030_, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3049_);
return v___x_3053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3071_, lean_object* v_hyps_3072_){
_start:
{
lean_object* v___f_3073_; lean_object* v___x_3074_; 
v___f_3073_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3073_, 0, v_hyps_3072_);
v___x_3074_ = lean_apply_2(v_inst_3071_, lean_box(0), v___f_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; lean_object* v_caches_3088_; lean_object* v_typeAnalysis_3089_; lean_object* v_target_3090_; uint8_t v_didChange_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3102_; 
v___x_3087_ = lean_st_ref_take(v___y_3076_);
v_caches_3088_ = lean_ctor_get(v___x_3087_, 0);
v_typeAnalysis_3089_ = lean_ctor_get(v___x_3087_, 1);
v_target_3090_ = lean_ctor_get(v___x_3087_, 2);
v_didChange_3091_ = lean_ctor_get_uint8(v___x_3087_, sizeof(void*)*4);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v___x_3087_, 3);
lean_dec(v_unused_3103_);
v___x_3093_ = v___x_3087_;
v_isShared_3094_ = v_isSharedCheck_3102_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_target_3090_);
lean_inc(v_typeAnalysis_3089_);
lean_inc(v_caches_3088_);
lean_dec(v___x_3087_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3102_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3095_ = lean_box(0);
v___x_3096_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 3, v___x_3096_);
v___x_3098_ = v___x_3093_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_caches_3088_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_typeAnalysis_3089_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_target_3090_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v___x_3096_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, sizeof(void*)*4, v_didChange_3091_);
v___x_3098_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_st_ref_put(v___y_3076_, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3095_);
return v___x_3100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3117_, lean_object* v_cls_3118_, lean_object* v_____do__lift_3119_, lean_object* v_____do__lift_3120_){
_start:
{
uint8_t v_hasTrace_3121_; 
v_hasTrace_3121_ = lean_ctor_get_uint8(v_____do__lift_3120_, sizeof(void*)*1);
if (v_hasTrace_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec(v_cls_3118_);
v___x_3122_ = lean_box(v_hasTrace_3121_);
v___x_3123_ = lean_apply_2(v_toPure_3117_, lean_box(0), v___x_3122_);
return v___x_3123_;
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3124_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3125_ = l_Lean_Name_append(v___x_3124_, v_cls_3118_);
v___x_3126_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3119_, v_____do__lift_3120_, v___x_3125_);
lean_dec(v___x_3125_);
v___x_3127_ = lean_box(v___x_3126_);
v___x_3128_ = lean_apply_2(v_toPure_3117_, lean_box(0), v___x_3127_);
return v___x_3128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3129_, lean_object* v_cls_3130_, lean_object* v_____do__lift_3131_, lean_object* v_____do__lift_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3129_, v_cls_3130_, v_____do__lift_3131_, v_____do__lift_3132_);
lean_dec_ref(v_____do__lift_3132_);
lean_dec_ref(v_____do__lift_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_inst_3134_, lean_object* v_toPure_3135_, lean_object* v_cls_3136_, lean_object* v_toBind_3137_, lean_object* v_____do__lift_3138_){
_start:
{
lean_object* v_getOptionsUnrestricted_3139_; lean_object* v___f_3140_; lean_object* v___x_3141_; 
v_getOptionsUnrestricted_3139_ = lean_ctor_get(v_inst_3134_, 1);
lean_inc(v_getOptionsUnrestricted_3139_);
lean_dec_ref(v_inst_3134_);
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3140_, 0, v_toPure_3135_);
lean_closure_set(v___f_3140_, 1, v_cls_3136_);
lean_closure_set(v___f_3140_, 2, v_____do__lift_3138_);
v___x_3141_ = lean_apply_4(v_toBind_3137_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3139_, v___f_3140_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3144_ = l_Lean_stringToMessageData(v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3145_, lean_object* v_a_3146_, lean_object* v___y_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_cls_3152_, uint8_t v_____do__lift_3153_){
_start:
{
if (v_____do__lift_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
lean_dec(v_cls_3152_);
lean_dec(v_inst_3151_);
lean_dec_ref(v_inst_3150_);
lean_dec_ref(v_inst_3149_);
lean_dec_ref(v_inst_3148_);
lean_dec_ref(v___y_3147_);
lean_dec_ref(v_a_3146_);
v___x_3154_ = lean_box(0);
v___x_3155_ = lean_apply_2(v_toPure_3145_, lean_box(0), v___x_3154_);
return v___x_3155_;
}
else
{
lean_object* v_type_3156_; lean_object* v_type_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
lean_dec(v_toPure_3145_);
v_type_3156_ = lean_ctor_get(v_a_3146_, 1);
lean_inc_ref(v_type_3156_);
lean_dec_ref(v_a_3146_);
v_type_3157_ = lean_ctor_get(v___y_3147_, 1);
lean_inc_ref(v_type_3157_);
lean_dec_ref(v___y_3147_);
v___x_3158_ = l_Lean_MessageData_ofExpr(v_type_3156_);
v___x_3159_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = l_Lean_MessageData_ofExpr(v_type_3157_);
v___x_3162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = l_Lean_addTrace___redArg(v_inst_3148_, v_inst_3149_, v_inst_3150_, v_inst_3151_, v_cls_3152_, v___x_3162_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3164_, lean_object* v_a_3165_, lean_object* v___y_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_cls_3171_, lean_object* v_____do__lift_3172_){
_start:
{
uint8_t v_____do__lift_3040__boxed_3173_; lean_object* v_res_3174_; 
v_____do__lift_3040__boxed_3173_ = lean_unbox(v_____do__lift_3172_);
v_res_3174_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3164_, v_a_3165_, v___y_3166_, v_inst_3167_, v_inst_3168_, v_inst_3169_, v_inst_3170_, v_cls_3171_, v_____do__lift_3040__boxed_3173_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_toPure_3177_, lean_object* v_toBind_3178_, lean_object* v_a_3179_, lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_x_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_getInheritedTraceOptions_3185_; lean_object* v_cls_3186_; lean_object* v___f_3187_; lean_object* v___f_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_getInheritedTraceOptions_3185_ = lean_ctor_get(v_inst_3175_, 2);
lean_inc(v_getInheritedTraceOptions_3185_);
v_cls_3186_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3178_, 2);
lean_inc(v_toPure_3177_);
v___f_3187_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3187_, 0, v_inst_3176_);
lean_closure_set(v___f_3187_, 1, v_toPure_3177_);
lean_closure_set(v___f_3187_, 2, v_cls_3186_);
lean_closure_set(v___f_3187_, 3, v_toBind_3178_);
v___f_3188_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3188_, 0, v_toPure_3177_);
lean_closure_set(v___f_3188_, 1, v_a_3179_);
lean_closure_set(v___f_3188_, 2, v___y_3184_);
lean_closure_set(v___f_3188_, 3, v_inst_3180_);
lean_closure_set(v___f_3188_, 4, v_inst_3175_);
lean_closure_set(v___f_3188_, 5, v_inst_3181_);
lean_closure_set(v___f_3188_, 6, v_inst_3182_);
lean_closure_set(v___f_3188_, 7, v_cls_3186_);
v___x_3189_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3185_, v___f_3187_);
v___x_3190_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v___x_3189_, v___f_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3191_, lean_object* v_res_3192_, lean_object* v_____r_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_apply_2(v_toPure_3191_, lean_box(0), v_res_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3195_, lean_object* v_toBind_3196_, lean_object* v___f_3197_, lean_object* v_____r_3198_){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3200_ = lean_apply_2(v_inst_3195_, lean_box(0), v___x_3199_);
v___x_3201_ = lean_apply_4(v_toBind_3196_, lean_box(0), lean_box(0), v___x_3200_, v___f_3197_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3202_, lean_object* v_____r_3203_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_apply_1(v___f_3202_, v_____r_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3205_, lean_object* v_type_3206_, lean_object* v_type_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_cls_3212_, lean_object* v_toBind_3213_, lean_object* v___f_3214_, uint8_t v_____do__lift_3215_){
_start:
{
if (v_____do__lift_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_dec(v___f_3214_);
lean_dec(v_toBind_3213_);
lean_dec(v_cls_3212_);
lean_dec(v_inst_3211_);
lean_dec_ref(v_inst_3210_);
lean_dec_ref(v_inst_3209_);
lean_dec_ref(v_inst_3208_);
lean_dec_ref(v_type_3207_);
lean_dec_ref(v_type_3206_);
v___x_3216_ = lean_box(0);
v___x_3217_ = lean_apply_1(v___f_3205_, v___x_3216_);
return v___x_3217_;
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
lean_dec(v___f_3205_);
v___x_3218_ = l_Lean_MessageData_ofExpr(v_type_3206_);
v___x_3219_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = l_Lean_MessageData_ofExpr(v_type_3207_);
v___x_3222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = l_Lean_addTrace___redArg(v_inst_3208_, v_inst_3209_, v_inst_3210_, v_inst_3211_, v_cls_3212_, v___x_3222_);
v___x_3224_ = lean_apply_4(v_toBind_3213_, lean_box(0), lean_box(0), v___x_3223_, v___f_3214_);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3225_, lean_object* v_type_3226_, lean_object* v_type_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_cls_3232_, lean_object* v_toBind_3233_, lean_object* v___f_3234_, lean_object* v_____do__lift_3235_){
_start:
{
uint8_t v_____do__lift_3140__boxed_3236_; lean_object* v_res_3237_; 
v_____do__lift_3140__boxed_3236_ = lean_unbox(v_____do__lift_3235_);
v_res_3237_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3225_, v_type_3226_, v_type_3227_, v_inst_3228_, v_inst_3229_, v_inst_3230_, v_inst_3231_, v_cls_3232_, v_toBind_3233_, v___f_3234_, v_____do__lift_3140__boxed_3236_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3238_, lean_object* v_inst_3239_, lean_object* v_toBind_3240_, lean_object* v_inst_3241_, lean_object* v___f_3242_, lean_object* v_a_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v___f_3248_, lean_object* v_res_3249_){
_start:
{
lean_object* v___x_3250_; lean_object* v_zero_3251_; uint8_t v_isZero_3252_; 
v___x_3250_ = lean_array_get_size(v_res_3249_);
v_zero_3251_ = lean_unsigned_to_nat(0u);
v_isZero_3252_ = lean_nat_dec_eq(v___x_3250_, v_zero_3251_);
if (v_isZero_3252_ == 1)
{
lean_object* v___f_3253_; lean_object* v___f_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
lean_dec(v___f_3248_);
lean_dec(v_inst_3247_);
lean_dec_ref(v_inst_3246_);
lean_dec_ref(v_inst_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_a_3243_);
lean_inc_ref(v_res_3249_);
lean_inc(v_toPure_3238_);
v___f_3253_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3253_, 0, v_toPure_3238_);
lean_closure_set(v___f_3253_, 1, v_res_3249_);
lean_inc(v_toBind_3240_);
v___f_3254_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3254_, 0, v_inst_3239_);
lean_closure_set(v___f_3254_, 1, v_toBind_3240_);
lean_closure_set(v___f_3254_, 2, v___f_3253_);
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_nat_dec_lt(v_zero_3251_, v___x_3250_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_dec_ref(v_res_3249_);
lean_dec(v___f_3242_);
lean_dec_ref(v_inst_3241_);
v___x_3257_ = lean_apply_2(v_toPure_3238_, lean_box(0), v___x_3255_);
v___x_3258_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3257_, v___f_3254_);
return v___x_3258_;
}
else
{
uint8_t v___x_3259_; 
v___x_3259_ = lean_nat_dec_le(v___x_3250_, v___x_3250_);
if (v___x_3259_ == 0)
{
if (v___x_3256_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec_ref(v_res_3249_);
lean_dec(v___f_3242_);
lean_dec_ref(v_inst_3241_);
v___x_3260_ = lean_apply_2(v_toPure_3238_, lean_box(0), v___x_3255_);
v___x_3261_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3260_, v___f_3254_);
return v___x_3261_;
}
else
{
size_t v___x_3262_; size_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec(v_toPure_3238_);
v___x_3262_ = ((size_t)0ULL);
v___x_3263_ = lean_usize_of_nat(v___x_3250_);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3241_, v___f_3242_, v_res_3249_, v___x_3262_, v___x_3263_, v___x_3255_);
v___x_3265_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3264_, v___f_3254_);
return v___x_3265_;
}
}
else
{
size_t v___x_3266_; size_t v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_dec(v_toPure_3238_);
v___x_3266_ = ((size_t)0ULL);
v___x_3267_ = lean_usize_of_nat(v___x_3250_);
v___x_3268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3241_, v___f_3242_, v_res_3249_, v___x_3266_, v___x_3267_, v___x_3255_);
v___x_3269_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3268_, v___f_3254_);
return v___x_3269_;
}
}
}
else
{
lean_object* v_one_3270_; lean_object* v_n_3271_; uint8_t v_isZero_3272_; 
lean_dec(v___f_3242_);
v_one_3270_ = lean_unsigned_to_nat(1u);
v_n_3271_ = lean_nat_sub(v___x_3250_, v_one_3270_);
v_isZero_3272_ = lean_nat_dec_eq(v_n_3271_, v_zero_3251_);
lean_dec(v_n_3271_);
if (v_isZero_3272_ == 1)
{
lean_object* v_newHyp_3273_; lean_object* v_type_3274_; lean_object* v_type_3275_; uint8_t v___x_3276_; 
lean_dec(v___f_3248_);
v_newHyp_3273_ = lean_array_fget_borrowed(v_res_3249_, v_zero_3251_);
v_type_3274_ = lean_ctor_get(v_newHyp_3273_, 1);
v_type_3275_ = lean_ctor_get(v_a_3243_, 1);
lean_inc_ref(v_type_3275_);
lean_dec_ref(v_a_3243_);
v___x_3276_ = lean_expr_eqv(v_type_3274_, v_type_3275_);
if (v___x_3276_ == 0)
{
lean_object* v_getInheritedTraceOptions_3277_; lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___f_3280_; lean_object* v_cls_3281_; lean_object* v___f_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_inc_ref(v_type_3274_);
v_getInheritedTraceOptions_3277_ = lean_ctor_get(v_inst_3244_, 2);
lean_inc(v_getInheritedTraceOptions_3277_);
lean_inc(v_toPure_3238_);
v___f_3278_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3278_, 0, v_toPure_3238_);
lean_closure_set(v___f_3278_, 1, v_res_3249_);
lean_inc_n(v_toBind_3240_, 4);
v___f_3279_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3279_, 0, v_inst_3239_);
lean_closure_set(v___f_3279_, 1, v_toBind_3240_);
lean_closure_set(v___f_3279_, 2, v___f_3278_);
lean_inc_ref(v___f_3279_);
v___f_3280_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3280_, 0, v___f_3279_);
v_cls_3281_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3282_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3282_, 0, v_inst_3245_);
lean_closure_set(v___f_3282_, 1, v_toPure_3238_);
lean_closure_set(v___f_3282_, 2, v_cls_3281_);
lean_closure_set(v___f_3282_, 3, v_toBind_3240_);
v___f_3283_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3283_, 0, v___f_3279_);
lean_closure_set(v___f_3283_, 1, v_type_3275_);
lean_closure_set(v___f_3283_, 2, v_type_3274_);
lean_closure_set(v___f_3283_, 3, v_inst_3241_);
lean_closure_set(v___f_3283_, 4, v_inst_3244_);
lean_closure_set(v___f_3283_, 5, v_inst_3246_);
lean_closure_set(v___f_3283_, 6, v_inst_3247_);
lean_closure_set(v___f_3283_, 7, v_cls_3281_);
lean_closure_set(v___f_3283_, 8, v_toBind_3240_);
lean_closure_set(v___f_3283_, 9, v___f_3280_);
v___x_3284_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3277_, v___f_3282_);
v___x_3285_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3284_, v___f_3283_);
return v___x_3285_;
}
else
{
lean_object* v___x_3286_; 
lean_dec_ref(v_type_3275_);
lean_dec(v_inst_3247_);
lean_dec_ref(v_inst_3246_);
lean_dec_ref(v_inst_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_inst_3241_);
lean_dec(v_toBind_3240_);
lean_dec(v_inst_3239_);
v___x_3286_ = lean_apply_2(v_toPure_3238_, lean_box(0), v_res_3249_);
return v___x_3286_;
}
}
else
{
lean_object* v___f_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
lean_dec(v_inst_3247_);
lean_dec_ref(v_inst_3246_);
lean_dec_ref(v_inst_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_a_3243_);
lean_inc_ref(v_res_3249_);
lean_inc(v_toPure_3238_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3287_, 0, v_toPure_3238_);
lean_closure_set(v___f_3287_, 1, v_res_3249_);
lean_inc(v_toBind_3240_);
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3288_, 0, v_inst_3239_);
lean_closure_set(v___f_3288_, 1, v_toBind_3240_);
lean_closure_set(v___f_3288_, 2, v___f_3287_);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_nat_dec_lt(v_zero_3251_, v___x_3250_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_dec_ref(v_res_3249_);
lean_dec(v___f_3248_);
lean_dec_ref(v_inst_3241_);
v___x_3291_ = lean_apply_2(v_toPure_3238_, lean_box(0), v___x_3289_);
v___x_3292_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3291_, v___f_3288_);
return v___x_3292_;
}
else
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_nat_dec_le(v___x_3250_, v___x_3250_);
if (v___x_3293_ == 0)
{
if (v___x_3290_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec_ref(v_res_3249_);
lean_dec(v___f_3248_);
lean_dec_ref(v_inst_3241_);
v___x_3294_ = lean_apply_2(v_toPure_3238_, lean_box(0), v___x_3289_);
v___x_3295_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3294_, v___f_3288_);
return v___x_3295_;
}
else
{
size_t v___x_3296_; size_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v_toPure_3238_);
v___x_3296_ = ((size_t)0ULL);
v___x_3297_ = lean_usize_of_nat(v___x_3250_);
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3241_, v___f_3248_, v_res_3249_, v___x_3296_, v___x_3297_, v___x_3289_);
v___x_3299_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3298_, v___f_3288_);
return v___x_3299_;
}
}
else
{
size_t v___x_3300_; size_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec(v_toPure_3238_);
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = lean_usize_of_nat(v___x_3250_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3241_, v___f_3248_, v_res_3249_, v___x_3300_, v___x_3301_, v___x_3289_);
v___x_3303_ = lean_apply_4(v_toBind_3240_, lean_box(0), lean_box(0), v___x_3302_, v___f_3288_);
return v___x_3303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3304_, lean_object* v_toPure_3305_, lean_object* v_____do__lift_3306_){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = l_Array_append___redArg(v_bs_3304_, v_____do__lift_3306_);
v___x_3308_ = lean_apply_2(v_toPure_3305_, lean_box(0), v___x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3309_, lean_object* v_toPure_3310_, lean_object* v_____do__lift_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3309_, v_toPure_3310_, v_____do__lift_3311_);
lean_dec_ref(v_____do__lift_3311_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_toPure_3315_, lean_object* v_toBind_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_f_3321_, lean_object* v_bs_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v___f_3324_; lean_object* v___f_3325_; lean_object* v___f_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_inc(v_inst_3319_);
lean_inc_ref(v_inst_3318_);
lean_inc_ref(v_inst_3317_);
lean_inc_ref_n(v_a_3323_, 2);
lean_inc_n(v_toBind_3316_, 3);
lean_inc_n(v_toPure_3315_, 2);
lean_inc_ref(v_inst_3314_);
lean_inc_ref(v_inst_3313_);
v___f_3324_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3324_, 0, v_inst_3313_);
lean_closure_set(v___f_3324_, 1, v_inst_3314_);
lean_closure_set(v___f_3324_, 2, v_toPure_3315_);
lean_closure_set(v___f_3324_, 3, v_toBind_3316_);
lean_closure_set(v___f_3324_, 4, v_a_3323_);
lean_closure_set(v___f_3324_, 5, v_inst_3317_);
lean_closure_set(v___f_3324_, 6, v_inst_3318_);
lean_closure_set(v___f_3324_, 7, v_inst_3319_);
lean_inc_ref(v___f_3324_);
v___f_3325_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3325_, 0, v_toPure_3315_);
lean_closure_set(v___f_3325_, 1, v_inst_3320_);
lean_closure_set(v___f_3325_, 2, v_toBind_3316_);
lean_closure_set(v___f_3325_, 3, v_inst_3317_);
lean_closure_set(v___f_3325_, 4, v___f_3324_);
lean_closure_set(v___f_3325_, 5, v_a_3323_);
lean_closure_set(v___f_3325_, 6, v_inst_3313_);
lean_closure_set(v___f_3325_, 7, v_inst_3314_);
lean_closure_set(v___f_3325_, 8, v_inst_3318_);
lean_closure_set(v___f_3325_, 9, v_inst_3319_);
lean_closure_set(v___f_3325_, 10, v___f_3324_);
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3326_, 0, v_bs_3322_);
lean_closure_set(v___f_3326_, 1, v_toPure_3315_);
v___x_3327_ = lean_apply_1(v_f_3321_, v_a_3323_);
v___x_3328_ = lean_apply_4(v_toBind_3316_, lean_box(0), lean_box(0), v___x_3327_, v___f_3325_);
v___x_3329_ = lean_apply_4(v_toBind_3316_, lean_box(0), lean_box(0), v___x_3328_, v___f_3326_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3332_, lean_object* v_toPure_3333_, lean_object* v_toBind_3334_, lean_object* v___f_3335_, lean_object* v_inst_3336_, lean_object* v___f_3337_, lean_object* v_____r_3338_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3339_ = lean_unsigned_to_nat(0u);
v___x_3340_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3341_ = lean_array_get_size(v_hyps_3332_);
v___x_3342_ = lean_nat_dec_lt(v___x_3339_, v___x_3341_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec(v___f_3337_);
lean_dec_ref(v_inst_3336_);
lean_dec_ref(v_hyps_3332_);
v___x_3343_ = lean_apply_2(v_toPure_3333_, lean_box(0), v___x_3340_);
v___x_3344_ = lean_apply_4(v_toBind_3334_, lean_box(0), lean_box(0), v___x_3343_, v___f_3335_);
return v___x_3344_;
}
else
{
size_t v___x_3345_; size_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec(v_toPure_3333_);
v___x_3345_ = ((size_t)0ULL);
v___x_3346_ = lean_usize_of_nat(v___x_3341_);
v___x_3347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3336_, v___f_3337_, v_hyps_3332_, v___x_3345_, v___x_3346_, v___x_3340_);
v___x_3348_ = lean_apply_4(v_toBind_3334_, lean_box(0), lean_box(0), v___x_3347_, v___f_3335_);
return v___x_3348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3349_, lean_object* v_toBind_3350_, lean_object* v___f_3351_, lean_object* v_inst_3352_, lean_object* v___f_3353_, lean_object* v_inst_3354_, lean_object* v___f_3355_, lean_object* v_hyps_3356_){
_start:
{
lean_object* v___f_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
lean_inc(v_toBind_3350_);
v___f_3357_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3357_, 0, v_hyps_3356_);
lean_closure_set(v___f_3357_, 1, v_toPure_3349_);
lean_closure_set(v___f_3357_, 2, v_toBind_3350_);
lean_closure_set(v___f_3357_, 3, v___f_3351_);
lean_closure_set(v___f_3357_, 4, v_inst_3352_);
lean_closure_set(v___f_3357_, 5, v___f_3353_);
v___x_3358_ = lean_apply_2(v_inst_3354_, lean_box(0), v___f_3355_);
v___x_3359_ = lean_apply_4(v_toBind_3350_, lean_box(0), lean_box(0), v___x_3358_, v___f_3357_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3361_, lean_object* v_inst_3362_, lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_inst_3365_, lean_object* v_inst_3366_, lean_object* v_f_3367_){
_start:
{
lean_object* v_toApplicative_3368_; lean_object* v_toBind_3369_; lean_object* v_toPure_3370_; lean_object* v___f_3371_; lean_object* v___f_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___f_3375_; lean_object* v___f_3376_; lean_object* v___x_3377_; 
v_toApplicative_3368_ = lean_ctor_get(v_inst_3361_, 0);
v_toBind_3369_ = lean_ctor_get(v_inst_3361_, 1);
lean_inc_n(v_toBind_3369_, 3);
v_toPure_3370_ = lean_ctor_get(v_toApplicative_3368_, 1);
lean_inc_n(v_toPure_3370_, 2);
lean_inc_n(v_inst_3366_, 3);
v___f_3371_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3371_, 0, v_inst_3366_);
v___f_3372_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3373_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3374_ = lean_apply_2(v_inst_3366_, lean_box(0), v___x_3373_);
lean_inc_ref(v_inst_3361_);
v___f_3375_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3375_, 0, v_inst_3362_);
lean_closure_set(v___f_3375_, 1, v_inst_3363_);
lean_closure_set(v___f_3375_, 2, v_toPure_3370_);
lean_closure_set(v___f_3375_, 3, v_toBind_3369_);
lean_closure_set(v___f_3375_, 4, v_inst_3361_);
lean_closure_set(v___f_3375_, 5, v_inst_3365_);
lean_closure_set(v___f_3375_, 6, v_inst_3364_);
lean_closure_set(v___f_3375_, 7, v_inst_3366_);
lean_closure_set(v___f_3375_, 8, v_f_3367_);
v___f_3376_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3376_, 0, v_toPure_3370_);
lean_closure_set(v___f_3376_, 1, v_toBind_3369_);
lean_closure_set(v___f_3376_, 2, v___f_3371_);
lean_closure_set(v___f_3376_, 3, v_inst_3361_);
lean_closure_set(v___f_3376_, 4, v___f_3375_);
lean_closure_set(v___f_3376_, 5, v_inst_3366_);
lean_closure_set(v___f_3376_, 6, v___f_3372_);
v___x_3377_ = lean_apply_4(v_toBind_3369_, lean_box(0), lean_box(0), v___x_3374_, v___f_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3378_, lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_inst_3383_, lean_object* v_inst_3384_, lean_object* v_f_3385_){
_start:
{
lean_object* v_toApplicative_3386_; lean_object* v_toBind_3387_; lean_object* v_toPure_3388_; lean_object* v___f_3389_; lean_object* v___f_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___f_3393_; lean_object* v___f_3394_; lean_object* v___x_3395_; 
v_toApplicative_3386_ = lean_ctor_get(v_inst_3379_, 0);
v_toBind_3387_ = lean_ctor_get(v_inst_3379_, 1);
lean_inc_n(v_toBind_3387_, 3);
v_toPure_3388_ = lean_ctor_get(v_toApplicative_3386_, 1);
lean_inc_n(v_toPure_3388_, 2);
lean_inc_n(v_inst_3384_, 3);
v___f_3389_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3389_, 0, v_inst_3384_);
v___f_3390_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3391_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3392_ = lean_apply_2(v_inst_3384_, lean_box(0), v___x_3391_);
lean_inc_ref(v_inst_3379_);
v___f_3393_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3393_, 0, v_inst_3380_);
lean_closure_set(v___f_3393_, 1, v_inst_3381_);
lean_closure_set(v___f_3393_, 2, v_toPure_3388_);
lean_closure_set(v___f_3393_, 3, v_toBind_3387_);
lean_closure_set(v___f_3393_, 4, v_inst_3379_);
lean_closure_set(v___f_3393_, 5, v_inst_3383_);
lean_closure_set(v___f_3393_, 6, v_inst_3382_);
lean_closure_set(v___f_3393_, 7, v_inst_3384_);
lean_closure_set(v___f_3393_, 8, v_f_3385_);
v___f_3394_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3394_, 0, v_toPure_3388_);
lean_closure_set(v___f_3394_, 1, v_toBind_3387_);
lean_closure_set(v___f_3394_, 2, v___f_3389_);
lean_closure_set(v___f_3394_, 3, v_inst_3379_);
lean_closure_set(v___f_3394_, 4, v___f_3393_);
lean_closure_set(v___f_3394_, 5, v_inst_3384_);
lean_closure_set(v___f_3394_, 6, v___f_3390_);
v___x_3395_ = lean_apply_4(v_toBind_3387_, lean_box(0), lean_box(0), v___x_3392_, v___f_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3396_, lean_object* v_____r_3397_){
_start:
{
uint8_t v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = 0;
v___x_3399_ = lean_box(v___x_3398_);
v___x_3400_ = lean_apply_2(v_toPure_3396_, lean_box(0), v___x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_snd_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; lean_object* v_caches_3415_; lean_object* v_typeAnalysis_3416_; lean_object* v_target_3417_; uint8_t v_didChange_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3428_; 
v___x_3414_ = lean_st_ref_take(v___y_3403_);
v_caches_3415_ = lean_ctor_get(v___x_3414_, 0);
v_typeAnalysis_3416_ = lean_ctor_get(v___x_3414_, 1);
v_target_3417_ = lean_ctor_get(v___x_3414_, 2);
v_didChange_3418_ = lean_ctor_get_uint8(v___x_3414_, sizeof(void*)*4);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3428_ == 0)
{
lean_object* v_unused_3429_; 
v_unused_3429_ = lean_ctor_get(v___x_3414_, 3);
lean_dec(v_unused_3429_);
v___x_3420_ = v___x_3414_;
v_isShared_3421_ = v_isSharedCheck_3428_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_target_3417_);
lean_inc(v_typeAnalysis_3416_);
lean_inc(v_caches_3415_);
lean_dec(v___x_3414_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3428_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3422_ = lean_box(0);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 3, v_snd_3401_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_caches_3415_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_typeAnalysis_3416_);
lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_target_3417_);
lean_ctor_set(v_reuseFailAlloc_3427_, 3, v_snd_3401_);
lean_ctor_set_uint8(v_reuseFailAlloc_3427_, sizeof(void*)*4, v_didChange_3418_);
v___x_3424_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = lean_st_ref_put(v___y_3403_, v___x_3424_);
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3422_);
return v___x_3426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed(lean_object* v_snd_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(v_snd_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_inst_3444_, lean_object* v_toBind_3445_, lean_object* v___f_3446_, lean_object* v_toPure_3447_, lean_object* v_____s_3448_){
_start:
{
lean_object* v_fst_3449_; 
v_fst_3449_ = lean_ctor_get(v_____s_3448_, 0);
if (lean_obj_tag(v_fst_3449_) == 0)
{
lean_object* v_snd_3450_; lean_object* v___f_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec(v_toPure_3447_);
v_snd_3450_ = lean_ctor_get(v_____s_3448_, 1);
lean_inc(v_snd_3450_);
lean_dec_ref(v_____s_3448_);
v___f_3451_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_3451_, 0, v_snd_3450_);
v___x_3452_ = lean_apply_2(v_inst_3444_, lean_box(0), v___f_3451_);
v___x_3453_ = lean_apply_4(v_toBind_3445_, lean_box(0), lean_box(0), v___x_3452_, v___f_3446_);
return v___x_3453_;
}
else
{
lean_object* v_val_3454_; lean_object* v___x_3455_; 
lean_inc_ref(v_fst_3449_);
lean_dec_ref(v_____s_3448_);
lean_dec(v___f_3446_);
lean_dec(v_toBind_3445_);
lean_dec(v_inst_3444_);
v_val_3454_ = lean_ctor_get(v_fst_3449_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v_fst_3449_, 1);
v___x_3455_ = lean_apply_2(v_toPure_3447_, lean_box(0), v_val_3454_);
return v___x_3455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_toPure_3456_, lean_object* v_____do__lift_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_apply_2(v_toPure_3456_, lean_box(0), v_____do__lift_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3459_, lean_object* v_next_3460_, lean_object* v_G_3461_, lean_object* v_____do__lift_3462_){
_start:
{
if (lean_obj_tag(v_____do__lift_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3464_; 
lean_dec(v_G_3461_);
v_a_3463_ = lean_ctor_get(v_____do__lift_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref_known(v_____do__lift_3462_, 1);
v___x_3464_ = lean_apply_2(v_toPure_3459_, lean_box(0), v_a_3463_);
return v___x_3464_;
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
lean_dec(v_toPure_3459_);
v_a_3465_ = lean_ctor_get(v_____do__lift_3462_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v_____do__lift_3462_, 1);
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = lean_nat_add(v_next_3460_, v___x_3466_);
v___x_3468_ = lean_apply_4(v_G_3461_, v___x_3467_, v_a_3465_, lean_box(0), lean_box(0));
return v___x_3468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3469_, lean_object* v_next_3470_, lean_object* v_G_3471_, lean_object* v_____do__lift_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3469_, v_next_3470_, v_G_3471_, v_____do__lift_3472_);
lean_dec(v_next_3470_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(uint8_t v___x_3474_, lean_object* v_snd_3475_, lean_object* v_toPure_3476_, lean_object* v_____r_3477_){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3478_ = lean_box(v___x_3474_);
v___x_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
v___x_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v_snd_3475_);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
v___x_3482_ = lean_apply_2(v_toPure_3476_, lean_box(0), v___x_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed(lean_object* v___x_3483_, lean_object* v_snd_3484_, lean_object* v_toPure_3485_, lean_object* v_____r_3486_){
_start:
{
uint8_t v___x_1675__boxed_3487_; lean_object* v_res_3488_; 
v___x_1675__boxed_3487_ = lean_unbox(v___x_3483_);
v_res_3488_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_1675__boxed_3487_, v_snd_3484_, v_toPure_3485_, v_____r_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_snd_3489_, lean_object* v_newHyp_3490_, lean_object* v___x_3491_, lean_object* v_toPure_3492_, lean_object* v_____r_3493_){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3494_ = lean_array_push(v_snd_3489_, v_newHyp_3490_);
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3491_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
v___x_3497_ = lean_apply_2(v_toPure_3492_, lean_box(0), v___x_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_toPure_3498_, lean_object* v___x_3499_, lean_object* v_____do__lift_3500_, lean_object* v_____do__lift_3501_){
_start:
{
uint8_t v_hasTrace_3502_; 
v_hasTrace_3502_ = lean_ctor_get_uint8(v_____do__lift_3501_, sizeof(void*)*1);
if (v_hasTrace_3502_ == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
lean_dec(v___x_3499_);
v___x_3503_ = lean_box(v_hasTrace_3502_);
v___x_3504_ = lean_apply_2(v_toPure_3498_, lean_box(0), v___x_3503_);
return v___x_3504_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3505_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3506_ = l_Lean_Name_append(v___x_3505_, v___x_3499_);
v___x_3507_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3500_, v_____do__lift_3501_, v___x_3506_);
lean_dec(v___x_3506_);
v___x_3508_ = lean_box(v___x_3507_);
v___x_3509_ = lean_apply_2(v_toPure_3498_, lean_box(0), v___x_3508_);
return v___x_3509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed(lean_object* v_toPure_3510_, lean_object* v___x_3511_, lean_object* v_____do__lift_3512_, lean_object* v_____do__lift_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(v_toPure_3510_, v___x_3511_, v_____do__lift_3512_, v_____do__lift_3513_);
lean_dec_ref(v_____do__lift_3513_);
lean_dec_ref(v_____do__lift_3512_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v_inst_3515_, lean_object* v_toPure_3516_, lean_object* v___x_3517_, lean_object* v_toBind_3518_, lean_object* v_____do__lift_3519_){
_start:
{
lean_object* v_getOptionsUnrestricted_3520_; lean_object* v___f_3521_; lean_object* v___x_3522_; 
v_getOptionsUnrestricted_3520_ = lean_ctor_get(v_inst_3515_, 1);
lean_inc(v_getOptionsUnrestricted_3520_);
lean_dec_ref(v_inst_3515_);
v___f_3521_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_3521_, 0, v_toPure_3516_);
lean_closure_set(v___f_3521_, 1, v___x_3517_);
lean_closure_set(v___f_3521_, 2, v_____do__lift_3519_);
v___x_3522_ = lean_apply_4(v_toBind_3518_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3520_, v___f_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object* v___f_3523_, lean_object* v___x_3524_, lean_object* v_type_3525_, lean_object* v_inst_3526_, lean_object* v_inst_3527_, lean_object* v_toMonadRef_3528_, lean_object* v_inst_3529_, lean_object* v___x_3530_, lean_object* v_toBind_3531_, lean_object* v___f_3532_, uint8_t v_____do__lift_3533_){
_start:
{
if (v_____do__lift_3533_ == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec(v___f_3532_);
lean_dec(v_toBind_3531_);
lean_dec(v___x_3530_);
lean_dec(v_inst_3529_);
lean_dec_ref(v_toMonadRef_3528_);
lean_dec_ref(v_inst_3527_);
lean_dec_ref(v_inst_3526_);
lean_dec_ref(v_type_3525_);
lean_dec_ref(v___x_3524_);
v___x_3534_ = lean_box(0);
v___x_3535_ = lean_apply_1(v___f_3523_, v___x_3534_);
return v___x_3535_;
}
else
{
lean_object* v_type_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_dec(v___f_3523_);
v_type_3536_ = lean_ctor_get(v___x_3524_, 1);
lean_inc_ref(v_type_3536_);
lean_dec_ref(v___x_3524_);
v___x_3537_ = l_Lean_MessageData_ofExpr(v_type_3536_);
v___x_3538_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3537_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = l_Lean_MessageData_ofExpr(v_type_3525_);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = l_Lean_addTrace___redArg(v_inst_3526_, v_inst_3527_, v_toMonadRef_3528_, v_inst_3529_, v___x_3530_, v___x_3541_);
v___x_3543_ = lean_apply_4(v_toBind_3531_, lean_box(0), lean_box(0), v___x_3542_, v___f_3532_);
return v___x_3543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___f_3544_, lean_object* v___x_3545_, lean_object* v_type_3546_, lean_object* v_inst_3547_, lean_object* v_inst_3548_, lean_object* v_toMonadRef_3549_, lean_object* v_inst_3550_, lean_object* v___x_3551_, lean_object* v_toBind_3552_, lean_object* v___f_3553_, lean_object* v_____do__lift_3554_){
_start:
{
uint8_t v_____do__lift_1750__boxed_3555_; lean_object* v_res_3556_; 
v_____do__lift_1750__boxed_3555_ = lean_unbox(v_____do__lift_3554_);
v_res_3556_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3544_, v___x_3545_, v_type_3546_, v_inst_3547_, v_inst_3548_, v_toMonadRef_3549_, v_inst_3550_, v___x_3551_, v_toBind_3552_, v___f_3553_, v_____do__lift_1750__boxed_3555_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v___x_3557_, lean_object* v_snd_3558_, lean_object* v___x_3559_, lean_object* v_toPure_3560_, lean_object* v_inst_3561_, lean_object* v_toBind_3562_, lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_toMonadRef_3566_, lean_object* v_inst_3567_, lean_object* v___f_3568_, lean_object* v_newHyp_3569_){
_start:
{
lean_object* v_type_3570_; lean_object* v_value_3571_; uint8_t v___x_3572_; 
v_type_3570_ = lean_ctor_get(v_newHyp_3569_, 1);
v_value_3571_ = lean_ctor_get(v_newHyp_3569_, 2);
lean_inc_ref(v_type_3570_);
v___x_3572_ = l_Lean_Expr_isFalse(v_type_3570_);
if (v___x_3572_ == 0)
{
lean_object* v_type_3573_; lean_object* v___f_3574_; lean_object* v___f_3575_; lean_object* v___f_3576_; lean_object* v___f_3577_; uint8_t v___x_3585_; 
lean_dec(v___f_3568_);
v_type_3573_ = lean_ctor_get(v___x_3557_, 1);
lean_inc(v_toPure_3560_);
lean_inc(v___x_3559_);
lean_inc_ref(v_newHyp_3569_);
lean_inc(v_snd_3558_);
v___f_3574_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3574_, 0, v_snd_3558_);
lean_closure_set(v___f_3574_, 1, v_newHyp_3569_);
lean_closure_set(v___f_3574_, 2, v___x_3559_);
lean_closure_set(v___f_3574_, 3, v_toPure_3560_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3575_, 0, v___f_3574_);
lean_inc(v_toBind_3562_);
v___f_3576_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3576_, 0, v_inst_3561_);
lean_closure_set(v___f_3576_, 1, v_toBind_3562_);
lean_closure_set(v___f_3576_, 2, v___f_3575_);
lean_inc_ref(v___f_3576_);
v___f_3577_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3577_, 0, v___f_3576_);
v___x_3585_ = lean_expr_eqv(v_type_3573_, v_type_3570_);
if (v___x_3585_ == 0)
{
lean_inc_ref(v_type_3570_);
lean_dec_ref(v_newHyp_3569_);
lean_dec(v___x_3559_);
lean_dec(v_snd_3558_);
goto v___jp_3578_;
}
else
{
if (v___x_3572_ == 0)
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_dec_ref(v___f_3577_);
lean_dec_ref(v___f_3576_);
lean_dec(v_inst_3567_);
lean_dec_ref(v_toMonadRef_3566_);
lean_dec_ref(v_inst_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec_ref(v_inst_3563_);
lean_dec(v_toBind_3562_);
lean_dec_ref(v___x_3557_);
v___x_3586_ = lean_box(0);
v___x_3587_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3558_, v_newHyp_3569_, v___x_3559_, v_toPure_3560_, v___x_3586_);
return v___x_3587_;
}
else
{
lean_inc_ref(v_type_3570_);
lean_dec_ref(v_newHyp_3569_);
lean_dec(v___x_3559_);
lean_dec(v_snd_3558_);
goto v___jp_3578_;
}
}
v___jp_3578_:
{
lean_object* v_getInheritedTraceOptions_3579_; lean_object* v___x_3580_; lean_object* v___f_3581_; lean_object* v___f_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_getInheritedTraceOptions_3579_ = lean_ctor_get(v_inst_3563_, 2);
lean_inc(v_getInheritedTraceOptions_3579_);
v___x_3580_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3562_, 3);
v___f_3581_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3581_, 0, v_inst_3564_);
lean_closure_set(v___f_3581_, 1, v_toPure_3560_);
lean_closure_set(v___f_3581_, 2, v___x_3580_);
lean_closure_set(v___f_3581_, 3, v_toBind_3562_);
v___f_3582_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3582_, 0, v___f_3576_);
lean_closure_set(v___f_3582_, 1, v___x_3557_);
lean_closure_set(v___f_3582_, 2, v_type_3570_);
lean_closure_set(v___f_3582_, 3, v_inst_3565_);
lean_closure_set(v___f_3582_, 4, v_inst_3563_);
lean_closure_set(v___f_3582_, 5, v_toMonadRef_3566_);
lean_closure_set(v___f_3582_, 6, v_inst_3567_);
lean_closure_set(v___f_3582_, 7, v___x_3580_);
lean_closure_set(v___f_3582_, 8, v_toBind_3562_);
lean_closure_set(v___f_3582_, 9, v___f_3577_);
v___x_3583_ = lean_apply_4(v_toBind_3562_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3579_, v___f_3581_);
v___x_3584_ = lean_apply_4(v_toBind_3562_, lean_box(0), lean_box(0), v___x_3583_, v___f_3582_);
return v___x_3584_;
}
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_inc_ref(v_value_3571_);
lean_dec_ref(v_newHyp_3569_);
lean_dec(v_inst_3567_);
lean_dec_ref(v_toMonadRef_3566_);
lean_dec_ref(v_inst_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec_ref(v_inst_3563_);
lean_dec(v_toPure_3560_);
lean_dec(v___x_3559_);
lean_dec(v_snd_3558_);
lean_dec_ref(v___x_3557_);
v___x_3588_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3588_, 0, v_value_3571_);
v___x_3589_ = lean_apply_2(v_inst_3561_, lean_box(0), v___x_3588_);
v___x_3590_ = lean_apply_4(v_toBind_3562_, lean_box(0), lean_box(0), v___x_3589_, v___f_3568_);
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3591_, lean_object* v_toPure_3592_, lean_object* v_hyps_3593_, lean_object* v___x_3594_, lean_object* v_inst_3595_, lean_object* v_toBind_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_toMonadRef_3600_, lean_object* v_inst_3601_, lean_object* v_f_3602_, lean_object* v___f_3603_, lean_object* v_next_3604_, lean_object* v_acc_3605_, lean_object* v_h_3606_, lean_object* v_G_3607_){
_start:
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_nat_dec_lt(v_next_3604_, v___x_3591_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; 
lean_dec(v_G_3607_);
lean_dec(v_next_3604_);
lean_dec(v___f_3603_);
lean_dec(v_f_3602_);
lean_dec(v_inst_3601_);
lean_dec_ref(v_toMonadRef_3600_);
lean_dec_ref(v_inst_3599_);
lean_dec_ref(v_inst_3598_);
lean_dec_ref(v_inst_3597_);
lean_dec(v_toBind_3596_);
lean_dec(v_inst_3595_);
lean_dec(v___x_3594_);
v___x_3609_ = lean_apply_2(v_toPure_3592_, lean_box(0), v_acc_3605_);
return v___x_3609_;
}
else
{
lean_object* v_snd_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; lean_object* v___f_3613_; lean_object* v___x_3614_; lean_object* v___f_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v_snd_3610_ = lean_ctor_get(v_acc_3605_, 1);
lean_inc_n(v_snd_3610_, 2);
lean_dec_ref(v_acc_3605_);
lean_inc(v_next_3604_);
lean_inc_n(v_toPure_3592_, 2);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3611_, 0, v_toPure_3592_);
lean_closure_set(v___f_3611_, 1, v_next_3604_);
lean_closure_set(v___f_3611_, 2, v_G_3607_);
v___x_3612_ = lean_box(v___x_3608_);
v___f_3613_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3613_, 0, v___x_3612_);
lean_closure_set(v___f_3613_, 1, v_snd_3610_);
lean_closure_set(v___f_3613_, 2, v_toPure_3592_);
v___x_3614_ = lean_array_fget_borrowed(v_hyps_3593_, v_next_3604_);
lean_inc_n(v_toBind_3596_, 3);
lean_inc_n(v___x_3614_, 2);
v___f_3615_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9), 13, 12);
lean_closure_set(v___f_3615_, 0, v___x_3614_);
lean_closure_set(v___f_3615_, 1, v_snd_3610_);
lean_closure_set(v___f_3615_, 2, v___x_3594_);
lean_closure_set(v___f_3615_, 3, v_toPure_3592_);
lean_closure_set(v___f_3615_, 4, v_inst_3595_);
lean_closure_set(v___f_3615_, 5, v_toBind_3596_);
lean_closure_set(v___f_3615_, 6, v_inst_3597_);
lean_closure_set(v___f_3615_, 7, v_inst_3598_);
lean_closure_set(v___f_3615_, 8, v_inst_3599_);
lean_closure_set(v___f_3615_, 9, v_toMonadRef_3600_);
lean_closure_set(v___f_3615_, 10, v_inst_3601_);
lean_closure_set(v___f_3615_, 11, v___f_3613_);
v___x_3616_ = lean_apply_2(v_f_3602_, v_next_3604_, v___x_3614_);
v___x_3617_ = lean_apply_4(v_toBind_3596_, lean_box(0), lean_box(0), v___x_3616_, v___f_3615_);
v___x_3618_ = lean_apply_4(v_toBind_3596_, lean_box(0), lean_box(0), v___x_3617_, v___f_3603_);
v___x_3619_ = lean_apply_4(v_toBind_3596_, lean_box(0), lean_box(0), v___x_3618_, v___f_3611_);
return v___x_3619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3620_ = _args[0];
lean_object* v_toPure_3621_ = _args[1];
lean_object* v_hyps_3622_ = _args[2];
lean_object* v___x_3623_ = _args[3];
lean_object* v_inst_3624_ = _args[4];
lean_object* v_toBind_3625_ = _args[5];
lean_object* v_inst_3626_ = _args[6];
lean_object* v_inst_3627_ = _args[7];
lean_object* v_inst_3628_ = _args[8];
lean_object* v_toMonadRef_3629_ = _args[9];
lean_object* v_inst_3630_ = _args[10];
lean_object* v_f_3631_ = _args[11];
lean_object* v___f_3632_ = _args[12];
lean_object* v_next_3633_ = _args[13];
lean_object* v_acc_3634_ = _args[14];
lean_object* v_h_3635_ = _args[15];
lean_object* v_G_3636_ = _args[16];
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3620_, v_toPure_3621_, v_hyps_3622_, v___x_3623_, v_inst_3624_, v_toBind_3625_, v_inst_3626_, v_inst_3627_, v_inst_3628_, v_toMonadRef_3629_, v_inst_3630_, v_f_3631_, v___f_3632_, v_next_3633_, v_acc_3634_, v_h_3635_, v_G_3636_);
lean_dec_ref(v_hyps_3622_);
lean_dec(v___x_3620_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3638_, lean_object* v_inst_3639_, lean_object* v_toBind_3640_, lean_object* v_inst_3641_, lean_object* v_inst_3642_, lean_object* v_inst_3643_, lean_object* v_toMonadRef_3644_, lean_object* v_inst_3645_, lean_object* v_f_3646_, lean_object* v___f_3647_, lean_object* v___f_3648_, lean_object* v_hyps_3649_){
_start:
{
lean_object* v___x_3650_; lean_object* v_newHyps_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___f_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3650_ = lean_array_get_size(v_hyps_3649_);
v_newHyps_3651_ = lean_mk_empty_array_with_capacity(v___x_3650_);
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_box(0);
lean_inc(v_toBind_3640_);
v___f_3654_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3654_, 0, v___x_3650_);
lean_closure_set(v___f_3654_, 1, v_toPure_3638_);
lean_closure_set(v___f_3654_, 2, v_hyps_3649_);
lean_closure_set(v___f_3654_, 3, v___x_3653_);
lean_closure_set(v___f_3654_, 4, v_inst_3639_);
lean_closure_set(v___f_3654_, 5, v_toBind_3640_);
lean_closure_set(v___f_3654_, 6, v_inst_3641_);
lean_closure_set(v___f_3654_, 7, v_inst_3642_);
lean_closure_set(v___f_3654_, 8, v_inst_3643_);
lean_closure_set(v___f_3654_, 9, v_toMonadRef_3644_);
lean_closure_set(v___f_3654_, 10, v_inst_3645_);
lean_closure_set(v___f_3654_, 11, v_f_3646_);
lean_closure_set(v___f_3654_, 12, v___f_3647_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v_newHyps_3651_);
v___x_3656_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3654_, v___x_3652_, v___x_3655_, lean_box(0));
v___x_3657_ = lean_apply_4(v_toBind_3640_, lean_box(0), lean_box(0), v___x_3656_, v___f_3648_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3658_, lean_object* v_inst_3659_, lean_object* v_inst_3660_, lean_object* v_inst_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_f_3664_){
_start:
{
lean_object* v_toApplicative_3665_; lean_object* v_toBind_3666_; lean_object* v_toPure_3667_; lean_object* v_toMonadRef_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___f_3671_; lean_object* v___f_3672_; lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___x_3675_; 
v_toApplicative_3665_ = lean_ctor_get(v_inst_3658_, 0);
v_toBind_3666_ = lean_ctor_get(v_inst_3658_, 1);
lean_inc_n(v_toBind_3666_, 3);
v_toPure_3667_ = lean_ctor_get(v_toApplicative_3665_, 1);
lean_inc_n(v_toPure_3667_, 4);
v_toMonadRef_3668_ = lean_ctor_get(v_inst_3660_, 1);
lean_inc_ref(v_toMonadRef_3668_);
lean_dec_ref(v_inst_3660_);
v___x_3669_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3659_, 2);
v___x_3670_ = lean_apply_2(v_inst_3659_, lean_box(0), v___x_3669_);
v___f_3671_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3671_, 0, v_toPure_3667_);
v___f_3672_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3672_, 0, v_inst_3659_);
lean_closure_set(v___f_3672_, 1, v_toBind_3666_);
lean_closure_set(v___f_3672_, 2, v___f_3671_);
lean_closure_set(v___f_3672_, 3, v_toPure_3667_);
v___f_3673_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3673_, 0, v_toPure_3667_);
v___f_3674_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3674_, 0, v_toPure_3667_);
lean_closure_set(v___f_3674_, 1, v_inst_3659_);
lean_closure_set(v___f_3674_, 2, v_toBind_3666_);
lean_closure_set(v___f_3674_, 3, v_inst_3661_);
lean_closure_set(v___f_3674_, 4, v_inst_3662_);
lean_closure_set(v___f_3674_, 5, v_inst_3658_);
lean_closure_set(v___f_3674_, 6, v_toMonadRef_3668_);
lean_closure_set(v___f_3674_, 7, v_inst_3663_);
lean_closure_set(v___f_3674_, 8, v_f_3664_);
lean_closure_set(v___f_3674_, 9, v___f_3673_);
lean_closure_set(v___f_3674_, 10, v___f_3672_);
v___x_3675_ = lean_apply_4(v_toBind_3666_, lean_box(0), lean_box(0), v___x_3670_, v___f_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3676_, lean_object* v_inst_3677_, lean_object* v_inst_3678_, lean_object* v_inst_3679_, lean_object* v_inst_3680_, lean_object* v_inst_3681_, lean_object* v_inst_3682_, lean_object* v_inst_3683_, lean_object* v_inst_3684_, lean_object* v_f_3685_){
_start:
{
lean_object* v_toApplicative_3686_; lean_object* v_toBind_3687_; lean_object* v_toPure_3688_; lean_object* v_toMonadRef_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___f_3695_; lean_object* v___x_3696_; 
v_toApplicative_3686_ = lean_ctor_get(v_inst_3677_, 0);
v_toBind_3687_ = lean_ctor_get(v_inst_3677_, 1);
lean_inc_n(v_toBind_3687_, 3);
v_toPure_3688_ = lean_ctor_get(v_toApplicative_3686_, 1);
lean_inc_n(v_toPure_3688_, 4);
v_toMonadRef_3689_ = lean_ctor_get(v_inst_3679_, 1);
lean_inc_ref(v_toMonadRef_3689_);
lean_dec_ref(v_inst_3679_);
v___x_3690_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3678_, 2);
v___x_3691_ = lean_apply_2(v_inst_3678_, lean_box(0), v___x_3690_);
v___f_3692_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3692_, 0, v_toPure_3688_);
v___f_3693_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3693_, 0, v_inst_3678_);
lean_closure_set(v___f_3693_, 1, v_toBind_3687_);
lean_closure_set(v___f_3693_, 2, v___f_3692_);
lean_closure_set(v___f_3693_, 3, v_toPure_3688_);
v___f_3694_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3694_, 0, v_toPure_3688_);
v___f_3695_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3695_, 0, v_toPure_3688_);
lean_closure_set(v___f_3695_, 1, v_inst_3678_);
lean_closure_set(v___f_3695_, 2, v_toBind_3687_);
lean_closure_set(v___f_3695_, 3, v_inst_3681_);
lean_closure_set(v___f_3695_, 4, v_inst_3682_);
lean_closure_set(v___f_3695_, 5, v_inst_3677_);
lean_closure_set(v___f_3695_, 6, v_toMonadRef_3689_);
lean_closure_set(v___f_3695_, 7, v_inst_3683_);
lean_closure_set(v___f_3695_, 8, v_f_3685_);
lean_closure_set(v___f_3695_, 9, v___f_3694_);
lean_closure_set(v___f_3695_, 10, v___f_3693_);
v___x_3696_ = lean_apply_4(v_toBind_3687_, lean_box(0), lean_box(0), v___x_3691_, v___f_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3697_, lean_object* v_inst_3698_, lean_object* v_inst_3699_, lean_object* v_inst_3700_, lean_object* v_inst_3701_, lean_object* v_inst_3702_, lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_inst_3705_, lean_object* v_f_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3697_, v_inst_3698_, v_inst_3699_, v_inst_3700_, v_inst_3701_, v_inst_3702_, v_inst_3703_, v_inst_3704_, v_inst_3705_, v_f_3706_);
lean_dec_ref(v_inst_3705_);
lean_dec_ref(v_inst_3701_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3708_, lean_object* v_snd_3709_, lean_object* v___x_3710_, lean_object* v_toPure_3711_, lean_object* v_inst_3712_, lean_object* v_toBind_3713_, lean_object* v_inst_3714_, lean_object* v_inst_3715_, lean_object* v_toMonadRef_3716_, lean_object* v_inst_3717_, lean_object* v_inst_3718_, lean_object* v___f_3719_, lean_object* v_newHyp_3720_){
_start:
{
lean_object* v_type_3721_; lean_object* v_value_3722_; uint8_t v___x_3723_; 
v_type_3721_ = lean_ctor_get(v_newHyp_3720_, 1);
v_value_3722_ = lean_ctor_get(v_newHyp_3720_, 2);
lean_inc_ref(v_type_3721_);
v___x_3723_ = l_Lean_Expr_isFalse(v_type_3721_);
if (v___x_3723_ == 0)
{
lean_object* v_type_3724_; lean_object* v___f_3725_; lean_object* v___f_3726_; lean_object* v___f_3727_; lean_object* v___f_3728_; uint8_t v___x_3736_; 
lean_dec(v___f_3719_);
v_type_3724_ = lean_ctor_get(v___x_3708_, 1);
lean_inc(v_toPure_3711_);
lean_inc(v___x_3710_);
lean_inc_ref(v_newHyp_3720_);
lean_inc(v_snd_3709_);
v___f_3725_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3725_, 0, v_snd_3709_);
lean_closure_set(v___f_3725_, 1, v_newHyp_3720_);
lean_closure_set(v___f_3725_, 2, v___x_3710_);
lean_closure_set(v___f_3725_, 3, v_toPure_3711_);
v___f_3726_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3726_, 0, v___f_3725_);
lean_inc(v_toBind_3713_);
v___f_3727_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3727_, 0, v_inst_3712_);
lean_closure_set(v___f_3727_, 1, v_toBind_3713_);
lean_closure_set(v___f_3727_, 2, v___f_3726_);
lean_inc_ref(v___f_3727_);
v___f_3728_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3728_, 0, v___f_3727_);
v___x_3736_ = lean_expr_eqv(v_type_3724_, v_type_3721_);
if (v___x_3736_ == 0)
{
lean_inc_ref(v_type_3721_);
lean_dec_ref(v_newHyp_3720_);
lean_dec(v___x_3710_);
lean_dec(v_snd_3709_);
goto v___jp_3729_;
}
else
{
if (v___x_3723_ == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_dec_ref(v___f_3728_);
lean_dec_ref(v___f_3727_);
lean_dec_ref(v_inst_3718_);
lean_dec(v_inst_3717_);
lean_dec_ref(v_toMonadRef_3716_);
lean_dec_ref(v_inst_3715_);
lean_dec_ref(v_inst_3714_);
lean_dec(v_toBind_3713_);
lean_dec_ref(v___x_3708_);
v___x_3737_ = lean_box(0);
v___x_3738_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3709_, v_newHyp_3720_, v___x_3710_, v_toPure_3711_, v___x_3737_);
return v___x_3738_;
}
else
{
lean_inc_ref(v_type_3721_);
lean_dec_ref(v_newHyp_3720_);
lean_dec(v___x_3710_);
lean_dec(v_snd_3709_);
goto v___jp_3729_;
}
}
v___jp_3729_:
{
lean_object* v_getInheritedTraceOptions_3730_; lean_object* v___x_3731_; lean_object* v___f_3732_; lean_object* v___f_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v_getInheritedTraceOptions_3730_ = lean_ctor_get(v_inst_3714_, 2);
lean_inc(v_getInheritedTraceOptions_3730_);
v___x_3731_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3713_, 3);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3732_, 0, v___f_3727_);
lean_closure_set(v___f_3732_, 1, v___x_3708_);
lean_closure_set(v___f_3732_, 2, v_type_3721_);
lean_closure_set(v___f_3732_, 3, v_inst_3715_);
lean_closure_set(v___f_3732_, 4, v_inst_3714_);
lean_closure_set(v___f_3732_, 5, v_toMonadRef_3716_);
lean_closure_set(v___f_3732_, 6, v_inst_3717_);
lean_closure_set(v___f_3732_, 7, v___x_3731_);
lean_closure_set(v___f_3732_, 8, v_toBind_3713_);
lean_closure_set(v___f_3732_, 9, v___f_3728_);
v___f_3733_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3733_, 0, v_inst_3718_);
lean_closure_set(v___f_3733_, 1, v_toPure_3711_);
lean_closure_set(v___f_3733_, 2, v___x_3731_);
lean_closure_set(v___f_3733_, 3, v_toBind_3713_);
v___x_3734_ = lean_apply_4(v_toBind_3713_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3730_, v___f_3733_);
v___x_3735_ = lean_apply_4(v_toBind_3713_, lean_box(0), lean_box(0), v___x_3734_, v___f_3732_);
return v___x_3735_;
}
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_inc_ref(v_value_3722_);
lean_dec_ref(v_newHyp_3720_);
lean_dec_ref(v_inst_3718_);
lean_dec(v_inst_3717_);
lean_dec_ref(v_toMonadRef_3716_);
lean_dec_ref(v_inst_3715_);
lean_dec_ref(v_inst_3714_);
lean_dec(v_toPure_3711_);
lean_dec(v___x_3710_);
lean_dec(v_snd_3709_);
lean_dec_ref(v___x_3708_);
v___x_3739_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3739_, 0, v_value_3722_);
v___x_3740_ = lean_apply_2(v_inst_3712_, lean_box(0), v___x_3739_);
v___x_3741_ = lean_apply_4(v_toBind_3713_, lean_box(0), lean_box(0), v___x_3740_, v___f_3719_);
return v___x_3741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3742_, lean_object* v_toPure_3743_, lean_object* v_hyps_3744_, lean_object* v___x_3745_, lean_object* v_inst_3746_, lean_object* v_toBind_3747_, lean_object* v_inst_3748_, lean_object* v_inst_3749_, lean_object* v_toMonadRef_3750_, lean_object* v_inst_3751_, lean_object* v_inst_3752_, lean_object* v_f_3753_, lean_object* v___f_3754_, lean_object* v_next_3755_, lean_object* v_acc_3756_, lean_object* v_h_3757_, lean_object* v_G_3758_){
_start:
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_nat_dec_lt(v_next_3755_, v___x_3742_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; 
lean_dec(v_G_3758_);
lean_dec(v_next_3755_);
lean_dec(v___f_3754_);
lean_dec(v_f_3753_);
lean_dec_ref(v_inst_3752_);
lean_dec(v_inst_3751_);
lean_dec_ref(v_toMonadRef_3750_);
lean_dec_ref(v_inst_3749_);
lean_dec_ref(v_inst_3748_);
lean_dec(v_toBind_3747_);
lean_dec(v_inst_3746_);
lean_dec(v___x_3745_);
v___x_3760_ = lean_apply_2(v_toPure_3743_, lean_box(0), v_acc_3756_);
return v___x_3760_;
}
else
{
lean_object* v_snd_3761_; lean_object* v___f_3762_; lean_object* v___x_3763_; lean_object* v___f_3764_; lean_object* v___x_3765_; lean_object* v___f_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_snd_3761_ = lean_ctor_get(v_acc_3756_, 1);
lean_inc_n(v_snd_3761_, 2);
lean_dec_ref(v_acc_3756_);
lean_inc(v_next_3755_);
lean_inc_n(v_toPure_3743_, 2);
v___f_3762_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3762_, 0, v_toPure_3743_);
lean_closure_set(v___f_3762_, 1, v_next_3755_);
lean_closure_set(v___f_3762_, 2, v_G_3758_);
v___x_3763_ = lean_box(v___x_3759_);
v___f_3764_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3764_, 0, v___x_3763_);
lean_closure_set(v___f_3764_, 1, v_snd_3761_);
lean_closure_set(v___f_3764_, 2, v_toPure_3743_);
v___x_3765_ = lean_array_fget_borrowed(v_hyps_3744_, v_next_3755_);
lean_dec(v_next_3755_);
lean_inc_n(v_toBind_3747_, 3);
lean_inc_n(v___x_3765_, 2);
v___f_3766_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3766_, 0, v___x_3765_);
lean_closure_set(v___f_3766_, 1, v_snd_3761_);
lean_closure_set(v___f_3766_, 2, v___x_3745_);
lean_closure_set(v___f_3766_, 3, v_toPure_3743_);
lean_closure_set(v___f_3766_, 4, v_inst_3746_);
lean_closure_set(v___f_3766_, 5, v_toBind_3747_);
lean_closure_set(v___f_3766_, 6, v_inst_3748_);
lean_closure_set(v___f_3766_, 7, v_inst_3749_);
lean_closure_set(v___f_3766_, 8, v_toMonadRef_3750_);
lean_closure_set(v___f_3766_, 9, v_inst_3751_);
lean_closure_set(v___f_3766_, 10, v_inst_3752_);
lean_closure_set(v___f_3766_, 11, v___f_3764_);
v___x_3767_ = lean_apply_1(v_f_3753_, v___x_3765_);
v___x_3768_ = lean_apply_4(v_toBind_3747_, lean_box(0), lean_box(0), v___x_3767_, v___f_3766_);
v___x_3769_ = lean_apply_4(v_toBind_3747_, lean_box(0), lean_box(0), v___x_3768_, v___f_3754_);
v___x_3770_ = lean_apply_4(v_toBind_3747_, lean_box(0), lean_box(0), v___x_3769_, v___f_3762_);
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3771_ = _args[0];
lean_object* v_toPure_3772_ = _args[1];
lean_object* v_hyps_3773_ = _args[2];
lean_object* v___x_3774_ = _args[3];
lean_object* v_inst_3775_ = _args[4];
lean_object* v_toBind_3776_ = _args[5];
lean_object* v_inst_3777_ = _args[6];
lean_object* v_inst_3778_ = _args[7];
lean_object* v_toMonadRef_3779_ = _args[8];
lean_object* v_inst_3780_ = _args[9];
lean_object* v_inst_3781_ = _args[10];
lean_object* v_f_3782_ = _args[11];
lean_object* v___f_3783_ = _args[12];
lean_object* v_next_3784_ = _args[13];
lean_object* v_acc_3785_ = _args[14];
lean_object* v_h_3786_ = _args[15];
lean_object* v_G_3787_ = _args[16];
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3771_, v_toPure_3772_, v_hyps_3773_, v___x_3774_, v_inst_3775_, v_toBind_3776_, v_inst_3777_, v_inst_3778_, v_toMonadRef_3779_, v_inst_3780_, v_inst_3781_, v_f_3782_, v___f_3783_, v_next_3784_, v_acc_3785_, v_h_3786_, v_G_3787_);
lean_dec_ref(v_hyps_3773_);
lean_dec(v___x_3771_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3789_, lean_object* v_inst_3790_, lean_object* v_toBind_3791_, lean_object* v_inst_3792_, lean_object* v_inst_3793_, lean_object* v_toMonadRef_3794_, lean_object* v_inst_3795_, lean_object* v_inst_3796_, lean_object* v_f_3797_, lean_object* v___f_3798_, lean_object* v___f_3799_, lean_object* v_hyps_3800_){
_start:
{
lean_object* v___x_3801_; lean_object* v_newHyps_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___f_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3801_ = lean_array_get_size(v_hyps_3800_);
v_newHyps_3802_ = lean_mk_empty_array_with_capacity(v___x_3801_);
v___x_3803_ = lean_unsigned_to_nat(0u);
v___x_3804_ = lean_box(0);
lean_inc(v_toBind_3791_);
v___f_3805_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3805_, 0, v___x_3801_);
lean_closure_set(v___f_3805_, 1, v_toPure_3789_);
lean_closure_set(v___f_3805_, 2, v_hyps_3800_);
lean_closure_set(v___f_3805_, 3, v___x_3804_);
lean_closure_set(v___f_3805_, 4, v_inst_3790_);
lean_closure_set(v___f_3805_, 5, v_toBind_3791_);
lean_closure_set(v___f_3805_, 6, v_inst_3792_);
lean_closure_set(v___f_3805_, 7, v_inst_3793_);
lean_closure_set(v___f_3805_, 8, v_toMonadRef_3794_);
lean_closure_set(v___f_3805_, 9, v_inst_3795_);
lean_closure_set(v___f_3805_, 10, v_inst_3796_);
lean_closure_set(v___f_3805_, 11, v_f_3797_);
lean_closure_set(v___f_3805_, 12, v___f_3798_);
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v_newHyps_3802_);
v___x_3807_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3805_, v___x_3803_, v___x_3806_, lean_box(0));
v___x_3808_ = lean_apply_4(v_toBind_3791_, lean_box(0), lean_box(0), v___x_3807_, v___f_3799_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3809_, lean_object* v_inst_3810_, lean_object* v_inst_3811_, lean_object* v_inst_3812_, lean_object* v_inst_3813_, lean_object* v_inst_3814_, lean_object* v_f_3815_){
_start:
{
lean_object* v_toApplicative_3816_; lean_object* v_toBind_3817_; lean_object* v_toPure_3818_; lean_object* v_toMonadRef_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___f_3822_; lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v___f_3825_; lean_object* v___x_3826_; 
v_toApplicative_3816_ = lean_ctor_get(v_inst_3809_, 0);
v_toBind_3817_ = lean_ctor_get(v_inst_3809_, 1);
lean_inc_n(v_toBind_3817_, 3);
v_toPure_3818_ = lean_ctor_get(v_toApplicative_3816_, 1);
lean_inc_n(v_toPure_3818_, 4);
v_toMonadRef_3819_ = lean_ctor_get(v_inst_3811_, 1);
lean_inc_ref(v_toMonadRef_3819_);
lean_dec_ref(v_inst_3811_);
v___x_3820_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3810_, 2);
v___x_3821_ = lean_apply_2(v_inst_3810_, lean_box(0), v___x_3820_);
v___f_3822_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3822_, 0, v_toPure_3818_);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3823_, 0, v_inst_3810_);
lean_closure_set(v___f_3823_, 1, v_toBind_3817_);
lean_closure_set(v___f_3823_, 2, v___f_3822_);
lean_closure_set(v___f_3823_, 3, v_toPure_3818_);
v___f_3824_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3824_, 0, v_toPure_3818_);
v___f_3825_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3825_, 0, v_toPure_3818_);
lean_closure_set(v___f_3825_, 1, v_inst_3810_);
lean_closure_set(v___f_3825_, 2, v_toBind_3817_);
lean_closure_set(v___f_3825_, 3, v_inst_3812_);
lean_closure_set(v___f_3825_, 4, v_inst_3809_);
lean_closure_set(v___f_3825_, 5, v_toMonadRef_3819_);
lean_closure_set(v___f_3825_, 6, v_inst_3814_);
lean_closure_set(v___f_3825_, 7, v_inst_3813_);
lean_closure_set(v___f_3825_, 8, v_f_3815_);
lean_closure_set(v___f_3825_, 9, v___f_3824_);
lean_closure_set(v___f_3825_, 10, v___f_3823_);
v___x_3826_ = lean_apply_4(v_toBind_3817_, lean_box(0), lean_box(0), v___x_3821_, v___f_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3827_, lean_object* v_inst_3828_, lean_object* v_inst_3829_, lean_object* v_inst_3830_, lean_object* v_inst_3831_, lean_object* v_inst_3832_, lean_object* v_inst_3833_, lean_object* v_inst_3834_, lean_object* v_inst_3835_, lean_object* v_f_3836_){
_start:
{
lean_object* v_toApplicative_3837_; lean_object* v_toBind_3838_; lean_object* v_toPure_3839_; lean_object* v_toMonadRef_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___f_3843_; lean_object* v___f_3844_; lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___x_3847_; 
v_toApplicative_3837_ = lean_ctor_get(v_inst_3828_, 0);
v_toBind_3838_ = lean_ctor_get(v_inst_3828_, 1);
lean_inc_n(v_toBind_3838_, 3);
v_toPure_3839_ = lean_ctor_get(v_toApplicative_3837_, 1);
lean_inc_n(v_toPure_3839_, 4);
v_toMonadRef_3840_ = lean_ctor_get(v_inst_3830_, 1);
lean_inc_ref(v_toMonadRef_3840_);
lean_dec_ref(v_inst_3830_);
v___x_3841_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3829_, 2);
v___x_3842_ = lean_apply_2(v_inst_3829_, lean_box(0), v___x_3841_);
v___f_3843_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3843_, 0, v_toPure_3839_);
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3844_, 0, v_inst_3829_);
lean_closure_set(v___f_3844_, 1, v_toBind_3838_);
lean_closure_set(v___f_3844_, 2, v___f_3843_);
lean_closure_set(v___f_3844_, 3, v_toPure_3839_);
v___f_3845_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3845_, 0, v_toPure_3839_);
v___f_3846_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3846_, 0, v_toPure_3839_);
lean_closure_set(v___f_3846_, 1, v_inst_3829_);
lean_closure_set(v___f_3846_, 2, v_toBind_3838_);
lean_closure_set(v___f_3846_, 3, v_inst_3832_);
lean_closure_set(v___f_3846_, 4, v_inst_3828_);
lean_closure_set(v___f_3846_, 5, v_toMonadRef_3840_);
lean_closure_set(v___f_3846_, 6, v_inst_3834_);
lean_closure_set(v___f_3846_, 7, v_inst_3833_);
lean_closure_set(v___f_3846_, 8, v_f_3836_);
lean_closure_set(v___f_3846_, 9, v___f_3845_);
lean_closure_set(v___f_3846_, 10, v___f_3844_);
v___x_3847_ = lean_apply_4(v_toBind_3838_, lean_box(0), lean_box(0), v___x_3842_, v___f_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3848_, lean_object* v_inst_3849_, lean_object* v_inst_3850_, lean_object* v_inst_3851_, lean_object* v_inst_3852_, lean_object* v_inst_3853_, lean_object* v_inst_3854_, lean_object* v_inst_3855_, lean_object* v_inst_3856_, lean_object* v_f_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3848_, v_inst_3849_, v_inst_3850_, v_inst_3851_, v_inst_3852_, v_inst_3853_, v_inst_3854_, v_inst_3855_, v_inst_3856_, v_f_3857_);
lean_dec_ref(v_inst_3856_);
lean_dec_ref(v_inst_3852_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3859_, lean_object* v_x_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_apply_1(v_f_3859_, v___y_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3863_, lean_object* v_inst_3864_, lean_object* v___f_3865_, lean_object* v_hyps_3866_){
_start:
{
lean_object* v_toPure_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; uint8_t v___x_3871_; 
v_toPure_3867_ = lean_ctor_get(v_toApplicative_3863_, 1);
lean_inc(v_toPure_3867_);
lean_dec_ref(v_toApplicative_3863_);
v___x_3868_ = lean_unsigned_to_nat(0u);
v___x_3869_ = lean_array_get_size(v_hyps_3866_);
v___x_3870_ = lean_box(0);
v___x_3871_ = lean_nat_dec_lt(v___x_3868_, v___x_3869_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; 
lean_dec_ref(v_hyps_3866_);
lean_dec(v___f_3865_);
lean_dec_ref(v_inst_3864_);
v___x_3872_ = lean_apply_2(v_toPure_3867_, lean_box(0), v___x_3870_);
return v___x_3872_;
}
else
{
uint8_t v___x_3873_; 
v___x_3873_ = lean_nat_dec_le(v___x_3869_, v___x_3869_);
if (v___x_3873_ == 0)
{
if (v___x_3871_ == 0)
{
lean_object* v___x_3874_; 
lean_dec_ref(v_hyps_3866_);
lean_dec(v___f_3865_);
lean_dec_ref(v_inst_3864_);
v___x_3874_ = lean_apply_2(v_toPure_3867_, lean_box(0), v___x_3870_);
return v___x_3874_;
}
else
{
size_t v___x_3875_; size_t v___x_3876_; lean_object* v___x_3877_; 
lean_dec(v_toPure_3867_);
v___x_3875_ = ((size_t)0ULL);
v___x_3876_ = lean_usize_of_nat(v___x_3869_);
v___x_3877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3864_, v___f_3865_, v_hyps_3866_, v___x_3875_, v___x_3876_, v___x_3870_);
return v___x_3877_;
}
}
else
{
size_t v___x_3878_; size_t v___x_3879_; lean_object* v___x_3880_; 
lean_dec(v_toPure_3867_);
v___x_3878_ = ((size_t)0ULL);
v___x_3879_ = lean_usize_of_nat(v___x_3869_);
v___x_3880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3864_, v___f_3865_, v_hyps_3866_, v___x_3878_, v___x_3879_, v___x_3870_);
return v___x_3880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3881_, lean_object* v_inst_3882_, lean_object* v_f_3883_){
_start:
{
lean_object* v_toApplicative_3884_; lean_object* v_toBind_3885_; lean_object* v___f_3886_; lean_object* v___f_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v_toApplicative_3884_ = lean_ctor_get(v_inst_3881_, 0);
lean_inc_ref(v_toApplicative_3884_);
v_toBind_3885_ = lean_ctor_get(v_inst_3881_, 1);
lean_inc(v_toBind_3885_);
v___f_3886_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3886_, 0, v_f_3883_);
v___f_3887_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3887_, 0, v_toApplicative_3884_);
lean_closure_set(v___f_3887_, 1, v_inst_3881_);
lean_closure_set(v___f_3887_, 2, v___f_3886_);
v___x_3888_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3889_ = lean_apply_2(v_inst_3882_, lean_box(0), v___x_3888_);
v___x_3890_ = lean_apply_4(v_toBind_3885_, lean_box(0), lean_box(0), v___x_3889_, v___f_3887_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3891_, lean_object* v_inst_3892_, lean_object* v_inst_3893_, lean_object* v_inst_3894_, lean_object* v_f_3895_){
_start:
{
lean_object* v_toApplicative_3896_; lean_object* v_toBind_3897_; lean_object* v___f_3898_; lean_object* v___f_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_toApplicative_3896_ = lean_ctor_get(v_inst_3892_, 0);
lean_inc_ref(v_toApplicative_3896_);
v_toBind_3897_ = lean_ctor_get(v_inst_3892_, 1);
lean_inc(v_toBind_3897_);
v___f_3898_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3898_, 0, v_f_3895_);
v___f_3899_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3899_, 0, v_toApplicative_3896_);
lean_closure_set(v___f_3899_, 1, v_inst_3892_);
lean_closure_set(v___f_3899_, 2, v___f_3898_);
v___x_3900_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3901_ = lean_apply_2(v_inst_3893_, lean_box(0), v___x_3900_);
v___x_3902_ = lean_apply_4(v_toBind_3897_, lean_box(0), lean_box(0), v___x_3901_, v___f_3899_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3903_, lean_object* v_inst_3904_, lean_object* v_inst_3905_, lean_object* v_inst_3906_, lean_object* v_f_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3903_, v_inst_3904_, v_inst_3905_, v_inst_3906_, v_f_3907_);
lean_dec_ref(v_inst_3906_);
return v_res_3908_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_3911_, lean_object* v_methods_3912_, lean_object* v_config_3913_, lean_object* v_hyp_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_){
_start:
{
lean_object* v___x_3923_; lean_object* v_caches_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v_typeAnalysis_3931_; lean_object* v_target_3932_; lean_object* v_hypotheses_3933_; uint8_t v_didChange_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3975_; 
v___x_3923_ = lean_st_ref_get(v_a_3915_);
v_caches_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc_ref(v_caches_3924_);
lean_dec(v___x_3923_);
v___x_3925_ = lean_unsigned_to_nat(0u);
v___x_3926_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_3911_, v_caches_3924_);
v___x_3927_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_3928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3925_);
lean_ctor_set(v___x_3928_, 1, v___x_3926_);
lean_ctor_set(v___x_3928_, 2, v___x_3927_);
lean_ctor_set(v___x_3928_, 3, v___x_3927_);
v___x_3929_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3911_, v___x_3927_, v_caches_3924_);
v___x_3930_ = lean_st_ref_take(v_a_3915_);
v_typeAnalysis_3931_ = lean_ctor_get(v___x_3930_, 1);
v_target_3932_ = lean_ctor_get(v___x_3930_, 2);
v_hypotheses_3933_ = lean_ctor_get(v___x_3930_, 3);
v_didChange_3934_ = lean_ctor_get_uint8(v___x_3930_, sizeof(void*)*4);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; 
v_unused_3976_ = lean_ctor_get(v___x_3930_, 0);
lean_dec(v_unused_3976_);
v___x_3936_ = v___x_3930_;
v_isShared_3937_ = v_isSharedCheck_3975_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_hypotheses_3933_);
lean_inc(v_target_3932_);
lean_inc(v_typeAnalysis_3931_);
lean_dec(v___x_3930_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3975_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v___x_3929_);
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_typeAnalysis_3931_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_target_3932_);
lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_hypotheses_3933_);
lean_ctor_set_uint8(v_reuseFailAlloc_3974_, sizeof(void*)*4, v_didChange_3934_);
v___x_3939_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3940_; lean_object* v_type_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3940_ = lean_st_ref_put(v_a_3915_, v___x_3939_);
v_type_3941_ = lean_ctor_get(v_hyp_3914_, 1);
lean_inc_ref(v_type_3941_);
v___x_3942_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3942_, 0, v_type_3941_);
v___x_3943_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3942_, v_methods_3912_, v_config_3913_, v___x_3928_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v_fst_3945_; lean_object* v_snd_3946_; lean_object* v___x_3947_; lean_object* v_caches_3948_; lean_object* v_persistentCache_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v_typeAnalysis_3952_; lean_object* v_target_3953_; lean_object* v_hypotheses_3954_; uint8_t v_didChange_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3964_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v_fst_3945_ = lean_ctor_get(v_a_3944_, 0);
lean_inc(v_fst_3945_);
v_snd_3946_ = lean_ctor_get(v_a_3944_, 1);
lean_inc(v_snd_3946_);
lean_dec(v_a_3944_);
v___x_3947_ = lean_st_ref_get(v_a_3915_);
v_caches_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc_ref(v_caches_3948_);
lean_dec(v___x_3947_);
v_persistentCache_3949_ = lean_ctor_get(v_snd_3946_, 1);
lean_inc_ref(v_persistentCache_3949_);
lean_dec(v_snd_3946_);
v___x_3950_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3911_, v_persistentCache_3949_, v_caches_3948_);
v___x_3951_ = lean_st_ref_take(v_a_3915_);
v_typeAnalysis_3952_ = lean_ctor_get(v___x_3951_, 1);
v_target_3953_ = lean_ctor_get(v___x_3951_, 2);
v_hypotheses_3954_ = lean_ctor_get(v___x_3951_, 3);
v_didChange_3955_ = lean_ctor_get_uint8(v___x_3951_, sizeof(void*)*4);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; 
v_unused_3965_ = lean_ctor_get(v___x_3951_, 0);
lean_dec(v_unused_3965_);
v___x_3957_ = v___x_3951_;
v_isShared_3958_ = v_isSharedCheck_3964_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_hypotheses_3954_);
lean_inc(v_target_3953_);
lean_inc(v_typeAnalysis_3952_);
lean_dec(v___x_3951_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3964_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v___x_3950_);
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_typeAnalysis_3952_);
lean_ctor_set(v_reuseFailAlloc_3963_, 2, v_target_3953_);
lean_ctor_set(v_reuseFailAlloc_3963_, 3, v_hypotheses_3954_);
lean_ctor_set_uint8(v_reuseFailAlloc_3963_, sizeof(void*)*4, v_didChange_3955_);
v___x_3960_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_st_ref_put(v_a_3915_, v___x_3960_);
v___x_3962_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_3914_, v_fst_3945_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
return v___x_3962_;
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec_ref(v_hyp_3914_);
v_a_3966_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3943_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3943_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_3977_, lean_object* v_methods_3978_, lean_object* v_config_3979_, lean_object* v_hyp_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
uint8_t v_cacheId_boxed_3989_; lean_object* v_res_3990_; 
v_cacheId_boxed_3989_ = lean_unbox(v_cacheId_3977_);
v_res_3990_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_3989_, v_methods_3978_, v_config_3979_, v_hyp_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_3991_, lean_object* v_methods_3992_, lean_object* v_config_3993_, lean_object* v_hyp_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_3991_, v_methods_3992_, v_config_3993_, v_hyp_3994_, v_a_3996_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4008_, lean_object* v_methods_4009_, lean_object* v_config_4010_, lean_object* v_hyp_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_){
_start:
{
uint8_t v_cacheId_boxed_4024_; lean_object* v_res_4025_; 
v_cacheId_boxed_4024_ = lean_unbox(v_cacheId_4008_);
v_res_4025_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4024_, v_methods_4009_, v_config_4010_, v_hyp_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4026_, lean_object* v_methods_4027_, lean_object* v_config_4028_, lean_object* v_hyp_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
lean_object* v___x_4038_; lean_object* v_caches_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v_typeAnalysis_4046_; lean_object* v_target_4047_; lean_object* v_hypotheses_4048_; uint8_t v_didChange_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4090_; 
v___x_4038_ = lean_st_ref_get(v_a_4030_);
v_caches_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc_ref(v_caches_4039_);
lean_dec(v___x_4038_);
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4026_, v_caches_4039_);
v___x_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4040_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4044_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4026_, v___x_4043_, v_caches_4039_);
v___x_4045_ = lean_st_ref_take(v_a_4030_);
v_typeAnalysis_4046_ = lean_ctor_get(v___x_4045_, 1);
v_target_4047_ = lean_ctor_get(v___x_4045_, 2);
v_hypotheses_4048_ = lean_ctor_get(v___x_4045_, 3);
v_didChange_4049_ = lean_ctor_get_uint8(v___x_4045_, sizeof(void*)*4);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v___x_4045_, 0);
lean_dec(v_unused_4091_);
v___x_4051_ = v___x_4045_;
v_isShared_4052_ = v_isSharedCheck_4090_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_hypotheses_4048_);
lean_inc(v_target_4047_);
lean_inc(v_typeAnalysis_4046_);
lean_dec(v___x_4045_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4090_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v___x_4044_);
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4044_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_typeAnalysis_4046_);
lean_ctor_set(v_reuseFailAlloc_4089_, 2, v_target_4047_);
lean_ctor_set(v_reuseFailAlloc_4089_, 3, v_hypotheses_4048_);
lean_ctor_set_uint8(v_reuseFailAlloc_4089_, sizeof(void*)*4, v_didChange_4049_);
v___x_4054_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; lean_object* v_type_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4055_ = lean_st_ref_put(v_a_4030_, v___x_4054_);
v_type_4056_ = lean_ctor_get(v_hyp_4029_, 1);
lean_inc_ref(v_type_4056_);
v___x_4057_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4057_, 0, v_type_4056_);
v___x_4058_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4057_, v_methods_4027_, v_config_4028_, v___x_4042_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v_fst_4060_; lean_object* v_snd_4061_; lean_object* v___x_4062_; lean_object* v_caches_4063_; lean_object* v_cache_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v_typeAnalysis_4067_; lean_object* v_target_4068_; lean_object* v_hypotheses_4069_; uint8_t v_didChange_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4079_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v_fst_4060_ = lean_ctor_get(v_a_4059_, 0);
lean_inc(v_fst_4060_);
v_snd_4061_ = lean_ctor_get(v_a_4059_, 1);
lean_inc(v_snd_4061_);
lean_dec(v_a_4059_);
v___x_4062_ = lean_st_ref_get(v_a_4030_);
v_caches_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc_ref(v_caches_4063_);
lean_dec(v___x_4062_);
v_cache_4064_ = lean_ctor_get(v_snd_4061_, 1);
lean_inc_ref(v_cache_4064_);
lean_dec(v_snd_4061_);
v___x_4065_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4026_, v_cache_4064_, v_caches_4063_);
v___x_4066_ = lean_st_ref_take(v_a_4030_);
v_typeAnalysis_4067_ = lean_ctor_get(v___x_4066_, 1);
v_target_4068_ = lean_ctor_get(v___x_4066_, 2);
v_hypotheses_4069_ = lean_ctor_get(v___x_4066_, 3);
v_didChange_4070_ = lean_ctor_get_uint8(v___x_4066_, sizeof(void*)*4);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4079_ == 0)
{
lean_object* v_unused_4080_; 
v_unused_4080_ = lean_ctor_get(v___x_4066_, 0);
lean_dec(v_unused_4080_);
v___x_4072_ = v___x_4066_;
v_isShared_4073_ = v_isSharedCheck_4079_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_hypotheses_4069_);
lean_inc(v_target_4068_);
lean_inc(v_typeAnalysis_4067_);
lean_dec(v___x_4066_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4079_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 0, v___x_4065_);
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v_typeAnalysis_4067_);
lean_ctor_set(v_reuseFailAlloc_4078_, 2, v_target_4068_);
lean_ctor_set(v_reuseFailAlloc_4078_, 3, v_hypotheses_4069_);
lean_ctor_set_uint8(v_reuseFailAlloc_4078_, sizeof(void*)*4, v_didChange_4070_);
v___x_4075_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_st_ref_put(v_a_4030_, v___x_4075_);
v___x_4077_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4029_, v_fst_4060_);
lean_dec(v_fst_4060_);
return v___x_4077_;
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec_ref(v_hyp_4029_);
v_a_4081_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4058_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4058_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4092_, lean_object* v_methods_4093_, lean_object* v_config_4094_, lean_object* v_hyp_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
uint8_t v_cacheId_boxed_4104_; lean_object* v_res_4105_; 
v_cacheId_boxed_4104_ = lean_unbox(v_cacheId_4092_);
v_res_4105_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4104_, v_methods_4093_, v_config_4094_, v_hyp_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec(v_a_4096_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4106_, lean_object* v_methods_4107_, lean_object* v_config_4108_, lean_object* v_hyp_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4106_, v_methods_4107_, v_config_4108_, v_hyp_4109_, v_a_4111_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4123_, lean_object* v_methods_4124_, lean_object* v_config_4125_, lean_object* v_hyp_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
uint8_t v_cacheId_boxed_4139_; lean_object* v_res_4140_; 
v_cacheId_boxed_4139_ = lean_unbox(v_cacheId_4123_);
v_res_4140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4139_, v_methods_4124_, v_config_4125_, v_hyp_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec(v_a_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
lean_dec(v_a_4129_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4141_, lean_object* v_a_4142_, lean_object* v___x_4143_, lean_object* v_____r_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4157_ = lean_array_push(v_snd_4141_, v_a_4142_);
v___x_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4143_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4161_, lean_object* v_a_4162_, lean_object* v___x_4163_, lean_object* v_____r_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4161_, v_a_4162_, v___x_4163_, v_____r_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4178_, lean_object* v___f_4179_, lean_object* v_____r_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v___x_4193_; lean_object* v_caches_4194_; lean_object* v_typeAnalysis_4195_; lean_object* v_target_4196_; lean_object* v_hypotheses_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4207_; 
v___x_4193_ = lean_st_ref_take(v___y_4182_);
v_caches_4194_ = lean_ctor_get(v___x_4193_, 0);
v_typeAnalysis_4195_ = lean_ctor_get(v___x_4193_, 1);
v_target_4196_ = lean_ctor_get(v___x_4193_, 2);
v_hypotheses_4197_ = lean_ctor_get(v___x_4193_, 3);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4199_ = v___x_4193_;
v_isShared_4200_ = v_isSharedCheck_4207_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_hypotheses_4197_);
lean_inc(v_target_4196_);
lean_inc(v_typeAnalysis_4195_);
lean_inc(v_caches_4194_);
lean_dec(v___x_4193_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4207_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4201_; lean_object* v___x_4203_; 
v___x_4201_ = lean_box(0);
if (v_isShared_4200_ == 0)
{
v___x_4203_ = v___x_4199_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_caches_4194_);
lean_ctor_set(v_reuseFailAlloc_4206_, 1, v_typeAnalysis_4195_);
lean_ctor_set(v_reuseFailAlloc_4206_, 2, v_target_4196_);
lean_ctor_set(v_reuseFailAlloc_4206_, 3, v_hypotheses_4197_);
v___x_4203_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_ctor_set_uint8(v___x_4203_, sizeof(void*)*4, v___x_4178_);
v___x_4204_ = lean_st_ref_put(v___y_4182_, v___x_4203_);
lean_inc(v___y_4191_);
lean_inc_ref(v___y_4190_);
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
lean_inc(v___y_4187_);
lean_inc_ref(v___y_4186_);
lean_inc(v___y_4185_);
lean_inc_ref(v___y_4184_);
lean_inc(v___y_4183_);
lean_inc(v___y_4182_);
lean_inc_ref(v___y_4181_);
v___x_4205_ = lean_apply_13(v___f_4179_, v___x_4201_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, lean_box(0));
return v___x_4205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4208_, lean_object* v___f_4209_, lean_object* v_____r_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
uint8_t v___x_22285__boxed_4223_; lean_object* v_res_4224_; 
v___x_22285__boxed_4223_ = lean_unbox(v___x_4208_);
v_res_4224_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22285__boxed_4223_, v___f_4209_, v_____r_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4225_, lean_object* v_hypotheses_4226_, uint8_t v_cacheId_4227_, lean_object* v_methods_4228_, lean_object* v_config_4229_, lean_object* v___x_4230_, lean_object* v___x_4231_, lean_object* v___x_4232_, lean_object* v_toMonadRef_4233_, lean_object* v___f_4234_, lean_object* v_next_4235_, lean_object* v_acc_4236_, lean_object* v_h_4237_, lean_object* v_G_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v___y_4252_; uint8_t v___x_4274_; 
v___x_4274_ = lean_nat_dec_lt(v_next_4235_, v___x_4225_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; 
lean_dec_ref(v_G_4238_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
lean_dec(v___x_4230_);
lean_dec_ref(v_config_4229_);
lean_dec_ref(v_methods_4228_);
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v_acc_4236_);
return v___x_4275_;
}
else
{
lean_object* v_snd_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4350_; 
v_snd_4276_ = lean_ctor_get(v_acc_4236_, 1);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_acc_4236_);
if (v_isSharedCheck_4350_ == 0)
{
lean_object* v_unused_4351_; 
v_unused_4351_ = lean_ctor_get(v_acc_4236_, 0);
lean_dec(v_unused_4351_);
v___x_4278_ = v_acc_4236_;
v_isShared_4279_ = v_isSharedCheck_4350_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_snd_4276_);
lean_dec(v_acc_4236_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4350_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4280_ = lean_array_fget_borrowed(v_hypotheses_4226_, v_next_4235_);
lean_inc(v___x_4280_);
v___x_4281_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4227_, v_methods_4228_, v_config_4229_, v___x_4280_, v___y_4240_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; lean_object* v_type_4283_; lean_object* v_value_4284_; uint8_t v___x_4285_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___x_4281_, 1);
v_type_4283_ = lean_ctor_get(v_a_4282_, 1);
v_value_4284_ = lean_ctor_get(v_a_4282_, 2);
lean_inc_ref(v_type_4283_);
v___x_4285_ = l_Lean_Expr_isFalse(v_type_4283_);
if (v___x_4285_ == 0)
{
lean_object* v_type_4286_; lean_object* v___f_4287_; uint8_t v___x_4317_; 
lean_del_object(v___x_4278_);
v_type_4286_ = lean_ctor_get(v___x_4280_, 1);
lean_inc(v___x_4230_);
lean_inc(v_a_4282_);
lean_inc(v_snd_4276_);
v___f_4287_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4287_, 0, v_snd_4276_);
lean_closure_set(v___f_4287_, 1, v_a_4282_);
lean_closure_set(v___f_4287_, 2, v___x_4230_);
v___x_4317_ = lean_expr_eqv(v_type_4286_, v_type_4283_);
if (v___x_4317_ == 0)
{
lean_inc_ref(v_type_4283_);
lean_dec(v_a_4282_);
lean_dec(v_snd_4276_);
lean_dec(v___x_4230_);
goto v___jp_4291_;
}
else
{
if (v___x_4285_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
lean_dec_ref(v___f_4287_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
v___x_4318_ = lean_box(0);
v___x_4319_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4276_, v_a_4282_, v___x_4230_, v___x_4318_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
v___y_4252_ = v___x_4319_;
goto v___jp_4251_;
}
else
{
lean_inc_ref(v_type_4283_);
lean_dec(v_a_4282_);
lean_dec(v_snd_4276_);
lean_dec(v___x_4230_);
goto v___jp_4291_;
}
}
v___jp_4288_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = lean_box(0);
v___x_4290_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4274_, v___f_4287_, v___x_4289_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
v___y_4252_ = v___x_4290_;
goto v___jp_4251_;
}
v___jp_4291_:
{
lean_object* v_toCold_4292_; lean_object* v_options_4293_; uint8_t v_hasTrace_4294_; 
v_toCold_4292_ = lean_ctor_get(v___y_4248_, 0);
v_options_4293_ = lean_ctor_get(v_toCold_4292_, 2);
v_hasTrace_4294_ = lean_ctor_get_uint8(v_options_4293_, sizeof(void*)*1);
if (v_hasTrace_4294_ == 0)
{
lean_dec_ref(v_type_4283_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
goto v___jp_4288_;
}
else
{
lean_object* v_inheritedTraceOptions_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v_inheritedTraceOptions_4295_ = lean_ctor_get(v_toCold_4292_, 11);
v___x_4296_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4297_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4298_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4293_, v___x_4297_);
if (v___x_4298_ == 0)
{
lean_dec_ref(v_type_4283_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
goto v___jp_4288_;
}
else
{
lean_object* v_type_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_22210__overap_4305_; lean_object* v___x_4306_; 
v_type_4299_ = lean_ctor_get(v___x_4280_, 1);
lean_inc_ref(v_type_4299_);
v___x_4300_ = l_Lean_MessageData_ofExpr(v_type_4299_);
v___x_4301_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = l_Lean_MessageData_ofExpr(v_type_4283_);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_22210__overap_4305_ = l_Lean_addTrace___redArg(v___x_4231_, v___x_4232_, v_toMonadRef_4233_, v___f_4234_, v___x_4296_, v___x_4304_);
lean_inc(v___y_4249_);
lean_inc_ref(v___y_4248_);
lean_inc(v___y_4247_);
lean_inc_ref(v___y_4246_);
lean_inc(v___y_4245_);
lean_inc_ref(v___y_4244_);
lean_inc(v___y_4243_);
lean_inc_ref(v___y_4242_);
lean_inc(v___y_4241_);
lean_inc(v___y_4240_);
lean_inc_ref(v___y_4239_);
v___x_4306_ = lean_apply_12(v___x_22210__overap_4305_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, lean_box(0));
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4308_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4274_, v___f_4287_, v_a_4307_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
v___y_4252_ = v___x_4308_;
goto v___jp_4251_;
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref(v___f_4287_);
lean_dec_ref(v_G_4238_);
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
}
}
else
{
lean_object* v___x_4320_; 
lean_inc_ref(v_value_4284_);
lean_dec(v_a_4282_);
lean_dec_ref(v_G_4238_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
lean_dec(v___x_4230_);
v___x_4320_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4284_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4332_; 
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4332_ == 0)
{
lean_object* v_unused_4333_; 
v_unused_4333_ = lean_ctor_get(v___x_4320_, 0);
lean_dec(v_unused_4333_);
v___x_4322_ = v___x_4320_;
v_isShared_4323_ = v_isSharedCheck_4332_;
goto v_resetjp_4321_;
}
else
{
lean_dec(v___x_4320_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4332_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4327_; 
v___x_4324_ = lean_box(v___x_4274_);
v___x_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v___x_4325_);
v___x_4327_ = v___x_4278_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4325_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v_snd_4276_);
v___x_4327_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
lean_object* v___x_4329_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 0, v___x_4327_);
v___x_4329_ = v___x_4322_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_del_object(v___x_4278_);
lean_dec(v_snd_4276_);
v_a_4334_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4320_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4320_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
lean_del_object(v___x_4278_);
lean_dec(v_snd_4276_);
lean_dec_ref(v_G_4238_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
lean_dec(v___x_4230_);
v_a_4342_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4281_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4281_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
v___jp_4251_:
{
if (lean_obj_tag(v___y_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4265_; 
v_a_4253_ = lean_ctor_get(v___y_4252_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___y_4252_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4255_ = v___y_4252_;
v_isShared_4256_ = v_isSharedCheck_4265_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___y_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4265_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
if (lean_obj_tag(v_a_4253_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4259_; 
lean_dec_ref(v_G_4238_);
v_a_4257_ = lean_ctor_get(v_a_4253_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v_a_4253_, 1);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v_a_4257_);
v___x_4259_ = v___x_4255_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4257_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
lean_del_object(v___x_4255_);
v_a_4261_ = lean_ctor_get(v_a_4253_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v_a_4253_, 1);
v___x_4262_ = lean_unsigned_to_nat(1u);
v___x_4263_ = lean_nat_add(v_next_4235_, v___x_4262_);
lean_inc(v___y_4249_);
lean_inc_ref(v___y_4248_);
lean_inc(v___y_4247_);
lean_inc_ref(v___y_4246_);
lean_inc(v___y_4245_);
lean_inc_ref(v___y_4244_);
lean_inc(v___y_4243_);
lean_inc_ref(v___y_4242_);
lean_inc(v___y_4241_);
lean_inc(v___y_4240_);
lean_inc_ref(v___y_4239_);
v___x_4264_ = lean_apply_16(v_G_4238_, v___x_4263_, v_a_4261_, lean_box(0), lean_box(0), v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, lean_box(0));
return v___x_4264_;
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_dec_ref(v_G_4238_);
v_a_4266_ = lean_ctor_get(v___y_4252_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___y_4252_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___y_4252_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___y_4252_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4352_ = _args[0];
lean_object* v_hypotheses_4353_ = _args[1];
lean_object* v_cacheId_4354_ = _args[2];
lean_object* v_methods_4355_ = _args[3];
lean_object* v_config_4356_ = _args[4];
lean_object* v___x_4357_ = _args[5];
lean_object* v___x_4358_ = _args[6];
lean_object* v___x_4359_ = _args[7];
lean_object* v_toMonadRef_4360_ = _args[8];
lean_object* v___f_4361_ = _args[9];
lean_object* v_next_4362_ = _args[10];
lean_object* v_acc_4363_ = _args[11];
lean_object* v_h_4364_ = _args[12];
lean_object* v_G_4365_ = _args[13];
lean_object* v___y_4366_ = _args[14];
lean_object* v___y_4367_ = _args[15];
lean_object* v___y_4368_ = _args[16];
lean_object* v___y_4369_ = _args[17];
lean_object* v___y_4370_ = _args[18];
lean_object* v___y_4371_ = _args[19];
lean_object* v___y_4372_ = _args[20];
lean_object* v___y_4373_ = _args[21];
lean_object* v___y_4374_ = _args[22];
lean_object* v___y_4375_ = _args[23];
lean_object* v___y_4376_ = _args[24];
lean_object* v___y_4377_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4378_; lean_object* v_res_4379_; 
v_cacheId_boxed_4378_ = lean_unbox(v_cacheId_4354_);
v_res_4379_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4352_, v_hypotheses_4353_, v_cacheId_boxed_4378_, v_methods_4355_, v_config_4356_, v___x_4357_, v___x_4358_, v___x_4359_, v_toMonadRef_4360_, v___f_4361_, v_next_4362_, v_acc_4363_, v_h_4364_, v_G_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v_next_4362_);
lean_dec_ref(v_hypotheses_4353_);
lean_dec(v___x_4352_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4380_, lean_object* v_methods_4381_, lean_object* v_config_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v___x_4395_; lean_object* v_toApplicative_4396_; lean_object* v_toFunctor_4397_; lean_object* v_toSeq_4398_; lean_object* v_toSeqLeft_4399_; lean_object* v_toSeqRight_4400_; lean_object* v___f_4401_; lean_object* v___f_4402_; lean_object* v___f_4403_; lean_object* v___f_4404_; lean_object* v___x_4405_; lean_object* v___f_4406_; lean_object* v___f_4407_; lean_object* v___f_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v_toApplicative_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4499_; 
v___x_4395_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4396_ = lean_ctor_get(v___x_4395_, 0);
v_toFunctor_4397_ = lean_ctor_get(v_toApplicative_4396_, 0);
v_toSeq_4398_ = lean_ctor_get(v_toApplicative_4396_, 2);
v_toSeqLeft_4399_ = lean_ctor_get(v_toApplicative_4396_, 3);
v_toSeqRight_4400_ = lean_ctor_get(v_toApplicative_4396_, 4);
v___f_4401_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4402_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4397_, 2);
v___f_4403_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4403_, 0, v_toFunctor_4397_);
v___f_4404_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4404_, 0, v_toFunctor_4397_);
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___f_4403_);
lean_ctor_set(v___x_4405_, 1, v___f_4404_);
lean_inc(v_toSeqRight_4400_);
v___f_4406_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4406_, 0, v_toSeqRight_4400_);
lean_inc(v_toSeqLeft_4399_);
v___f_4407_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4407_, 0, v_toSeqLeft_4399_);
lean_inc(v_toSeq_4398_);
v___f_4408_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4408_, 0, v_toSeq_4398_);
v___x_4409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4405_);
lean_ctor_set(v___x_4409_, 1, v___f_4401_);
lean_ctor_set(v___x_4409_, 2, v___f_4408_);
lean_ctor_set(v___x_4409_, 3, v___f_4407_);
lean_ctor_set(v___x_4409_, 4, v___f_4406_);
v___x_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
lean_ctor_set(v___x_4410_, 1, v___f_4402_);
v___x_4411_ = l_StateRefT_x27_instMonad___redArg(v___x_4410_);
v_toApplicative_4412_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4499_ == 0)
{
lean_object* v_unused_4500_; 
v_unused_4500_ = lean_ctor_get(v___x_4411_, 1);
lean_dec(v_unused_4500_);
v___x_4414_ = v___x_4411_;
v_isShared_4415_ = v_isSharedCheck_4499_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_toApplicative_4412_);
lean_dec(v___x_4411_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4499_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v_toFunctor_4416_; lean_object* v_toSeq_4417_; lean_object* v_toSeqLeft_4418_; lean_object* v_toSeqRight_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4497_; 
v_toFunctor_4416_ = lean_ctor_get(v_toApplicative_4412_, 0);
v_toSeq_4417_ = lean_ctor_get(v_toApplicative_4412_, 2);
v_toSeqLeft_4418_ = lean_ctor_get(v_toApplicative_4412_, 3);
v_toSeqRight_4419_ = lean_ctor_get(v_toApplicative_4412_, 4);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_toApplicative_4412_);
if (v_isSharedCheck_4497_ == 0)
{
lean_object* v_unused_4498_; 
v_unused_4498_ = lean_ctor_get(v_toApplicative_4412_, 1);
lean_dec(v_unused_4498_);
v___x_4421_ = v_toApplicative_4412_;
v_isShared_4422_ = v_isSharedCheck_4497_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_toSeqRight_4419_);
lean_inc(v_toSeqLeft_4418_);
lean_inc(v_toSeq_4417_);
lean_inc(v_toFunctor_4416_);
lean_dec(v_toApplicative_4412_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4497_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___f_4423_; lean_object* v___f_4424_; lean_object* v___f_4425_; lean_object* v___f_4426_; lean_object* v___x_4427_; lean_object* v___f_4428_; lean_object* v___f_4429_; lean_object* v___f_4430_; lean_object* v___x_4432_; 
v___f_4423_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4424_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4416_);
v___f_4425_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4425_, 0, v_toFunctor_4416_);
v___f_4426_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4426_, 0, v_toFunctor_4416_);
v___x_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___f_4425_);
lean_ctor_set(v___x_4427_, 1, v___f_4426_);
v___f_4428_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4428_, 0, v_toSeqRight_4419_);
v___f_4429_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4429_, 0, v_toSeqLeft_4418_);
v___f_4430_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4430_, 0, v_toSeq_4417_);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 4, v___f_4428_);
lean_ctor_set(v___x_4421_, 3, v___f_4429_);
lean_ctor_set(v___x_4421_, 2, v___f_4430_);
lean_ctor_set(v___x_4421_, 1, v___f_4423_);
lean_ctor_set(v___x_4421_, 0, v___x_4427_);
v___x_4432_ = v___x_4421_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4427_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v___f_4423_);
lean_ctor_set(v_reuseFailAlloc_4496_, 2, v___f_4430_);
lean_ctor_set(v_reuseFailAlloc_4496_, 3, v___f_4429_);
lean_ctor_set(v_reuseFailAlloc_4496_, 4, v___f_4428_);
v___x_4432_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
lean_object* v___x_4434_; 
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 1, v___f_4424_);
lean_ctor_set(v___x_4414_, 0, v___x_4432_);
v___x_4434_ = v___x_4414_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v___f_4424_);
v___x_4434_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v_toMonadRef_4443_; lean_object* v___f_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v_hypotheses_4447_; lean_object* v___x_4448_; lean_object* v_newHyps_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v___x_22108__overap_4455_; lean_object* v___x_4456_; 
v___x_4435_ = l_StateRefT_x27_instMonad___redArg(v___x_4434_);
v___x_4436_ = l_ReaderT_instMonad___redArg(v___x_4435_);
v___x_4437_ = l_StateRefT_x27_instMonad___redArg(v___x_4436_);
v___x_4438_ = l_ReaderT_instMonad___redArg(v___x_4437_);
v___x_4439_ = l_ReaderT_instMonad___redArg(v___x_4438_);
v___x_4440_ = l_StateRefT_x27_instMonad___redArg(v___x_4439_);
v___x_4441_ = l_ReaderT_instMonad___redArg(v___x_4440_);
v___x_4442_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4443_ = lean_ctor_get(v___x_4442_, 0);
v___f_4444_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4445_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4446_ = lean_st_ref_get(v_a_4384_);
v_hypotheses_4447_ = lean_ctor_get(v___x_4446_, 3);
lean_inc_ref(v_hypotheses_4447_);
lean_dec(v___x_4446_);
v___x_4448_ = lean_array_get_size(v_hypotheses_4447_);
v_newHyps_4449_ = lean_mk_empty_array_with_capacity(v___x_4448_);
v___x_4450_ = lean_unsigned_to_nat(0u);
v___x_4451_ = lean_box(0);
v___x_4452_ = lean_box(v_cacheId_4380_);
lean_inc_ref(v_toMonadRef_4443_);
v___f_4453_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4453_, 0, v___x_4448_);
lean_closure_set(v___f_4453_, 1, v_hypotheses_4447_);
lean_closure_set(v___f_4453_, 2, v___x_4452_);
lean_closure_set(v___f_4453_, 3, v_methods_4381_);
lean_closure_set(v___f_4453_, 4, v_config_4382_);
lean_closure_set(v___f_4453_, 5, v___x_4451_);
lean_closure_set(v___f_4453_, 6, v___x_4441_);
lean_closure_set(v___f_4453_, 7, v___x_4445_);
lean_closure_set(v___f_4453_, 8, v_toMonadRef_4443_);
lean_closure_set(v___f_4453_, 9, v___f_4444_);
v___x_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4451_);
lean_ctor_set(v___x_4454_, 1, v_newHyps_4449_);
v___x_22108__overap_4455_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4453_, v___x_4450_, v___x_4454_, lean_box(0));
lean_inc(v_a_4393_);
lean_inc_ref(v_a_4392_);
lean_inc(v_a_4391_);
lean_inc_ref(v_a_4390_);
lean_inc(v_a_4389_);
lean_inc_ref(v_a_4388_);
lean_inc(v_a_4387_);
lean_inc_ref(v_a_4386_);
lean_inc(v_a_4385_);
lean_inc(v_a_4384_);
lean_inc_ref(v_a_4383_);
v___x_4456_ = lean_apply_12(v___x_22108__overap_4455_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, lean_box(0));
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4486_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4459_ = v___x_4456_;
v_isShared_4460_ = v_isSharedCheck_4486_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4456_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4486_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_fst_4461_; 
v_fst_4461_ = lean_ctor_get(v_a_4457_, 0);
if (lean_obj_tag(v_fst_4461_) == 0)
{
lean_object* v_snd_4462_; lean_object* v___x_4463_; lean_object* v_caches_4464_; lean_object* v_typeAnalysis_4465_; lean_object* v_target_4466_; uint8_t v_didChange_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4480_; 
v_snd_4462_ = lean_ctor_get(v_a_4457_, 1);
lean_inc(v_snd_4462_);
lean_dec(v_a_4457_);
v___x_4463_ = lean_st_ref_take(v_a_4384_);
v_caches_4464_ = lean_ctor_get(v___x_4463_, 0);
v_typeAnalysis_4465_ = lean_ctor_get(v___x_4463_, 1);
v_target_4466_ = lean_ctor_get(v___x_4463_, 2);
v_didChange_4467_ = lean_ctor_get_uint8(v___x_4463_, sizeof(void*)*4);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4480_ == 0)
{
lean_object* v_unused_4481_; 
v_unused_4481_ = lean_ctor_get(v___x_4463_, 3);
lean_dec(v_unused_4481_);
v___x_4469_ = v___x_4463_;
v_isShared_4470_ = v_isSharedCheck_4480_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_target_4466_);
lean_inc(v_typeAnalysis_4465_);
lean_inc(v_caches_4464_);
lean_dec(v___x_4463_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4480_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 3, v_snd_4462_);
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_caches_4464_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_typeAnalysis_4465_);
lean_ctor_set(v_reuseFailAlloc_4479_, 2, v_target_4466_);
lean_ctor_set(v_reuseFailAlloc_4479_, 3, v_snd_4462_);
lean_ctor_set_uint8(v_reuseFailAlloc_4479_, sizeof(void*)*4, v_didChange_4467_);
v___x_4472_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; uint8_t v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4477_; 
v___x_4473_ = lean_st_ref_put(v_a_4384_, v___x_4472_);
v___x_4474_ = 0;
v___x_4475_ = lean_box(v___x_4474_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4475_);
v___x_4477_ = v___x_4459_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4475_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
else
{
lean_object* v_val_4482_; lean_object* v___x_4484_; 
lean_inc_ref(v_fst_4461_);
lean_dec(v_a_4457_);
v_val_4482_ = lean_ctor_get(v_fst_4461_, 0);
lean_inc(v_val_4482_);
lean_dec_ref_known(v_fst_4461_, 1);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v_val_4482_);
v___x_4484_ = v___x_4459_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_val_4482_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
v_a_4487_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4456_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4456_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_4501_, lean_object* v_methods_4502_, lean_object* v_config_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
uint8_t v_cacheId_boxed_4516_; lean_object* v_res_4517_; 
v_cacheId_boxed_4516_ = lean_unbox(v_cacheId_4501_);
v_res_4517_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_4516_, v_methods_4502_, v_config_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_4518_, lean_object* v_hypotheses_4519_, uint8_t v_cacheId_4520_, lean_object* v_methods_4521_, lean_object* v_config_4522_, lean_object* v___x_4523_, lean_object* v___x_4524_, lean_object* v___x_4525_, lean_object* v_toMonadRef_4526_, lean_object* v___f_4527_, lean_object* v_next_4528_, lean_object* v_acc_4529_, lean_object* v_h_4530_, lean_object* v_G_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v___y_4545_; uint8_t v___x_4567_; 
v___x_4567_ = lean_nat_dec_lt(v_next_4528_, v___x_4518_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; 
lean_dec_ref(v_G_4531_);
lean_dec(v___f_4527_);
lean_dec_ref(v_toMonadRef_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
lean_dec(v___x_4523_);
lean_dec_ref(v_config_4522_);
lean_dec_ref(v_methods_4521_);
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v_acc_4529_);
return v___x_4568_;
}
else
{
lean_object* v_snd_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4643_; 
v_snd_4569_ = lean_ctor_get(v_acc_4529_, 1);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_acc_4529_);
if (v_isSharedCheck_4643_ == 0)
{
lean_object* v_unused_4644_; 
v_unused_4644_ = lean_ctor_get(v_acc_4529_, 0);
lean_dec(v_unused_4644_);
v___x_4571_ = v_acc_4529_;
v_isShared_4572_ = v_isSharedCheck_4643_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_snd_4569_);
lean_dec(v_acc_4529_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4643_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4573_ = lean_array_fget_borrowed(v_hypotheses_4519_, v_next_4528_);
lean_inc(v___x_4573_);
v___x_4574_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4520_, v_methods_4521_, v_config_4522_, v___x_4573_, v___y_4533_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v_type_4576_; lean_object* v_value_4577_; uint8_t v___x_4578_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref_known(v___x_4574_, 1);
v_type_4576_ = lean_ctor_get(v_a_4575_, 1);
v_value_4577_ = lean_ctor_get(v_a_4575_, 2);
lean_inc_ref(v_type_4576_);
v___x_4578_ = l_Lean_Expr_isFalse(v_type_4576_);
if (v___x_4578_ == 0)
{
lean_object* v_type_4579_; lean_object* v___f_4580_; uint8_t v___x_4610_; 
lean_del_object(v___x_4571_);
v_type_4579_ = lean_ctor_get(v___x_4573_, 1);
lean_inc(v___x_4523_);
lean_inc(v_a_4575_);
lean_inc(v_snd_4569_);
v___f_4580_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4580_, 0, v_snd_4569_);
lean_closure_set(v___f_4580_, 1, v_a_4575_);
lean_closure_set(v___f_4580_, 2, v___x_4523_);
v___x_4610_ = lean_expr_eqv(v_type_4579_, v_type_4576_);
if (v___x_4610_ == 0)
{
lean_inc_ref(v_type_4576_);
lean_dec(v_a_4575_);
lean_dec(v_snd_4569_);
lean_dec(v___x_4523_);
goto v___jp_4584_;
}
else
{
if (v___x_4578_ == 0)
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
lean_dec_ref(v___f_4580_);
lean_dec(v___f_4527_);
lean_dec_ref(v_toMonadRef_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
v___x_4611_ = lean_box(0);
v___x_4612_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4569_, v_a_4575_, v___x_4523_, v___x_4611_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
v___y_4545_ = v___x_4612_;
goto v___jp_4544_;
}
else
{
lean_inc_ref(v_type_4576_);
lean_dec(v_a_4575_);
lean_dec(v_snd_4569_);
lean_dec(v___x_4523_);
goto v___jp_4584_;
}
}
v___jp_4581_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = lean_box(0);
v___x_4583_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4567_, v___f_4580_, v___x_4582_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
v___y_4545_ = v___x_4583_;
goto v___jp_4544_;
}
v___jp_4584_:
{
lean_object* v_toCold_4585_; lean_object* v_options_4586_; uint8_t v_hasTrace_4587_; 
v_toCold_4585_ = lean_ctor_get(v___y_4541_, 0);
v_options_4586_ = lean_ctor_get(v_toCold_4585_, 2);
v_hasTrace_4587_ = lean_ctor_get_uint8(v_options_4586_, sizeof(void*)*1);
if (v_hasTrace_4587_ == 0)
{
lean_dec_ref(v_type_4576_);
lean_dec(v___f_4527_);
lean_dec_ref(v_toMonadRef_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
goto v___jp_4581_;
}
else
{
lean_object* v_inheritedTraceOptions_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; uint8_t v___x_4591_; 
v_inheritedTraceOptions_4588_ = lean_ctor_get(v_toCold_4585_, 11);
v___x_4589_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4590_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4588_, v_options_4586_, v___x_4590_);
if (v___x_4591_ == 0)
{
lean_dec_ref(v_type_4576_);
lean_dec(v___f_4527_);
lean_dec_ref(v_toMonadRef_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
goto v___jp_4581_;
}
else
{
lean_object* v_type_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_22210__overap_4598_; lean_object* v___x_4599_; 
v_type_4592_ = lean_ctor_get(v___x_4573_, 1);
lean_inc_ref(v_type_4592_);
v___x_4593_ = l_Lean_MessageData_ofExpr(v_type_4592_);
v___x_4594_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4593_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
v___x_4596_ = l_Lean_MessageData_ofExpr(v_type_4576_);
v___x_4597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4595_);
lean_ctor_set(v___x_4597_, 1, v___x_4596_);
v___x_22210__overap_4598_ = l_Lean_addTrace___redArg(v___x_4524_, v___x_4525_, v_toMonadRef_4526_, v___f_4527_, v___x_4589_, v___x_4597_);
lean_inc(v___y_4542_);
lean_inc_ref(v___y_4541_);
lean_inc(v___y_4540_);
lean_inc_ref(v___y_4539_);
lean_inc(v___y_4538_);
lean_inc_ref(v___y_4537_);
lean_inc(v___y_4536_);
lean_inc_ref(v___y_4535_);
lean_inc(v___y_4534_);
lean_inc(v___y_4533_);
lean_inc_ref(v___y_4532_);
v___x_4599_ = lean_apply_12(v___x_22210__overap_4598_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, lean_box(0));
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4601_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref_known(v___x_4599_, 1);
v___x_4601_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4567_, v___f_4580_, v_a_4600_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
v___y_4545_ = v___x_4601_;
goto v___jp_4544_;
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4609_; 
lean_dec_ref(v___f_4580_);
lean_dec_ref(v_G_4531_);
v_a_4602_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4604_ = v___x_4599_;
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4599_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4613_; 
lean_inc_ref(v_value_4577_);
lean_dec(v_a_4575_);
lean_dec_ref(v_G_4531_);
lean_dec(v___f_4527_);
lean_dec_ref(v_toMonadRef_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
lean_dec(v___x_4523_);
v___x_4613_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4577_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4625_; 
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4625_ == 0)
{
lean_object* v_unused_4626_; 
v_unused_4626_ = lean_ctor_get(v___x_4613_, 0);
lean_dec(v_unused_4626_);
v___x_4615_ = v___x_4613_;
v_isShared_4616_ = v_isSharedCheck_4625_;
goto v_resetjp_4614_;
}
else
{
lean_dec(v___x_4613_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4625_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
v___x_4617_ = lean_box(v___x_4567_);
v___x_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 0, v___x_4618_);
v___x_4620_ = v___x_4571_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4618_);
lean_ctor_set(v_reuseFailAlloc_4624_, 1, v_snd_4569_);
v___x_4620_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
lean_object* v___x_4622_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4620_);
v___x_4622_ = v___x_4615_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_del_object(v___x_4571_);
lean_dec(v_snd_4569_);
v_a_4627_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4613_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4613_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_del_object(v___x_4571_);
lean_dec(v_snd_4569_);
lean_dec_ref(v_G_4531_);
lean_dec(v___f_4527_);
lean_dec_ref(v_toMonadRef_4526_);
lean_dec_ref(v___x_4525_);
lean_dec_ref(v___x_4524_);
lean_dec(v___x_4523_);
v_a_4635_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4574_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4574_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
}
v___jp_4544_:
{
if (lean_obj_tag(v___y_4545_) == 0)
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4558_; 
v_a_4546_ = lean_ctor_get(v___y_4545_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___y_4545_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4548_ = v___y_4545_;
v_isShared_4549_ = v_isSharedCheck_4558_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___y_4545_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4558_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
if (lean_obj_tag(v_a_4546_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4552_; 
lean_dec_ref(v_G_4531_);
v_a_4550_ = lean_ctor_get(v_a_4546_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v_a_4546_, 1);
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 0, v_a_4550_);
v___x_4552_ = v___x_4548_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4550_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
lean_del_object(v___x_4548_);
v_a_4554_ = lean_ctor_get(v_a_4546_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v_a_4546_, 1);
v___x_4555_ = lean_unsigned_to_nat(1u);
v___x_4556_ = lean_nat_add(v_next_4528_, v___x_4555_);
lean_inc(v___y_4542_);
lean_inc_ref(v___y_4541_);
lean_inc(v___y_4540_);
lean_inc_ref(v___y_4539_);
lean_inc(v___y_4538_);
lean_inc_ref(v___y_4537_);
lean_inc(v___y_4536_);
lean_inc_ref(v___y_4535_);
lean_inc(v___y_4534_);
lean_inc(v___y_4533_);
lean_inc_ref(v___y_4532_);
v___x_4557_ = lean_apply_16(v_G_4531_, v___x_4556_, v_a_4554_, lean_box(0), lean_box(0), v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, lean_box(0));
return v___x_4557_;
}
}
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
lean_dec_ref(v_G_4531_);
v_a_4559_ = lean_ctor_get(v___y_4545_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___y_4545_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___y_4545_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___y_4545_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4645_ = _args[0];
lean_object* v_hypotheses_4646_ = _args[1];
lean_object* v_cacheId_4647_ = _args[2];
lean_object* v_methods_4648_ = _args[3];
lean_object* v_config_4649_ = _args[4];
lean_object* v___x_4650_ = _args[5];
lean_object* v___x_4651_ = _args[6];
lean_object* v___x_4652_ = _args[7];
lean_object* v_toMonadRef_4653_ = _args[8];
lean_object* v___f_4654_ = _args[9];
lean_object* v_next_4655_ = _args[10];
lean_object* v_acc_4656_ = _args[11];
lean_object* v_h_4657_ = _args[12];
lean_object* v_G_4658_ = _args[13];
lean_object* v___y_4659_ = _args[14];
lean_object* v___y_4660_ = _args[15];
lean_object* v___y_4661_ = _args[16];
lean_object* v___y_4662_ = _args[17];
lean_object* v___y_4663_ = _args[18];
lean_object* v___y_4664_ = _args[19];
lean_object* v___y_4665_ = _args[20];
lean_object* v___y_4666_ = _args[21];
lean_object* v___y_4667_ = _args[22];
lean_object* v___y_4668_ = _args[23];
lean_object* v___y_4669_ = _args[24];
lean_object* v___y_4670_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4671_; lean_object* v_res_4672_; 
v_cacheId_boxed_4671_ = lean_unbox(v_cacheId_4647_);
v_res_4672_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4645_, v_hypotheses_4646_, v_cacheId_boxed_4671_, v_methods_4648_, v_config_4649_, v___x_4650_, v___x_4651_, v___x_4652_, v_toMonadRef_4653_, v___f_4654_, v_next_4655_, v_acc_4656_, v_h_4657_, v_G_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v_next_4655_);
lean_dec_ref(v_hypotheses_4646_);
lean_dec(v___x_4645_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4673_, lean_object* v_methods_4674_, lean_object* v_config_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v___x_4688_; lean_object* v_toApplicative_4689_; lean_object* v_toFunctor_4690_; lean_object* v_toSeq_4691_; lean_object* v_toSeqLeft_4692_; lean_object* v_toSeqRight_4693_; lean_object* v___f_4694_; lean_object* v___f_4695_; lean_object* v___f_4696_; lean_object* v___f_4697_; lean_object* v___x_4698_; lean_object* v___f_4699_; lean_object* v___f_4700_; lean_object* v___f_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v_toApplicative_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4792_; 
v___x_4688_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4689_ = lean_ctor_get(v___x_4688_, 0);
v_toFunctor_4690_ = lean_ctor_get(v_toApplicative_4689_, 0);
v_toSeq_4691_ = lean_ctor_get(v_toApplicative_4689_, 2);
v_toSeqLeft_4692_ = lean_ctor_get(v_toApplicative_4689_, 3);
v_toSeqRight_4693_ = lean_ctor_get(v_toApplicative_4689_, 4);
v___f_4694_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4695_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4690_, 2);
v___f_4696_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4696_, 0, v_toFunctor_4690_);
v___f_4697_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4697_, 0, v_toFunctor_4690_);
v___x_4698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4698_, 0, v___f_4696_);
lean_ctor_set(v___x_4698_, 1, v___f_4697_);
lean_inc(v_toSeqRight_4693_);
v___f_4699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4699_, 0, v_toSeqRight_4693_);
lean_inc(v_toSeqLeft_4692_);
v___f_4700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4700_, 0, v_toSeqLeft_4692_);
lean_inc(v_toSeq_4691_);
v___f_4701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4701_, 0, v_toSeq_4691_);
v___x_4702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4698_);
lean_ctor_set(v___x_4702_, 1, v___f_4694_);
lean_ctor_set(v___x_4702_, 2, v___f_4701_);
lean_ctor_set(v___x_4702_, 3, v___f_4700_);
lean_ctor_set(v___x_4702_, 4, v___f_4699_);
v___x_4703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4702_);
lean_ctor_set(v___x_4703_, 1, v___f_4695_);
v___x_4704_ = l_StateRefT_x27_instMonad___redArg(v___x_4703_);
v_toApplicative_4705_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4792_ == 0)
{
lean_object* v_unused_4793_; 
v_unused_4793_ = lean_ctor_get(v___x_4704_, 1);
lean_dec(v_unused_4793_);
v___x_4707_ = v___x_4704_;
v_isShared_4708_ = v_isSharedCheck_4792_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_toApplicative_4705_);
lean_dec(v___x_4704_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4792_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v_toFunctor_4709_; lean_object* v_toSeq_4710_; lean_object* v_toSeqLeft_4711_; lean_object* v_toSeqRight_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4790_; 
v_toFunctor_4709_ = lean_ctor_get(v_toApplicative_4705_, 0);
v_toSeq_4710_ = lean_ctor_get(v_toApplicative_4705_, 2);
v_toSeqLeft_4711_ = lean_ctor_get(v_toApplicative_4705_, 3);
v_toSeqRight_4712_ = lean_ctor_get(v_toApplicative_4705_, 4);
v_isSharedCheck_4790_ = !lean_is_exclusive(v_toApplicative_4705_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; 
v_unused_4791_ = lean_ctor_get(v_toApplicative_4705_, 1);
lean_dec(v_unused_4791_);
v___x_4714_ = v_toApplicative_4705_;
v_isShared_4715_ = v_isSharedCheck_4790_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_toSeqRight_4712_);
lean_inc(v_toSeqLeft_4711_);
lean_inc(v_toSeq_4710_);
lean_inc(v_toFunctor_4709_);
lean_dec(v_toApplicative_4705_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4790_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___f_4716_; lean_object* v___f_4717_; lean_object* v___f_4718_; lean_object* v___f_4719_; lean_object* v___x_4720_; lean_object* v___f_4721_; lean_object* v___f_4722_; lean_object* v___f_4723_; lean_object* v___x_4725_; 
v___f_4716_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4717_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4709_);
v___f_4718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4718_, 0, v_toFunctor_4709_);
v___f_4719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4719_, 0, v_toFunctor_4709_);
v___x_4720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___f_4718_);
lean_ctor_set(v___x_4720_, 1, v___f_4719_);
v___f_4721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4721_, 0, v_toSeqRight_4712_);
v___f_4722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4722_, 0, v_toSeqLeft_4711_);
v___f_4723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4723_, 0, v_toSeq_4710_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 4, v___f_4721_);
lean_ctor_set(v___x_4714_, 3, v___f_4722_);
lean_ctor_set(v___x_4714_, 2, v___f_4723_);
lean_ctor_set(v___x_4714_, 1, v___f_4716_);
lean_ctor_set(v___x_4714_, 0, v___x_4720_);
v___x_4725_ = v___x_4714_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4720_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v___f_4716_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v___f_4723_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v___f_4722_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v___f_4721_);
v___x_4725_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4727_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 1, v___f_4717_);
lean_ctor_set(v___x_4707_, 0, v___x_4725_);
v___x_4727_ = v___x_4707_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4725_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v___f_4717_);
v___x_4727_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v_toMonadRef_4736_; lean_object* v___f_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v_hypotheses_4740_; lean_object* v___x_4741_; lean_object* v_newHyps_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___f_4746_; lean_object* v___x_4747_; lean_object* v___x_22108__overap_4748_; lean_object* v___x_4749_; 
v___x_4728_ = l_StateRefT_x27_instMonad___redArg(v___x_4727_);
v___x_4729_ = l_ReaderT_instMonad___redArg(v___x_4728_);
v___x_4730_ = l_StateRefT_x27_instMonad___redArg(v___x_4729_);
v___x_4731_ = l_ReaderT_instMonad___redArg(v___x_4730_);
v___x_4732_ = l_ReaderT_instMonad___redArg(v___x_4731_);
v___x_4733_ = l_StateRefT_x27_instMonad___redArg(v___x_4732_);
v___x_4734_ = l_ReaderT_instMonad___redArg(v___x_4733_);
v___x_4735_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4736_ = lean_ctor_get(v___x_4735_, 0);
v___f_4737_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4738_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4739_ = lean_st_ref_get(v_a_4677_);
v_hypotheses_4740_ = lean_ctor_get(v___x_4739_, 3);
lean_inc_ref(v_hypotheses_4740_);
lean_dec(v___x_4739_);
v___x_4741_ = lean_array_get_size(v_hypotheses_4740_);
v_newHyps_4742_ = lean_mk_empty_array_with_capacity(v___x_4741_);
v___x_4743_ = lean_unsigned_to_nat(0u);
v___x_4744_ = lean_box(0);
v___x_4745_ = lean_box(v_cacheId_4673_);
lean_inc_ref(v_toMonadRef_4736_);
v___f_4746_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4746_, 0, v___x_4741_);
lean_closure_set(v___f_4746_, 1, v_hypotheses_4740_);
lean_closure_set(v___f_4746_, 2, v___x_4745_);
lean_closure_set(v___f_4746_, 3, v_methods_4674_);
lean_closure_set(v___f_4746_, 4, v_config_4675_);
lean_closure_set(v___f_4746_, 5, v___x_4744_);
lean_closure_set(v___f_4746_, 6, v___x_4734_);
lean_closure_set(v___f_4746_, 7, v___x_4738_);
lean_closure_set(v___f_4746_, 8, v_toMonadRef_4736_);
lean_closure_set(v___f_4746_, 9, v___f_4737_);
v___x_4747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4744_);
lean_ctor_set(v___x_4747_, 1, v_newHyps_4742_);
v___x_22108__overap_4748_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4746_, v___x_4743_, v___x_4747_, lean_box(0));
lean_inc(v_a_4686_);
lean_inc_ref(v_a_4685_);
lean_inc(v_a_4684_);
lean_inc_ref(v_a_4683_);
lean_inc(v_a_4682_);
lean_inc_ref(v_a_4681_);
lean_inc(v_a_4680_);
lean_inc_ref(v_a_4679_);
lean_inc(v_a_4678_);
lean_inc(v_a_4677_);
lean_inc_ref(v_a_4676_);
v___x_4749_ = lean_apply_12(v___x_22108__overap_4748_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, lean_box(0));
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4779_; 
v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4752_ = v___x_4749_;
v_isShared_4753_ = v_isSharedCheck_4779_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4749_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4779_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v_fst_4754_; 
v_fst_4754_ = lean_ctor_get(v_a_4750_, 0);
if (lean_obj_tag(v_fst_4754_) == 0)
{
lean_object* v_snd_4755_; lean_object* v___x_4756_; lean_object* v_caches_4757_; lean_object* v_typeAnalysis_4758_; lean_object* v_target_4759_; uint8_t v_didChange_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4773_; 
v_snd_4755_ = lean_ctor_get(v_a_4750_, 1);
lean_inc(v_snd_4755_);
lean_dec(v_a_4750_);
v___x_4756_ = lean_st_ref_take(v_a_4677_);
v_caches_4757_ = lean_ctor_get(v___x_4756_, 0);
v_typeAnalysis_4758_ = lean_ctor_get(v___x_4756_, 1);
v_target_4759_ = lean_ctor_get(v___x_4756_, 2);
v_didChange_4760_ = lean_ctor_get_uint8(v___x_4756_, sizeof(void*)*4);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4773_ == 0)
{
lean_object* v_unused_4774_; 
v_unused_4774_ = lean_ctor_get(v___x_4756_, 3);
lean_dec(v_unused_4774_);
v___x_4762_ = v___x_4756_;
v_isShared_4763_ = v_isSharedCheck_4773_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_target_4759_);
lean_inc(v_typeAnalysis_4758_);
lean_inc(v_caches_4757_);
lean_dec(v___x_4756_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4773_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 3, v_snd_4755_);
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_caches_4757_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_typeAnalysis_4758_);
lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_target_4759_);
lean_ctor_set(v_reuseFailAlloc_4772_, 3, v_snd_4755_);
lean_ctor_set_uint8(v_reuseFailAlloc_4772_, sizeof(void*)*4, v_didChange_4760_);
v___x_4765_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
lean_object* v___x_4766_; uint8_t v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4770_; 
v___x_4766_ = lean_st_ref_put(v_a_4677_, v___x_4765_);
v___x_4767_ = 0;
v___x_4768_ = lean_box(v___x_4767_);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 0, v___x_4768_);
v___x_4770_ = v___x_4752_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4768_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
else
{
lean_object* v_val_4775_; lean_object* v___x_4777_; 
lean_inc_ref(v_fst_4754_);
lean_dec(v_a_4750_);
v_val_4775_ = lean_ctor_get(v_fst_4754_, 0);
lean_inc(v_val_4775_);
lean_dec_ref_known(v_fst_4754_, 1);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 0, v_val_4775_);
v___x_4777_ = v___x_4752_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_val_4775_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
v_a_4780_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4749_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4749_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4794_, lean_object* v_methods_4795_, lean_object* v_config_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_){
_start:
{
uint8_t v_cacheId_boxed_4809_; lean_object* v_res_4810_; 
v_cacheId_boxed_4809_ = lean_unbox(v_cacheId_4794_);
v_res_4810_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4809_, v_methods_4795_, v_config_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
lean_dec(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v___x_4817_; lean_object* v_env_4818_; lean_object* v___x_4819_; lean_object* v_toCold_4820_; lean_object* v_mctx_4821_; lean_object* v_lctx_4822_; lean_object* v_options_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4817_ = lean_st_ref_get(v___y_4815_);
v_env_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc_ref(v_env_4818_);
lean_dec(v___x_4817_);
v___x_4819_ = lean_st_ref_get(v___y_4813_);
v_toCold_4820_ = lean_ctor_get(v___y_4814_, 0);
v_mctx_4821_ = lean_ctor_get(v___x_4819_, 0);
lean_inc_ref(v_mctx_4821_);
lean_dec(v___x_4819_);
v_lctx_4822_ = lean_ctor_get(v___y_4812_, 2);
v_options_4823_ = lean_ctor_get(v_toCold_4820_, 2);
lean_inc_ref(v_options_4823_);
lean_inc_ref(v_lctx_4822_);
v___x_4824_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4824_, 0, v_env_4818_);
lean_ctor_set(v___x_4824_, 1, v_mctx_4821_);
lean_ctor_set(v___x_4824_, 2, v_lctx_4822_);
lean_ctor_set(v___x_4824_, 3, v_options_4823_);
v___x_4825_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
lean_ctor_set(v___x_4825_, 1, v_msgData_4811_);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
return v_res_4833_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4834_; double v___x_4835_; 
v___x_4834_ = lean_unsigned_to_nat(0u);
v___x_4835_ = lean_float_of_nat(v___x_4834_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4839_, lean_object* v_msg_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v_ref_4846_; lean_object* v___x_4847_; lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4893_; 
v_ref_4846_ = lean_ctor_get(v___y_4843_, 2);
v___x_4847_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4850_ = v___x_4847_;
v_isShared_4851_ = v_isSharedCheck_4893_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4847_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4893_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4852_; lean_object* v_traceState_4853_; lean_object* v_env_4854_; lean_object* v_nextMacroScope_4855_; lean_object* v_ngen_4856_; lean_object* v_auxDeclNGen_4857_; lean_object* v_cache_4858_; lean_object* v_recordedDeps_4859_; lean_object* v_messages_4860_; lean_object* v_infoState_4861_; lean_object* v_snapshotTasks_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4892_; 
v___x_4852_ = lean_st_ref_take(v___y_4844_);
v_traceState_4853_ = lean_ctor_get(v___x_4852_, 4);
v_env_4854_ = lean_ctor_get(v___x_4852_, 0);
v_nextMacroScope_4855_ = lean_ctor_get(v___x_4852_, 1);
v_ngen_4856_ = lean_ctor_get(v___x_4852_, 2);
v_auxDeclNGen_4857_ = lean_ctor_get(v___x_4852_, 3);
v_cache_4858_ = lean_ctor_get(v___x_4852_, 5);
v_recordedDeps_4859_ = lean_ctor_get(v___x_4852_, 6);
v_messages_4860_ = lean_ctor_get(v___x_4852_, 7);
v_infoState_4861_ = lean_ctor_get(v___x_4852_, 8);
v_snapshotTasks_4862_ = lean_ctor_get(v___x_4852_, 9);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4864_ = v___x_4852_;
v_isShared_4865_ = v_isSharedCheck_4892_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_snapshotTasks_4862_);
lean_inc(v_infoState_4861_);
lean_inc(v_messages_4860_);
lean_inc(v_recordedDeps_4859_);
lean_inc(v_cache_4858_);
lean_inc(v_traceState_4853_);
lean_inc(v_auxDeclNGen_4857_);
lean_inc(v_ngen_4856_);
lean_inc(v_nextMacroScope_4855_);
lean_inc(v_env_4854_);
lean_dec(v___x_4852_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4892_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
uint64_t v_tid_4866_; lean_object* v_traces_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4891_; 
v_tid_4866_ = lean_ctor_get_uint64(v_traceState_4853_, sizeof(void*)*1);
v_traces_4867_ = lean_ctor_get(v_traceState_4853_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v_traceState_4853_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4869_ = v_traceState_4853_;
v_isShared_4870_ = v_isSharedCheck_4891_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_traces_4867_);
lean_dec(v_traceState_4853_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4891_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; double v___x_4873_; uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4871_ = lean_box(0);
v___x_4872_ = lean_box(0);
v___x_4873_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4874_ = 0;
v___x_4875_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4876_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4876_, 0, v_cls_4839_);
lean_ctor_set(v___x_4876_, 1, v___x_4872_);
lean_ctor_set(v___x_4876_, 2, v___x_4875_);
lean_ctor_set_float(v___x_4876_, sizeof(void*)*3, v___x_4873_);
lean_ctor_set_float(v___x_4876_, sizeof(void*)*3 + 8, v___x_4873_);
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*3 + 16, v___x_4874_);
v___x_4877_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4878_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4876_);
lean_ctor_set(v___x_4878_, 1, v_a_4848_);
lean_ctor_set(v___x_4878_, 2, v___x_4877_);
lean_inc(v_ref_4846_);
v___x_4879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4879_, 0, v_ref_4846_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
v___x_4880_ = l_Lean_PersistentArray_push___redArg(v_traces_4867_, v___x_4879_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v___x_4880_);
v___x_4882_ = v___x_4869_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4880_);
lean_ctor_set_uint64(v_reuseFailAlloc_4890_, sizeof(void*)*1, v_tid_4866_);
v___x_4882_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4884_; 
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 4, v___x_4882_);
v___x_4884_ = v___x_4864_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_env_4854_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v_nextMacroScope_4855_);
lean_ctor_set(v_reuseFailAlloc_4889_, 2, v_ngen_4856_);
lean_ctor_set(v_reuseFailAlloc_4889_, 3, v_auxDeclNGen_4857_);
lean_ctor_set(v_reuseFailAlloc_4889_, 4, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4889_, 5, v_cache_4858_);
lean_ctor_set(v_reuseFailAlloc_4889_, 6, v_recordedDeps_4859_);
lean_ctor_set(v_reuseFailAlloc_4889_, 7, v_messages_4860_);
lean_ctor_set(v_reuseFailAlloc_4889_, 8, v_infoState_4861_);
lean_ctor_set(v_reuseFailAlloc_4889_, 9, v_snapshotTasks_4862_);
v___x_4884_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4885_ = lean_st_ref_put(v___y_4844_, v___x_4884_);
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v___x_4871_);
v___x_4887_ = v___x_4850_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4871_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4894_, lean_object* v_msg_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4894_, v_msg_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_4902_, lean_object* v___f_4903_, lean_object* v_____r_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v___x_4918_; lean_object* v_caches_4919_; lean_object* v_typeAnalysis_4920_; lean_object* v_target_4921_; lean_object* v_hypotheses_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4932_; 
v___x_4918_ = lean_st_ref_take(v___y_4907_);
v_caches_4919_ = lean_ctor_get(v___x_4918_, 0);
v_typeAnalysis_4920_ = lean_ctor_get(v___x_4918_, 1);
v_target_4921_ = lean_ctor_get(v___x_4918_, 2);
v_hypotheses_4922_ = lean_ctor_get(v___x_4918_, 3);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4924_ = v___x_4918_;
v_isShared_4925_ = v_isSharedCheck_4932_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_hypotheses_4922_);
lean_inc(v_target_4921_);
lean_inc(v_typeAnalysis_4920_);
lean_inc(v_caches_4919_);
lean_dec(v___x_4918_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4932_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4926_; lean_object* v___x_4928_; 
v___x_4926_ = lean_box(0);
if (v_isShared_4925_ == 0)
{
v___x_4928_ = v___x_4924_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_caches_4919_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_typeAnalysis_4920_);
lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_target_4921_);
lean_ctor_set(v_reuseFailAlloc_4931_, 3, v_hypotheses_4922_);
v___x_4928_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
lean_ctor_set_uint8(v___x_4928_, sizeof(void*)*4, v___x_4902_);
v___x_4929_ = lean_st_ref_put(v___y_4907_, v___x_4928_);
lean_inc(v___y_4916_);
lean_inc_ref(v___y_4915_);
lean_inc(v___y_4914_);
lean_inc_ref(v___y_4913_);
lean_inc(v___y_4912_);
lean_inc_ref(v___y_4911_);
lean_inc(v___y_4910_);
lean_inc_ref(v___y_4909_);
lean_inc(v___y_4908_);
lean_inc(v___y_4907_);
lean_inc_ref(v___y_4906_);
lean_inc(v___y_4905_);
v___x_4930_ = lean_apply_14(v___f_4903_, v___x_4926_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, lean_box(0));
return v___x_4930_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_4933_, lean_object* v___f_4934_, lean_object* v_____r_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
uint8_t v___x_35925__boxed_4949_; lean_object* v_res_4950_; 
v___x_35925__boxed_4949_ = lean_unbox(v___x_4933_);
v_res_4950_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35925__boxed_4949_, v___f_4934_, v_____r_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
lean_dec(v___y_4947_);
lean_dec_ref(v___y_4946_);
lean_dec(v___y_4945_);
lean_dec_ref(v___y_4944_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v___y_4939_);
lean_dec(v___y_4938_);
lean_dec_ref(v___y_4937_);
lean_dec(v___y_4936_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_4951_, lean_object* v_a_4952_, lean_object* v___x_4953_, lean_object* v_____r_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4968_ = lean_array_push(v_snd_4951_, v_a_4952_);
v___x_4969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4953_);
lean_ctor_set(v___x_4969_, 1, v___x_4968_);
v___x_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
v___x_4971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4971_, 0, v___x_4970_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_4972_ = _args[0];
lean_object* v_a_4973_ = _args[1];
lean_object* v___x_4974_ = _args[2];
lean_object* v_____r_4975_ = _args[3];
lean_object* v___y_4976_ = _args[4];
lean_object* v___y_4977_ = _args[5];
lean_object* v___y_4978_ = _args[6];
lean_object* v___y_4979_ = _args[7];
lean_object* v___y_4980_ = _args[8];
lean_object* v___y_4981_ = _args[9];
lean_object* v___y_4982_ = _args[10];
lean_object* v___y_4983_ = _args[11];
lean_object* v___y_4984_ = _args[12];
lean_object* v___y_4985_ = _args[13];
lean_object* v___y_4986_ = _args[14];
lean_object* v___y_4987_ = _args[15];
lean_object* v___y_4988_ = _args[16];
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_4972_, v_a_4973_, v___x_4974_, v_____r_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
lean_dec(v___y_4987_);
lean_dec_ref(v___y_4986_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
lean_dec(v___y_4976_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_4990_, lean_object* v___x_4991_, lean_object* v_methods_4992_, lean_object* v_config_4993_, lean_object* v_a_4994_, lean_object* v_b_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v___y_5010_; uint8_t v___x_5032_; 
v___x_5032_ = lean_nat_dec_lt(v_a_4994_, v_upperBound_4990_);
if (v___x_5032_ == 0)
{
lean_object* v___x_5033_; 
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v___x_5033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5033_, 0, v_b_4995_);
return v___x_5033_;
}
else
{
lean_object* v_snd_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5133_; 
v_snd_5034_ = lean_ctor_get(v_b_4995_, 1);
v_isSharedCheck_5133_ = !lean_is_exclusive(v_b_4995_);
if (v_isSharedCheck_5133_ == 0)
{
lean_object* v_unused_5134_; 
v_unused_5134_ = lean_ctor_get(v_b_4995_, 0);
lean_dec(v_unused_5134_);
v___x_5036_ = v_b_4995_;
v_isShared_5037_ = v_isSharedCheck_5133_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_snd_5034_);
lean_dec(v_b_4995_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5133_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v_type_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5038_ = lean_box(0);
v___x_5039_ = lean_array_fget_borrowed(v___x_4991_, v_a_4994_);
v___x_5040_ = lean_st_ref_take(v___y_4996_);
v___x_5041_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5042_ = lean_st_ref_put(v___y_4996_, v___x_5041_);
v_type_5043_ = lean_ctor_get(v___x_5039_, 1);
v___x_5044_ = lean_unsigned_to_nat(0u);
v___x_5045_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5044_);
lean_ctor_set(v___x_5045_, 1, v___x_5040_);
lean_ctor_set(v___x_5045_, 2, v___x_5041_);
lean_ctor_set(v___x_5045_, 3, v___x_5041_);
lean_inc_ref(v_type_5043_);
v___x_5046_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5046_, 0, v_type_5043_);
lean_inc_ref(v_config_4993_);
lean_inc_ref(v_methods_4992_);
v___x_5047_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5046_, v_methods_4992_, v_config_4993_, v___x_5045_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v_snd_5049_; lean_object* v_fst_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5124_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
v_snd_5049_ = lean_ctor_get(v_a_5048_, 1);
v_fst_5050_ = lean_ctor_get(v_a_5048_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v_a_5048_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5052_ = v_a_5048_;
v_isShared_5053_ = v_isSharedCheck_5124_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_snd_5049_);
lean_inc(v_fst_5050_);
lean_dec(v_a_5048_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5124_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v_persistentCache_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v_persistentCache_5054_ = lean_ctor_get(v_snd_5049_, 1);
lean_inc_ref(v_persistentCache_5054_);
lean_dec(v_snd_5049_);
v___x_5055_ = lean_st_ref_swap(v___y_4996_, v_persistentCache_5054_);
lean_dec(v___x_5055_);
lean_inc(v___x_5039_);
v___x_5056_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5039_, v_fst_5050_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v_a_5057_; lean_object* v_type_5058_; lean_object* v_value_5059_; uint8_t v___x_5060_; 
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v___x_5056_, 1);
v_type_5058_ = lean_ctor_get(v_a_5057_, 1);
v_value_5059_ = lean_ctor_get(v_a_5057_, 2);
lean_inc_ref(v_type_5058_);
v___x_5060_ = l_Lean_Expr_isFalse(v_type_5058_);
if (v___x_5060_ == 0)
{
lean_object* v___f_5061_; uint8_t v___x_5091_; 
lean_del_object(v___x_5052_);
lean_inc(v_a_5057_);
lean_inc(v_snd_5034_);
v___f_5061_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5061_, 0, v_snd_5034_);
lean_closure_set(v___f_5061_, 1, v_a_5057_);
lean_closure_set(v___f_5061_, 2, v___x_5038_);
v___x_5091_ = lean_expr_eqv(v_type_5043_, v_type_5058_);
if (v___x_5091_ == 0)
{
lean_inc_ref(v_type_5058_);
lean_dec(v_a_5057_);
lean_dec(v_snd_5034_);
goto v___jp_5065_;
}
else
{
if (v___x_5060_ == 0)
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_dec_ref(v___f_5061_);
lean_del_object(v___x_5036_);
v___x_5092_ = lean_box(0);
v___x_5093_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5034_, v_a_5057_, v___x_5038_, v___x_5092_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
v___y_5010_ = v___x_5093_;
goto v___jp_5009_;
}
else
{
lean_inc_ref(v_type_5058_);
lean_dec(v_a_5057_);
lean_dec(v_snd_5034_);
goto v___jp_5065_;
}
}
v___jp_5062_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_box(0);
v___x_5064_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5032_, v___f_5061_, v___x_5063_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
v___y_5010_ = v___x_5064_;
goto v___jp_5009_;
}
v___jp_5065_:
{
lean_object* v_toCold_5066_; lean_object* v_options_5067_; uint8_t v_hasTrace_5068_; 
v_toCold_5066_ = lean_ctor_get(v___y_5006_, 0);
v_options_5067_ = lean_ctor_get(v_toCold_5066_, 2);
v_hasTrace_5068_ = lean_ctor_get_uint8(v_options_5067_, sizeof(void*)*1);
if (v_hasTrace_5068_ == 0)
{
lean_dec_ref(v_type_5058_);
lean_del_object(v___x_5036_);
goto v___jp_5062_;
}
else
{
lean_object* v_inheritedTraceOptions_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; uint8_t v___x_5072_; 
v_inheritedTraceOptions_5069_ = lean_ctor_get(v_toCold_5066_, 11);
v___x_5070_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5071_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5069_, v_options_5067_, v___x_5071_);
if (v___x_5072_ == 0)
{
lean_dec_ref(v_type_5058_);
lean_del_object(v___x_5036_);
goto v___jp_5062_;
}
else
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; 
lean_inc_ref(v_type_5043_);
v___x_5073_ = l_Lean_MessageData_ofExpr(v_type_5043_);
v___x_5074_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5037_ == 0)
{
lean_ctor_set_tag(v___x_5036_, 7);
lean_ctor_set(v___x_5036_, 1, v___x_5074_);
lean_ctor_set(v___x_5036_, 0, v___x_5073_);
v___x_5076_ = v___x_5036_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5073_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v___x_5074_);
v___x_5076_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5077_ = l_Lean_MessageData_ofExpr(v_type_5058_);
v___x_5078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5078_, 0, v___x_5076_);
lean_ctor_set(v___x_5078_, 1, v___x_5077_);
v___x_5079_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5070_, v___x_5078_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v___x_5081_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref_known(v___x_5079_, 1);
v___x_5081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5032_, v___f_5061_, v_a_5080_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
v___y_5010_ = v___x_5081_;
goto v___jp_5009_;
}
else
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
lean_dec_ref(v___f_5061_);
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v_a_5082_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5084_ = v___x_5079_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5079_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
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
lean_object* v___x_5094_; 
lean_inc_ref(v_value_5059_);
lean_dec(v_a_5057_);
lean_del_object(v___x_5036_);
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v___x_5094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5059_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5106_; 
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5106_ == 0)
{
lean_object* v_unused_5107_; 
v_unused_5107_ = lean_ctor_get(v___x_5094_, 0);
lean_dec(v_unused_5107_);
v___x_5096_ = v___x_5094_;
v_isShared_5097_ = v_isSharedCheck_5106_;
goto v_resetjp_5095_;
}
else
{
lean_dec(v___x_5094_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5106_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5101_; 
v___x_5098_ = lean_box(v___x_5032_);
v___x_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5098_);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 1, v_snd_5034_);
lean_ctor_set(v___x_5052_, 0, v___x_5099_);
v___x_5101_ = v___x_5052_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v___x_5099_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v_snd_5034_);
v___x_5101_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
lean_object* v___x_5103_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 0, v___x_5101_);
v___x_5103_ = v___x_5096_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5101_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
else
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5115_; 
lean_del_object(v___x_5052_);
lean_dec(v_snd_5034_);
v_a_5108_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5110_ = v___x_5094_;
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_5094_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_del_object(v___x_5052_);
lean_del_object(v___x_5036_);
lean_dec(v_snd_5034_);
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v_a_5116_ = lean_ctor_get(v___x_5056_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5056_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5056_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
lean_del_object(v___x_5036_);
lean_dec(v_snd_5034_);
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v_a_5125_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5047_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5047_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
}
v___jp_5009_:
{
if (lean_obj_tag(v___y_5010_) == 0)
{
lean_object* v_a_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5023_; 
v_a_5011_ = lean_ctor_get(v___y_5010_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___y_5010_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5013_ = v___y_5010_;
v_isShared_5014_ = v_isSharedCheck_5023_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_a_5011_);
lean_dec(v___y_5010_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5023_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
if (lean_obj_tag(v_a_5011_) == 0)
{
lean_object* v_a_5015_; lean_object* v___x_5017_; 
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v_a_5015_ = lean_ctor_get(v_a_5011_, 0);
lean_inc(v_a_5015_);
lean_dec_ref_known(v_a_5011_, 1);
if (v_isShared_5014_ == 0)
{
lean_ctor_set(v___x_5013_, 0, v_a_5015_);
v___x_5017_ = v___x_5013_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5015_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
lean_del_object(v___x_5013_);
v_a_5019_ = lean_ctor_get(v_a_5011_, 0);
lean_inc(v_a_5019_);
lean_dec_ref_known(v_a_5011_, 1);
v___x_5020_ = lean_unsigned_to_nat(1u);
v___x_5021_ = lean_nat_add(v_a_4994_, v___x_5020_);
lean_dec(v_a_4994_);
v_a_4994_ = v___x_5021_;
v_b_4995_ = v_a_5019_;
goto _start;
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v_a_5024_ = lean_ctor_get(v___y_5010_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___y_5010_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___y_5010_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___y_5010_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5135_ = _args[0];
lean_object* v___x_5136_ = _args[1];
lean_object* v_methods_5137_ = _args[2];
lean_object* v_config_5138_ = _args[3];
lean_object* v_a_5139_ = _args[4];
lean_object* v_b_5140_ = _args[5];
lean_object* v___y_5141_ = _args[6];
lean_object* v___y_5142_ = _args[7];
lean_object* v___y_5143_ = _args[8];
lean_object* v___y_5144_ = _args[9];
lean_object* v___y_5145_ = _args[10];
lean_object* v___y_5146_ = _args[11];
lean_object* v___y_5147_ = _args[12];
lean_object* v___y_5148_ = _args[13];
lean_object* v___y_5149_ = _args[14];
lean_object* v___y_5150_ = _args[15];
lean_object* v___y_5151_ = _args[16];
lean_object* v___y_5152_ = _args[17];
lean_object* v___y_5153_ = _args[18];
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5135_, v___x_5136_, v_methods_5137_, v_config_5138_, v_a_5139_, v_b_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___x_5136_);
lean_dec(v_upperBound_5135_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_5155_, lean_object* v_config_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_){
_start:
{
lean_object* v___x_5170_; lean_object* v_hypotheses_5171_; lean_object* v___x_5172_; lean_object* v_newHyps_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; 
v___x_5170_ = lean_st_ref_get(v_a_5159_);
v_hypotheses_5171_ = lean_ctor_get(v___x_5170_, 3);
lean_inc_ref(v_hypotheses_5171_);
lean_dec(v___x_5170_);
v___x_5172_ = lean_array_get_size(v_hypotheses_5171_);
v_newHyps_5173_ = lean_mk_empty_array_with_capacity(v___x_5172_);
v___x_5174_ = lean_unsigned_to_nat(0u);
v___x_5175_ = lean_box(0);
v___x_5176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5175_);
lean_ctor_set(v___x_5176_, 1, v_newHyps_5173_);
v___x_5177_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_5172_, v_hypotheses_5171_, v_methods_5155_, v_config_5156_, v___x_5174_, v___x_5176_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
lean_dec_ref(v_hypotheses_5171_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5207_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5180_ = v___x_5177_;
v_isShared_5181_ = v_isSharedCheck_5207_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5177_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5207_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v_fst_5182_; 
v_fst_5182_ = lean_ctor_get(v_a_5178_, 0);
if (lean_obj_tag(v_fst_5182_) == 0)
{
lean_object* v_snd_5183_; lean_object* v___x_5184_; lean_object* v_caches_5185_; lean_object* v_typeAnalysis_5186_; lean_object* v_target_5187_; uint8_t v_didChange_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5201_; 
v_snd_5183_ = lean_ctor_get(v_a_5178_, 1);
lean_inc(v_snd_5183_);
lean_dec(v_a_5178_);
v___x_5184_ = lean_st_ref_take(v_a_5159_);
v_caches_5185_ = lean_ctor_get(v___x_5184_, 0);
v_typeAnalysis_5186_ = lean_ctor_get(v___x_5184_, 1);
v_target_5187_ = lean_ctor_get(v___x_5184_, 2);
v_didChange_5188_ = lean_ctor_get_uint8(v___x_5184_, sizeof(void*)*4);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5201_ == 0)
{
lean_object* v_unused_5202_; 
v_unused_5202_ = lean_ctor_get(v___x_5184_, 3);
lean_dec(v_unused_5202_);
v___x_5190_ = v___x_5184_;
v_isShared_5191_ = v_isSharedCheck_5201_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_target_5187_);
lean_inc(v_typeAnalysis_5186_);
lean_inc(v_caches_5185_);
lean_dec(v___x_5184_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5201_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
lean_ctor_set(v___x_5190_, 3, v_snd_5183_);
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_caches_5185_);
lean_ctor_set(v_reuseFailAlloc_5200_, 1, v_typeAnalysis_5186_);
lean_ctor_set(v_reuseFailAlloc_5200_, 2, v_target_5187_);
lean_ctor_set(v_reuseFailAlloc_5200_, 3, v_snd_5183_);
lean_ctor_set_uint8(v_reuseFailAlloc_5200_, sizeof(void*)*4, v_didChange_5188_);
v___x_5193_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
lean_object* v___x_5194_; uint8_t v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5198_; 
v___x_5194_ = lean_st_ref_put(v_a_5159_, v___x_5193_);
v___x_5195_ = 0;
v___x_5196_ = lean_box(v___x_5195_);
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 0, v___x_5196_);
v___x_5198_ = v___x_5180_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v___x_5196_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
else
{
lean_object* v_val_5203_; lean_object* v___x_5205_; 
lean_inc_ref(v_fst_5182_);
lean_dec(v_a_5178_);
v_val_5203_ = lean_ctor_get(v_fst_5182_, 0);
lean_inc(v_val_5203_);
lean_dec_ref_known(v_fst_5182_, 1);
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 0, v_val_5203_);
v___x_5205_ = v___x_5180_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_val_5203_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
v_a_5208_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5177_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5177_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_5216_, lean_object* v_config_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5216_, v_config_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_);
lean_dec(v_a_5229_);
lean_dec_ref(v_a_5228_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
lean_dec(v_a_5221_);
lean_dec(v_a_5220_);
lean_dec_ref(v_a_5219_);
lean_dec(v_a_5218_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_5232_, lean_object* v_msg_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5232_, v_msg_5233_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_5248_, lean_object* v_msg_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_){
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5248_, v_msg_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_upperBound_5264_, lean_object* v___x_5265_, lean_object* v_methods_5266_, lean_object* v_config_5267_, lean_object* v_inst_5268_, lean_object* v_R_5269_, lean_object* v_a_5270_, lean_object* v_b_5271_, lean_object* v_c_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5264_, v___x_5265_, v_methods_5266_, v_config_5267_, v_a_5270_, v_b_5271_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5287_ = _args[0];
lean_object* v___x_5288_ = _args[1];
lean_object* v_methods_5289_ = _args[2];
lean_object* v_config_5290_ = _args[3];
lean_object* v_inst_5291_ = _args[4];
lean_object* v_R_5292_ = _args[5];
lean_object* v_a_5293_ = _args[6];
lean_object* v_b_5294_ = _args[7];
lean_object* v_c_5295_ = _args[8];
lean_object* v___y_5296_ = _args[9];
lean_object* v___y_5297_ = _args[10];
lean_object* v___y_5298_ = _args[11];
lean_object* v___y_5299_ = _args[12];
lean_object* v___y_5300_ = _args[13];
lean_object* v___y_5301_ = _args[14];
lean_object* v___y_5302_ = _args[15];
lean_object* v___y_5303_ = _args[16];
lean_object* v___y_5304_ = _args[17];
lean_object* v___y_5305_ = _args[18];
lean_object* v___y_5306_ = _args[19];
lean_object* v___y_5307_ = _args[20];
lean_object* v___y_5308_ = _args[21];
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5287_, v___x_5288_, v_methods_5289_, v_config_5290_, v_inst_5291_, v_R_5292_, v_a_5293_, v_b_5294_, v_c_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec(v___y_5298_);
lean_dec_ref(v___y_5297_);
lean_dec(v___y_5296_);
lean_dec_ref(v___x_5288_);
lean_dec(v_upperBound_5287_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_5310_, lean_object* v_config_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_){
_start:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; 
v___x_5324_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5325_ = lean_st_mk_ref(v___x_5324_);
v___x_5326_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5310_, v_config_5311_, v___x_5325_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5335_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5329_ = v___x_5326_;
v_isShared_5330_ = v_isSharedCheck_5335_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5335_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5331_; lean_object* v___x_5333_; 
v___x_5331_ = lean_st_ref_get(v___x_5325_);
lean_dec(v___x_5325_);
lean_dec(v___x_5331_);
if (v_isShared_5330_ == 0)
{
v___x_5333_ = v___x_5329_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5327_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
else
{
lean_dec(v___x_5325_);
return v___x_5326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_5336_, lean_object* v_config_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5336_, v_config_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_);
lean_dec(v_a_5348_);
lean_dec_ref(v_a_5347_);
lean_dec(v_a_5346_);
lean_dec_ref(v_a_5345_);
lean_dec(v_a_5344_);
lean_dec_ref(v_a_5343_);
lean_dec(v_a_5342_);
lean_dec_ref(v_a_5341_);
lean_dec(v_a_5340_);
lean_dec(v_a_5339_);
lean_dec_ref(v_a_5338_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_5351_, lean_object* v_msg_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
lean_object* v_ref_5358_; lean_object* v___x_5359_; lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5405_; 
v_ref_5358_ = lean_ctor_get(v___y_5355_, 2);
v___x_5359_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_);
v_a_5360_ = lean_ctor_get(v___x_5359_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5362_ = v___x_5359_;
v_isShared_5363_ = v_isSharedCheck_5405_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5359_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5405_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5364_; lean_object* v_traceState_5365_; lean_object* v_env_5366_; lean_object* v_nextMacroScope_5367_; lean_object* v_ngen_5368_; lean_object* v_auxDeclNGen_5369_; lean_object* v_cache_5370_; lean_object* v_recordedDeps_5371_; lean_object* v_messages_5372_; lean_object* v_infoState_5373_; lean_object* v_snapshotTasks_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5404_; 
v___x_5364_ = lean_st_ref_take(v___y_5356_);
v_traceState_5365_ = lean_ctor_get(v___x_5364_, 4);
v_env_5366_ = lean_ctor_get(v___x_5364_, 0);
v_nextMacroScope_5367_ = lean_ctor_get(v___x_5364_, 1);
v_ngen_5368_ = lean_ctor_get(v___x_5364_, 2);
v_auxDeclNGen_5369_ = lean_ctor_get(v___x_5364_, 3);
v_cache_5370_ = lean_ctor_get(v___x_5364_, 5);
v_recordedDeps_5371_ = lean_ctor_get(v___x_5364_, 6);
v_messages_5372_ = lean_ctor_get(v___x_5364_, 7);
v_infoState_5373_ = lean_ctor_get(v___x_5364_, 8);
v_snapshotTasks_5374_ = lean_ctor_get(v___x_5364_, 9);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5376_ = v___x_5364_;
v_isShared_5377_ = v_isSharedCheck_5404_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_snapshotTasks_5374_);
lean_inc(v_infoState_5373_);
lean_inc(v_messages_5372_);
lean_inc(v_recordedDeps_5371_);
lean_inc(v_cache_5370_);
lean_inc(v_traceState_5365_);
lean_inc(v_auxDeclNGen_5369_);
lean_inc(v_ngen_5368_);
lean_inc(v_nextMacroScope_5367_);
lean_inc(v_env_5366_);
lean_dec(v___x_5364_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5404_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
uint64_t v_tid_5378_; lean_object* v_traces_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5403_; 
v_tid_5378_ = lean_ctor_get_uint64(v_traceState_5365_, sizeof(void*)*1);
v_traces_5379_ = lean_ctor_get(v_traceState_5365_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v_traceState_5365_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5381_ = v_traceState_5365_;
v_isShared_5382_ = v_isSharedCheck_5403_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_traces_5379_);
lean_dec(v_traceState_5365_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5403_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; double v___x_5385_; uint8_t v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5394_; 
v___x_5383_ = lean_box(0);
v___x_5384_ = lean_box(0);
v___x_5385_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5386_ = 0;
v___x_5387_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5388_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5388_, 0, v_cls_5351_);
lean_ctor_set(v___x_5388_, 1, v___x_5384_);
lean_ctor_set(v___x_5388_, 2, v___x_5387_);
lean_ctor_set_float(v___x_5388_, sizeof(void*)*3, v___x_5385_);
lean_ctor_set_float(v___x_5388_, sizeof(void*)*3 + 8, v___x_5385_);
lean_ctor_set_uint8(v___x_5388_, sizeof(void*)*3 + 16, v___x_5386_);
v___x_5389_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5390_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5390_, 0, v___x_5388_);
lean_ctor_set(v___x_5390_, 1, v_a_5360_);
lean_ctor_set(v___x_5390_, 2, v___x_5389_);
lean_inc(v_ref_5358_);
v___x_5391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5391_, 0, v_ref_5358_);
lean_ctor_set(v___x_5391_, 1, v___x_5390_);
v___x_5392_ = l_Lean_PersistentArray_push___redArg(v_traces_5379_, v___x_5391_);
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 0, v___x_5392_);
v___x_5394_ = v___x_5381_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5392_);
lean_ctor_set_uint64(v_reuseFailAlloc_5402_, sizeof(void*)*1, v_tid_5378_);
v___x_5394_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5396_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 4, v___x_5394_);
v___x_5396_ = v___x_5376_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_env_5366_);
lean_ctor_set(v_reuseFailAlloc_5401_, 1, v_nextMacroScope_5367_);
lean_ctor_set(v_reuseFailAlloc_5401_, 2, v_ngen_5368_);
lean_ctor_set(v_reuseFailAlloc_5401_, 3, v_auxDeclNGen_5369_);
lean_ctor_set(v_reuseFailAlloc_5401_, 4, v___x_5394_);
lean_ctor_set(v_reuseFailAlloc_5401_, 5, v_cache_5370_);
lean_ctor_set(v_reuseFailAlloc_5401_, 6, v_recordedDeps_5371_);
lean_ctor_set(v_reuseFailAlloc_5401_, 7, v_messages_5372_);
lean_ctor_set(v_reuseFailAlloc_5401_, 8, v_infoState_5373_);
lean_ctor_set(v_reuseFailAlloc_5401_, 9, v_snapshotTasks_5374_);
v___x_5396_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
lean_object* v___x_5397_; lean_object* v___x_5399_; 
v___x_5397_ = lean_st_ref_put(v___y_5356_, v___x_5396_);
if (v_isShared_5363_ == 0)
{
lean_ctor_set(v___x_5362_, 0, v___x_5383_);
v___x_5399_ = v___x_5362_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5383_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5406_, lean_object* v_msg_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_){
_start:
{
lean_object* v_res_5413_; 
v_res_5413_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5406_, v_msg_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
lean_dec(v___y_5411_);
lean_dec_ref(v___y_5410_);
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
return v_res_5413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5414_, lean_object* v___x_5415_, lean_object* v_methods_5416_, lean_object* v_config_5417_, lean_object* v_a_5418_, lean_object* v_b_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v___y_5434_; uint8_t v___x_5456_; 
v___x_5456_ = lean_nat_dec_lt(v_a_5418_, v_upperBound_5414_);
if (v___x_5456_ == 0)
{
lean_object* v___x_5457_; 
lean_dec(v_a_5418_);
lean_dec_ref(v_config_5417_);
lean_dec_ref(v_methods_5416_);
v___x_5457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5457_, 0, v_b_5419_);
return v___x_5457_;
}
else
{
lean_object* v_snd_5458_; lean_object* v___x_5460_; uint8_t v_isShared_5461_; uint8_t v_isSharedCheck_5564_; 
v_snd_5458_ = lean_ctor_get(v_b_5419_, 1);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_b_5419_);
if (v_isSharedCheck_5564_ == 0)
{
lean_object* v_unused_5565_; 
v_unused_5565_ = lean_ctor_get(v_b_5419_, 0);
lean_dec(v_unused_5565_);
v___x_5460_ = v_b_5419_;
v_isShared_5461_ = v_isSharedCheck_5564_;
goto v_resetjp_5459_;
}
else
{
lean_inc(v_snd_5458_);
lean_dec(v_b_5419_);
v___x_5460_ = lean_box(0);
v_isShared_5461_ = v_isSharedCheck_5564_;
goto v_resetjp_5459_;
}
v_resetjp_5459_:
{
lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v_type_5467_; lean_object* v___x_5468_; lean_object* v___x_5470_; 
v___x_5462_ = lean_box(0);
v___x_5463_ = lean_array_fget_borrowed(v___x_5415_, v_a_5418_);
v___x_5464_ = lean_st_ref_take(v___y_5420_);
v___x_5465_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5466_ = lean_st_ref_put(v___y_5420_, v___x_5465_);
v_type_5467_ = lean_ctor_get(v___x_5463_, 1);
v___x_5468_ = lean_unsigned_to_nat(0u);
if (v_isShared_5461_ == 0)
{
lean_ctor_set(v___x_5460_, 1, v___x_5464_);
lean_ctor_set(v___x_5460_, 0, v___x_5468_);
v___x_5470_ = v___x_5460_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v___x_5468_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v___x_5464_);
v___x_5470_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
lean_inc_ref(v_type_5467_);
v___x_5471_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5471_, 0, v_type_5467_);
lean_inc_ref(v_config_5417_);
lean_inc_ref(v_methods_5416_);
v___x_5472_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5471_, v_methods_5416_, v_config_5417_, v___x_5470_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
if (lean_obj_tag(v___x_5472_) == 0)
{
lean_object* v_a_5473_; lean_object* v_snd_5474_; lean_object* v_fst_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5554_; 
v_a_5473_ = lean_ctor_get(v___x_5472_, 0);
lean_inc(v_a_5473_);
lean_dec_ref_known(v___x_5472_, 1);
v_snd_5474_ = lean_ctor_get(v_a_5473_, 1);
v_fst_5475_ = lean_ctor_get(v_a_5473_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v_a_5473_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5477_ = v_a_5473_;
v_isShared_5478_ = v_isSharedCheck_5554_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_snd_5474_);
lean_inc(v_fst_5475_);
lean_dec(v_a_5473_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5554_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v_cache_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5552_; 
v_cache_5479_ = lean_ctor_get(v_snd_5474_, 1);
v_isSharedCheck_5552_ = !lean_is_exclusive(v_snd_5474_);
if (v_isSharedCheck_5552_ == 0)
{
lean_object* v_unused_5553_; 
v_unused_5553_ = lean_ctor_get(v_snd_5474_, 0);
lean_dec(v_unused_5553_);
v___x_5481_ = v_snd_5474_;
v_isShared_5482_ = v_isSharedCheck_5552_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_cache_5479_);
lean_dec(v_snd_5474_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5552_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5483_ = lean_st_ref_swap(v___y_5420_, v_cache_5479_);
lean_dec(v___x_5483_);
lean_inc(v___x_5463_);
v___x_5484_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5463_, v_fst_5475_);
lean_dec(v_fst_5475_);
if (lean_obj_tag(v___x_5484_) == 0)
{
lean_object* v_a_5485_; lean_object* v_type_5486_; lean_object* v_value_5487_; uint8_t v___x_5488_; 
v_a_5485_ = lean_ctor_get(v___x_5484_, 0);
lean_inc(v_a_5485_);
lean_dec_ref_known(v___x_5484_, 1);
v_type_5486_ = lean_ctor_get(v_a_5485_, 1);
v_value_5487_ = lean_ctor_get(v_a_5485_, 2);
lean_inc_ref(v_type_5486_);
v___x_5488_ = l_Lean_Expr_isFalse(v_type_5486_);
if (v___x_5488_ == 0)
{
lean_object* v___f_5489_; uint8_t v___x_5519_; 
lean_del_object(v___x_5477_);
lean_inc(v_a_5485_);
lean_inc(v_snd_5458_);
v___f_5489_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5489_, 0, v_snd_5458_);
lean_closure_set(v___f_5489_, 1, v_a_5485_);
lean_closure_set(v___f_5489_, 2, v___x_5462_);
v___x_5519_ = lean_expr_eqv(v_type_5467_, v_type_5486_);
if (v___x_5519_ == 0)
{
lean_inc_ref(v_type_5486_);
lean_dec(v_a_5485_);
lean_dec(v_snd_5458_);
goto v___jp_5493_;
}
else
{
if (v___x_5488_ == 0)
{
lean_object* v___x_5520_; lean_object* v___x_5521_; 
lean_dec_ref(v___f_5489_);
lean_del_object(v___x_5481_);
v___x_5520_ = lean_box(0);
v___x_5521_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5458_, v_a_5485_, v___x_5462_, v___x_5520_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
v___y_5434_ = v___x_5521_;
goto v___jp_5433_;
}
else
{
lean_inc_ref(v_type_5486_);
lean_dec(v_a_5485_);
lean_dec(v_snd_5458_);
goto v___jp_5493_;
}
}
v___jp_5490_:
{
lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5491_ = lean_box(0);
v___x_5492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5456_, v___f_5489_, v___x_5491_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
v___y_5434_ = v___x_5492_;
goto v___jp_5433_;
}
v___jp_5493_:
{
lean_object* v_toCold_5494_; lean_object* v_options_5495_; uint8_t v_hasTrace_5496_; 
v_toCold_5494_ = lean_ctor_get(v___y_5430_, 0);
v_options_5495_ = lean_ctor_get(v_toCold_5494_, 2);
v_hasTrace_5496_ = lean_ctor_get_uint8(v_options_5495_, sizeof(void*)*1);
if (v_hasTrace_5496_ == 0)
{
lean_dec_ref(v_type_5486_);
lean_del_object(v___x_5481_);
goto v___jp_5490_;
}
else
{
lean_object* v_inheritedTraceOptions_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; uint8_t v___x_5500_; 
v_inheritedTraceOptions_5497_ = lean_ctor_get(v_toCold_5494_, 11);
v___x_5498_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5499_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5500_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5497_, v_options_5495_, v___x_5499_);
if (v___x_5500_ == 0)
{
lean_dec_ref(v_type_5486_);
lean_del_object(v___x_5481_);
goto v___jp_5490_;
}
else
{
lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5504_; 
lean_inc_ref(v_type_5467_);
v___x_5501_ = l_Lean_MessageData_ofExpr(v_type_5467_);
v___x_5502_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5482_ == 0)
{
lean_ctor_set_tag(v___x_5481_, 7);
lean_ctor_set(v___x_5481_, 1, v___x_5502_);
lean_ctor_set(v___x_5481_, 0, v___x_5501_);
v___x_5504_ = v___x_5481_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5501_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5502_);
v___x_5504_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; 
v___x_5505_ = l_Lean_MessageData_ofExpr(v_type_5486_);
v___x_5506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5506_, 0, v___x_5504_);
lean_ctor_set(v___x_5506_, 1, v___x_5505_);
v___x_5507_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5498_, v___x_5506_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
if (lean_obj_tag(v___x_5507_) == 0)
{
lean_object* v_a_5508_; lean_object* v___x_5509_; 
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc(v_a_5508_);
lean_dec_ref_known(v___x_5507_, 1);
v___x_5509_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5456_, v___f_5489_, v_a_5508_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
v___y_5434_ = v___x_5509_;
goto v___jp_5433_;
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
lean_dec_ref(v___f_5489_);
lean_dec(v_a_5418_);
lean_dec_ref(v_config_5417_);
lean_dec_ref(v_methods_5416_);
v_a_5510_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5507_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5507_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
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
lean_object* v___x_5522_; 
lean_inc_ref(v_value_5487_);
lean_dec(v_a_5485_);
lean_del_object(v___x_5481_);
lean_dec(v_a_5418_);
lean_dec_ref(v_config_5417_);
lean_dec_ref(v_methods_5416_);
v___x_5522_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5487_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
if (lean_obj_tag(v___x_5522_) == 0)
{
lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5534_; 
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5522_);
if (v_isSharedCheck_5534_ == 0)
{
lean_object* v_unused_5535_; 
v_unused_5535_ = lean_ctor_get(v___x_5522_, 0);
lean_dec(v_unused_5535_);
v___x_5524_ = v___x_5522_;
v_isShared_5525_ = v_isSharedCheck_5534_;
goto v_resetjp_5523_;
}
else
{
lean_dec(v___x_5522_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5534_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5529_; 
v___x_5526_ = lean_box(v___x_5456_);
v___x_5527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5527_, 0, v___x_5526_);
if (v_isShared_5478_ == 0)
{
lean_ctor_set(v___x_5477_, 1, v_snd_5458_);
lean_ctor_set(v___x_5477_, 0, v___x_5527_);
v___x_5529_ = v___x_5477_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v_snd_5458_);
v___x_5529_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
lean_object* v___x_5531_; 
if (v_isShared_5525_ == 0)
{
lean_ctor_set(v___x_5524_, 0, v___x_5529_);
v___x_5531_ = v___x_5524_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v___x_5529_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
else
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5543_; 
lean_del_object(v___x_5477_);
lean_dec(v_snd_5458_);
v_a_5536_ = lean_ctor_get(v___x_5522_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5522_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5538_ = v___x_5522_;
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5522_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
if (v_isShared_5539_ == 0)
{
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_a_5536_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
}
else
{
lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5551_; 
lean_del_object(v___x_5481_);
lean_del_object(v___x_5477_);
lean_dec(v_snd_5458_);
lean_dec(v_a_5418_);
lean_dec_ref(v_config_5417_);
lean_dec_ref(v_methods_5416_);
v_a_5544_ = lean_ctor_get(v___x_5484_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5484_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5546_ = v___x_5484_;
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5484_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5549_; 
if (v_isShared_5547_ == 0)
{
v___x_5549_ = v___x_5546_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
return v___x_5549_;
}
}
}
}
}
}
else
{
lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
lean_dec(v_snd_5458_);
lean_dec(v_a_5418_);
lean_dec_ref(v_config_5417_);
lean_dec_ref(v_methods_5416_);
v_a_5555_ = lean_ctor_get(v___x_5472_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5557_ = v___x_5472_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_dec(v___x_5472_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
}
}
v___jp_5433_:
{
if (lean_obj_tag(v___y_5434_) == 0)
{
lean_object* v_a_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5447_; 
v_a_5435_ = lean_ctor_get(v___y_5434_, 0);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___y_5434_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5437_ = v___y_5434_;
v_isShared_5438_ = v_isSharedCheck_5447_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_a_5435_);
lean_dec(v___y_5434_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5447_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
if (lean_obj_tag(v_a_5435_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5441_; 
lean_dec(v_a_5418_);
lean_dec_ref(v_config_5417_);
lean_dec_ref(v_methods_5416_);
v_a_5439_ = lean_ctor_get(v_a_5435_, 0);
lean_inc(v_a_5439_);
lean_dec_ref_known(v_a_5435_, 1);
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 0, v_a_5439_);
v___x_5441_ = v___x_5437_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5439_);
v___x_5441_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
return v___x_5441_;
}
}
else
{
lean_object* v_a_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
lean_del_object(v___x_5437_);
v_a_5443_ = lean_ctor_get(v_a_5435_, 0);
lean_inc(v_a_5443_);
lean_dec_ref_known(v_a_5435_, 1);
v___x_5444_ = lean_unsigned_to_nat(1u);
v___x_5445_ = lean_nat_add(v_a_5418_, v___x_5444_);
lean_dec(v_a_5418_);
v_a_5418_ = v___x_5445_;
v_b_5419_ = v_a_5443_;
goto _start;
}
}
}
else
{
lean_object* v_a_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5455_; 
lean_dec(v_a_5418_);
lean_dec_ref(v_config_5417_);
lean_dec_ref(v_methods_5416_);
v_a_5448_ = lean_ctor_get(v___y_5434_, 0);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___y_5434_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5450_ = v___y_5434_;
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_a_5448_);
lean_dec(v___y_5434_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
lean_object* v___x_5453_; 
if (v_isShared_5451_ == 0)
{
v___x_5453_ = v___x_5450_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_a_5448_);
v___x_5453_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
return v___x_5453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5566_ = _args[0];
lean_object* v___x_5567_ = _args[1];
lean_object* v_methods_5568_ = _args[2];
lean_object* v_config_5569_ = _args[3];
lean_object* v_a_5570_ = _args[4];
lean_object* v_b_5571_ = _args[5];
lean_object* v___y_5572_ = _args[6];
lean_object* v___y_5573_ = _args[7];
lean_object* v___y_5574_ = _args[8];
lean_object* v___y_5575_ = _args[9];
lean_object* v___y_5576_ = _args[10];
lean_object* v___y_5577_ = _args[11];
lean_object* v___y_5578_ = _args[12];
lean_object* v___y_5579_ = _args[13];
lean_object* v___y_5580_ = _args[14];
lean_object* v___y_5581_ = _args[15];
lean_object* v___y_5582_ = _args[16];
lean_object* v___y_5583_ = _args[17];
lean_object* v___y_5584_ = _args[18];
_start:
{
lean_object* v_res_5585_; 
v_res_5585_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5566_, v___x_5567_, v_methods_5568_, v_config_5569_, v_a_5570_, v_b_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_);
lean_dec(v___y_5583_);
lean_dec_ref(v___y_5582_);
lean_dec(v___y_5581_);
lean_dec_ref(v___y_5580_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec(v___y_5572_);
lean_dec_ref(v___x_5567_);
lean_dec(v_upperBound_5566_);
return v_res_5585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5586_, lean_object* v_config_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_){
_start:
{
lean_object* v___x_5601_; lean_object* v_hypotheses_5602_; lean_object* v___x_5603_; lean_object* v_newHyps_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; 
v___x_5601_ = lean_st_ref_get(v_a_5590_);
v_hypotheses_5602_ = lean_ctor_get(v___x_5601_, 3);
lean_inc_ref(v_hypotheses_5602_);
lean_dec(v___x_5601_);
v___x_5603_ = lean_array_get_size(v_hypotheses_5602_);
v_newHyps_5604_ = lean_mk_empty_array_with_capacity(v___x_5603_);
v___x_5605_ = lean_unsigned_to_nat(0u);
v___x_5606_ = lean_box(0);
v___x_5607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5607_, 0, v___x_5606_);
lean_ctor_set(v___x_5607_, 1, v_newHyps_5604_);
v___x_5608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5603_, v_hypotheses_5602_, v_methods_5586_, v_config_5587_, v___x_5605_, v___x_5607_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_);
lean_dec_ref(v_hypotheses_5602_);
if (lean_obj_tag(v___x_5608_) == 0)
{
lean_object* v_a_5609_; lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5638_; 
v_a_5609_ = lean_ctor_get(v___x_5608_, 0);
v_isSharedCheck_5638_ = !lean_is_exclusive(v___x_5608_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5611_ = v___x_5608_;
v_isShared_5612_ = v_isSharedCheck_5638_;
goto v_resetjp_5610_;
}
else
{
lean_inc(v_a_5609_);
lean_dec(v___x_5608_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5638_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v_fst_5613_; 
v_fst_5613_ = lean_ctor_get(v_a_5609_, 0);
if (lean_obj_tag(v_fst_5613_) == 0)
{
lean_object* v_snd_5614_; lean_object* v___x_5615_; lean_object* v_caches_5616_; lean_object* v_typeAnalysis_5617_; lean_object* v_target_5618_; uint8_t v_didChange_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5632_; 
v_snd_5614_ = lean_ctor_get(v_a_5609_, 1);
lean_inc(v_snd_5614_);
lean_dec(v_a_5609_);
v___x_5615_ = lean_st_ref_take(v_a_5590_);
v_caches_5616_ = lean_ctor_get(v___x_5615_, 0);
v_typeAnalysis_5617_ = lean_ctor_get(v___x_5615_, 1);
v_target_5618_ = lean_ctor_get(v___x_5615_, 2);
v_didChange_5619_ = lean_ctor_get_uint8(v___x_5615_, sizeof(void*)*4);
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5615_);
if (v_isSharedCheck_5632_ == 0)
{
lean_object* v_unused_5633_; 
v_unused_5633_ = lean_ctor_get(v___x_5615_, 3);
lean_dec(v_unused_5633_);
v___x_5621_ = v___x_5615_;
v_isShared_5622_ = v_isSharedCheck_5632_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_target_5618_);
lean_inc(v_typeAnalysis_5617_);
lean_inc(v_caches_5616_);
lean_dec(v___x_5615_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5632_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5624_; 
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 3, v_snd_5614_);
v___x_5624_ = v___x_5621_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_caches_5616_);
lean_ctor_set(v_reuseFailAlloc_5631_, 1, v_typeAnalysis_5617_);
lean_ctor_set(v_reuseFailAlloc_5631_, 2, v_target_5618_);
lean_ctor_set(v_reuseFailAlloc_5631_, 3, v_snd_5614_);
lean_ctor_set_uint8(v_reuseFailAlloc_5631_, sizeof(void*)*4, v_didChange_5619_);
v___x_5624_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
lean_object* v___x_5625_; uint8_t v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5629_; 
v___x_5625_ = lean_st_ref_put(v_a_5590_, v___x_5624_);
v___x_5626_ = 0;
v___x_5627_ = lean_box(v___x_5626_);
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 0, v___x_5627_);
v___x_5629_ = v___x_5611_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5627_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
else
{
lean_object* v_val_5634_; lean_object* v___x_5636_; 
lean_inc_ref(v_fst_5613_);
lean_dec(v_a_5609_);
v_val_5634_ = lean_ctor_get(v_fst_5613_, 0);
lean_inc(v_val_5634_);
lean_dec_ref_known(v_fst_5613_, 1);
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 0, v_val_5634_);
v___x_5636_ = v___x_5611_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_val_5634_);
v___x_5636_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
return v___x_5636_;
}
}
}
}
else
{
lean_object* v_a_5639_; lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5646_; 
v_a_5639_ = lean_ctor_get(v___x_5608_, 0);
v_isSharedCheck_5646_ = !lean_is_exclusive(v___x_5608_);
if (v_isSharedCheck_5646_ == 0)
{
v___x_5641_ = v___x_5608_;
v_isShared_5642_ = v_isSharedCheck_5646_;
goto v_resetjp_5640_;
}
else
{
lean_inc(v_a_5639_);
lean_dec(v___x_5608_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5646_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v___x_5644_; 
if (v_isShared_5642_ == 0)
{
v___x_5644_ = v___x_5641_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
v___x_5644_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
return v___x_5644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5647_, lean_object* v_config_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_){
_start:
{
lean_object* v_res_5662_; 
v_res_5662_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5647_, v_config_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_);
lean_dec(v_a_5660_);
lean_dec_ref(v_a_5659_);
lean_dec(v_a_5658_);
lean_dec_ref(v_a_5657_);
lean_dec(v_a_5656_);
lean_dec_ref(v_a_5655_);
lean_dec(v_a_5654_);
lean_dec_ref(v_a_5653_);
lean_dec(v_a_5652_);
lean_dec(v_a_5651_);
lean_dec_ref(v_a_5650_);
lean_dec(v_a_5649_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5663_, lean_object* v_msg_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_){
_start:
{
lean_object* v___x_5678_; 
v___x_5678_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5663_, v_msg_5664_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_);
return v___x_5678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5679_, lean_object* v_msg_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_){
_start:
{
lean_object* v_res_5694_; 
v_res_5694_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5679_, v_msg_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
lean_dec(v___y_5692_);
lean_dec_ref(v___y_5691_);
lean_dec(v___y_5690_);
lean_dec_ref(v___y_5689_);
lean_dec(v___y_5688_);
lean_dec_ref(v___y_5687_);
lean_dec(v___y_5686_);
lean_dec_ref(v___y_5685_);
lean_dec(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5695_, lean_object* v___x_5696_, lean_object* v_methods_5697_, lean_object* v_config_5698_, lean_object* v_inst_5699_, lean_object* v_R_5700_, lean_object* v_a_5701_, lean_object* v_b_5702_, lean_object* v_c_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5695_, v___x_5696_, v_methods_5697_, v_config_5698_, v_a_5701_, v_b_5702_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5718_ = _args[0];
lean_object* v___x_5719_ = _args[1];
lean_object* v_methods_5720_ = _args[2];
lean_object* v_config_5721_ = _args[3];
lean_object* v_inst_5722_ = _args[4];
lean_object* v_R_5723_ = _args[5];
lean_object* v_a_5724_ = _args[6];
lean_object* v_b_5725_ = _args[7];
lean_object* v_c_5726_ = _args[8];
lean_object* v___y_5727_ = _args[9];
lean_object* v___y_5728_ = _args[10];
lean_object* v___y_5729_ = _args[11];
lean_object* v___y_5730_ = _args[12];
lean_object* v___y_5731_ = _args[13];
lean_object* v___y_5732_ = _args[14];
lean_object* v___y_5733_ = _args[15];
lean_object* v___y_5734_ = _args[16];
lean_object* v___y_5735_ = _args[17];
lean_object* v___y_5736_ = _args[18];
lean_object* v___y_5737_ = _args[19];
lean_object* v___y_5738_ = _args[20];
lean_object* v___y_5739_ = _args[21];
_start:
{
lean_object* v_res_5740_; 
v_res_5740_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5718_, v___x_5719_, v_methods_5720_, v_config_5721_, v_inst_5722_, v_R_5723_, v_a_5724_, v_b_5725_, v_c_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_);
lean_dec(v___y_5738_);
lean_dec_ref(v___y_5737_);
lean_dec(v___y_5736_);
lean_dec_ref(v___y_5735_);
lean_dec(v___y_5734_);
lean_dec_ref(v___y_5733_);
lean_dec(v___y_5732_);
lean_dec_ref(v___y_5731_);
lean_dec(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v___x_5719_);
lean_dec(v_upperBound_5718_);
return v_res_5740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5741_, lean_object* v_config_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_){
_start:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; 
v___x_5755_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5756_ = lean_st_mk_ref(v___x_5755_);
v___x_5757_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5741_, v_config_5742_, v___x_5756_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_);
if (lean_obj_tag(v___x_5757_) == 0)
{
lean_object* v_a_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5766_; 
v_a_5758_ = lean_ctor_get(v___x_5757_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5757_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5760_ = v___x_5757_;
v_isShared_5761_ = v_isSharedCheck_5766_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_a_5758_);
lean_dec(v___x_5757_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5766_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5762_; lean_object* v___x_5764_; 
v___x_5762_ = lean_st_ref_get(v___x_5756_);
lean_dec(v___x_5756_);
lean_dec(v___x_5762_);
if (v_isShared_5761_ == 0)
{
v___x_5764_ = v___x_5760_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5758_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
else
{
lean_dec(v___x_5756_);
return v___x_5757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5767_, lean_object* v_config_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_){
_start:
{
lean_object* v_res_5781_; 
v_res_5781_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5767_, v_config_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_, v_a_5779_);
lean_dec(v_a_5779_);
lean_dec_ref(v_a_5778_);
lean_dec(v_a_5777_);
lean_dec_ref(v_a_5776_);
lean_dec(v_a_5775_);
lean_dec_ref(v_a_5774_);
lean_dec(v_a_5773_);
lean_dec_ref(v_a_5772_);
lean_dec(v_a_5771_);
lean_dec(v_a_5770_);
lean_dec_ref(v_a_5769_);
return v_res_5781_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5783_; lean_object* v___x_5784_; 
v___x_5783_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5784_ = l_Lean_stringToMessageData(v___x_5783_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5785_, lean_object* v_x_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_){
_start:
{
lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; 
v___x_5799_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5800_ = l_Lean_MessageData_ofName(v_name_5785_);
v___x_5801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5801_, 0, v___x_5799_);
lean_ctor_set(v___x_5801_, 1, v___x_5800_);
v___x_5802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5802_, 0, v___x_5801_);
return v___x_5802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5803_, lean_object* v_x_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5803_, v_x_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
lean_dec(v___y_5815_);
lean_dec_ref(v___y_5814_);
lean_dec(v___y_5813_);
lean_dec_ref(v___y_5812_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5808_);
lean_dec(v___y_5807_);
lean_dec(v___y_5806_);
lean_dec_ref(v___y_5805_);
lean_dec_ref(v_x_5804_);
return v_res_5817_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5818_; 
v___x_5818_ = l_instMonadExceptOfEIO___redArg();
return v___x_5818_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5819_; lean_object* v___x_5820_; 
v___x_5819_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5820_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5819_);
return v___x_5820_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5822_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5821_);
return v___x_5822_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___x_5823_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5824_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5823_);
return v___x_5824_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5826_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5825_);
return v___x_5826_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5827_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5828_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5827_);
return v___x_5828_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5829_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5830_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5829_);
return v___x_5830_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5831_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5832_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5831_);
return v___x_5832_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5833_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5834_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5833_);
return v___x_5834_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; 
v___x_5835_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5836_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5835_);
return v___x_5836_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; 
v___x_5837_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5838_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5837_);
return v___x_5838_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5839_; lean_object* v___x_5840_; 
v___x_5839_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5840_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5839_);
return v___x_5840_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5842_; double v___x_5843_; 
v___x_5842_ = lean_unsigned_to_nat(1000000000u);
v___x_5843_ = lean_float_of_nat(v___x_5842_);
return v___x_5843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_){
_start:
{
lean_object* v___x_5857_; lean_object* v_toApplicative_5858_; lean_object* v_toFunctor_5859_; lean_object* v_toSeq_5860_; lean_object* v_toSeqLeft_5861_; lean_object* v_toSeqRight_5862_; lean_object* v___f_5863_; lean_object* v___f_5864_; lean_object* v___f_5865_; lean_object* v___f_5866_; lean_object* v___x_5867_; lean_object* v___f_5868_; lean_object* v___f_5869_; lean_object* v___f_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v_toApplicative_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_6017_; 
v___x_5857_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5858_ = lean_ctor_get(v___x_5857_, 0);
v_toFunctor_5859_ = lean_ctor_get(v_toApplicative_5858_, 0);
v_toSeq_5860_ = lean_ctor_get(v_toApplicative_5858_, 2);
v_toSeqLeft_5861_ = lean_ctor_get(v_toApplicative_5858_, 3);
v_toSeqRight_5862_ = lean_ctor_get(v_toApplicative_5858_, 4);
v___f_5863_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5864_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5859_, 2);
v___f_5865_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5865_, 0, v_toFunctor_5859_);
v___f_5866_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5866_, 0, v_toFunctor_5859_);
v___x_5867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5867_, 0, v___f_5865_);
lean_ctor_set(v___x_5867_, 1, v___f_5866_);
lean_inc(v_toSeqRight_5862_);
v___f_5868_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5868_, 0, v_toSeqRight_5862_);
lean_inc(v_toSeqLeft_5861_);
v___f_5869_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5869_, 0, v_toSeqLeft_5861_);
lean_inc(v_toSeq_5860_);
v___f_5870_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5870_, 0, v_toSeq_5860_);
v___x_5871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5871_, 0, v___x_5867_);
lean_ctor_set(v___x_5871_, 1, v___f_5863_);
lean_ctor_set(v___x_5871_, 2, v___f_5870_);
lean_ctor_set(v___x_5871_, 3, v___f_5869_);
lean_ctor_set(v___x_5871_, 4, v___f_5868_);
v___x_5872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5872_, 0, v___x_5871_);
lean_ctor_set(v___x_5872_, 1, v___f_5864_);
v___x_5873_ = l_StateRefT_x27_instMonad___redArg(v___x_5872_);
v_toApplicative_5874_ = lean_ctor_get(v___x_5873_, 0);
v_isSharedCheck_6017_ = !lean_is_exclusive(v___x_5873_);
if (v_isSharedCheck_6017_ == 0)
{
lean_object* v_unused_6018_; 
v_unused_6018_ = lean_ctor_get(v___x_5873_, 1);
lean_dec(v_unused_6018_);
v___x_5876_ = v___x_5873_;
v_isShared_5877_ = v_isSharedCheck_6017_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_toApplicative_5874_);
lean_dec(v___x_5873_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_6017_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v_toFunctor_5878_; lean_object* v_toSeq_5879_; lean_object* v_toSeqLeft_5880_; lean_object* v_toSeqRight_5881_; lean_object* v___x_5883_; uint8_t v_isShared_5884_; uint8_t v_isSharedCheck_6015_; 
v_toFunctor_5878_ = lean_ctor_get(v_toApplicative_5874_, 0);
v_toSeq_5879_ = lean_ctor_get(v_toApplicative_5874_, 2);
v_toSeqLeft_5880_ = lean_ctor_get(v_toApplicative_5874_, 3);
v_toSeqRight_5881_ = lean_ctor_get(v_toApplicative_5874_, 4);
v_isSharedCheck_6015_ = !lean_is_exclusive(v_toApplicative_5874_);
if (v_isSharedCheck_6015_ == 0)
{
lean_object* v_unused_6016_; 
v_unused_6016_ = lean_ctor_get(v_toApplicative_5874_, 1);
lean_dec(v_unused_6016_);
v___x_5883_ = v_toApplicative_5874_;
v_isShared_5884_ = v_isSharedCheck_6015_;
goto v_resetjp_5882_;
}
else
{
lean_inc(v_toSeqRight_5881_);
lean_inc(v_toSeqLeft_5880_);
lean_inc(v_toSeq_5879_);
lean_inc(v_toFunctor_5878_);
lean_dec(v_toApplicative_5874_);
v___x_5883_ = lean_box(0);
v_isShared_5884_ = v_isSharedCheck_6015_;
goto v_resetjp_5882_;
}
v_resetjp_5882_:
{
lean_object* v___f_5885_; lean_object* v___f_5886_; lean_object* v___f_5887_; lean_object* v___f_5888_; lean_object* v___x_5889_; lean_object* v___f_5890_; lean_object* v___f_5891_; lean_object* v___f_5892_; lean_object* v___x_5894_; 
v___f_5885_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5886_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5878_);
v___f_5887_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5887_, 0, v_toFunctor_5878_);
v___f_5888_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5888_, 0, v_toFunctor_5878_);
v___x_5889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___f_5887_);
lean_ctor_set(v___x_5889_, 1, v___f_5888_);
v___f_5890_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5890_, 0, v_toSeqRight_5881_);
v___f_5891_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5891_, 0, v_toSeqLeft_5880_);
v___f_5892_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5892_, 0, v_toSeq_5879_);
if (v_isShared_5884_ == 0)
{
lean_ctor_set(v___x_5883_, 4, v___f_5890_);
lean_ctor_set(v___x_5883_, 3, v___f_5891_);
lean_ctor_set(v___x_5883_, 2, v___f_5892_);
lean_ctor_set(v___x_5883_, 1, v___f_5885_);
lean_ctor_set(v___x_5883_, 0, v___x_5889_);
v___x_5894_ = v___x_5883_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_6014_; 
v_reuseFailAlloc_6014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6014_, 0, v___x_5889_);
lean_ctor_set(v_reuseFailAlloc_6014_, 1, v___f_5885_);
lean_ctor_set(v_reuseFailAlloc_6014_, 2, v___f_5892_);
lean_ctor_set(v_reuseFailAlloc_6014_, 3, v___f_5891_);
lean_ctor_set(v_reuseFailAlloc_6014_, 4, v___f_5890_);
v___x_5894_ = v_reuseFailAlloc_6014_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
lean_object* v___x_5896_; 
if (v_isShared_5877_ == 0)
{
lean_ctor_set(v___x_5876_, 1, v___f_5886_);
lean_ctor_set(v___x_5876_, 0, v___x_5894_);
v___x_5896_ = v___x_5876_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v___x_5894_);
lean_ctor_set(v_reuseFailAlloc_6013_, 1, v___f_5886_);
v___x_5896_ = v_reuseFailAlloc_6013_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v_toMonadRef_5906_; lean_object* v___x_5907_; lean_object* v_name_5908_; lean_object* v_run_x27_5909_; lean_object* v___x_5911_; uint8_t v_isShared_5912_; uint8_t v_isSharedCheck_6012_; 
v___x_5897_ = l_StateRefT_x27_instMonad___redArg(v___x_5896_);
v___x_5898_ = l_ReaderT_instMonad___redArg(v___x_5897_);
v___x_5899_ = l_StateRefT_x27_instMonad___redArg(v___x_5898_);
v___x_5900_ = l_ReaderT_instMonad___redArg(v___x_5899_);
v___x_5901_ = l_ReaderT_instMonad___redArg(v___x_5900_);
v___x_5902_ = l_StateRefT_x27_instMonad___redArg(v___x_5901_);
v___x_5903_ = l_ReaderT_instMonad___redArg(v___x_5902_);
v___x_5904_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5905_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_5906_ = lean_ctor_get(v___x_5905_, 0);
v___x_5907_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_name_5908_ = lean_ctor_get(v_pass_5844_, 0);
v_run_x27_5909_ = lean_ctor_get(v_pass_5844_, 1);
v_isSharedCheck_6012_ = !lean_is_exclusive(v_pass_5844_);
if (v_isSharedCheck_6012_ == 0)
{
v___x_5911_ = v_pass_5844_;
v_isShared_5912_ = v_isSharedCheck_6012_;
goto v_resetjp_5910_;
}
else
{
lean_inc(v_run_x27_5909_);
lean_inc(v_name_5908_);
lean_dec(v_pass_5844_);
v___x_5911_ = lean_box(0);
v_isShared_5912_ = v_isSharedCheck_6012_;
goto v_resetjp_5910_;
}
v_resetjp_5910_:
{
lean_object* v___x_5913_; lean_object* v_toCold_5914_; lean_object* v_options_5915_; uint8_t v_hasTrace_5916_; 
v___x_5913_ = l_Lean_KVMap_instValueBool;
v_toCold_5914_ = lean_ctor_get(v_a_5854_, 0);
v_options_5915_ = lean_ctor_get(v_toCold_5914_, 2);
v_hasTrace_5916_ = lean_ctor_get_uint8(v_options_5915_, sizeof(void*)*1);
if (v_hasTrace_5916_ == 0)
{
lean_object* v___x_5917_; 
lean_del_object(v___x_5911_);
lean_dec(v_name_5908_);
lean_dec_ref(v___x_5903_);
lean_inc(v_a_5855_);
lean_inc_ref(v_a_5854_);
lean_inc(v_a_5853_);
lean_inc_ref(v_a_5852_);
lean_inc(v_a_5851_);
lean_inc_ref(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
lean_inc(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
v___x_5917_ = lean_apply_12(v_run_x27_5909_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, lean_box(0));
return v___x_5917_;
}
else
{
lean_object* v_inheritedTraceOptions_5918_; lean_object* v___f_5919_; lean_object* v___f_5920_; lean_object* v___f_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; uint8_t v___x_5925_; lean_object* v___y_5927_; lean_object* v___y_5928_; lean_object* v_a_5929_; lean_object* v___y_5945_; lean_object* v___y_5946_; lean_object* v_a_5947_; 
v_inheritedTraceOptions_5918_ = lean_ctor_get(v_toCold_5914_, 11);
v___f_5919_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5919_, 0, v_name_5908_);
v___f_5920_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_5921_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5922_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5923_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5924_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5925_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5918_, v_options_5915_, v___x_5924_);
if (v___x_5925_ == 0)
{
lean_object* v___x_6008_; lean_object* v___x_6009_; uint8_t v___x_6010_; 
v___x_6008_ = l_Lean_trace_profiler;
v___x_6009_ = l_Lean_Option_get___redArg(v___x_5913_, v_options_5915_, v___x_6008_);
v___x_6010_ = lean_unbox(v___x_6009_);
lean_dec(v___x_6009_);
if (v___x_6010_ == 0)
{
lean_object* v___x_6011_; 
lean_dec_ref(v___f_5919_);
lean_del_object(v___x_5911_);
lean_dec_ref(v___x_5903_);
lean_inc(v_a_5855_);
lean_inc_ref(v_a_5854_);
lean_inc(v_a_5853_);
lean_inc_ref(v_a_5852_);
lean_inc(v_a_5851_);
lean_inc_ref(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
lean_inc(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
v___x_6011_ = lean_apply_12(v_run_x27_5909_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, lean_box(0));
return v___x_6011_;
}
else
{
goto v___jp_5957_;
}
}
else
{
goto v___jp_5957_;
}
v___jp_5926_:
{
lean_object* v___x_5930_; double v___x_5931_; double v___x_5932_; double v___x_5933_; double v___x_5934_; double v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5939_; 
v___x_5930_ = lean_io_mono_nanos_now();
v___x_5931_ = lean_float_of_nat(v___y_5928_);
v___x_5932_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5933_ = lean_float_div(v___x_5931_, v___x_5932_);
v___x_5934_ = lean_float_of_nat(v___x_5930_);
v___x_5935_ = lean_float_div(v___x_5934_, v___x_5932_);
v___x_5936_ = lean_box_float(v___x_5933_);
v___x_5937_ = lean_box_float(v___x_5935_);
if (v_isShared_5912_ == 0)
{
lean_ctor_set(v___x_5911_, 1, v___x_5937_);
lean_ctor_set(v___x_5911_, 0, v___x_5936_);
v___x_5939_ = v___x_5911_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5943_; 
v_reuseFailAlloc_5943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5943_, 0, v___x_5936_);
lean_ctor_set(v_reuseFailAlloc_5943_, 1, v___x_5937_);
v___x_5939_ = v_reuseFailAlloc_5943_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
lean_object* v___x_5940_; lean_object* v___x_28875__overap_5941_; lean_object* v___x_5942_; 
v___x_5940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5940_, 0, v_a_5929_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
lean_inc_ref(v_toMonadRef_5906_);
v___x_28875__overap_5941_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5903_, v___x_5904_, v_toMonadRef_5906_, v___f_5920_, lean_box(0), v___x_5907_, v___f_5921_, v___x_5922_, v_hasTrace_5916_, v___x_5923_, v_options_5915_, v___x_5925_, v___y_5927_, v___f_5919_, v___x_5940_);
lean_inc(v_a_5855_);
lean_inc_ref(v_a_5854_);
lean_inc(v_a_5853_);
lean_inc_ref(v_a_5852_);
lean_inc(v_a_5851_);
lean_inc_ref(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
lean_inc(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
v___x_5942_ = lean_apply_12(v___x_28875__overap_5941_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, lean_box(0));
return v___x_5942_;
}
}
v___jp_5944_:
{
lean_object* v___x_5948_; double v___x_5949_; double v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_28896__overap_5955_; lean_object* v___x_5956_; 
v___x_5948_ = lean_io_get_num_heartbeats();
v___x_5949_ = lean_float_of_nat(v___y_5945_);
v___x_5950_ = lean_float_of_nat(v___x_5948_);
v___x_5951_ = lean_box_float(v___x_5949_);
v___x_5952_ = lean_box_float(v___x_5950_);
v___x_5953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5951_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
v___x_5954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5954_, 0, v_a_5947_);
lean_ctor_set(v___x_5954_, 1, v___x_5953_);
lean_inc_ref(v_toMonadRef_5906_);
v___x_28896__overap_5955_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5903_, v___x_5904_, v_toMonadRef_5906_, v___f_5920_, lean_box(0), v___x_5907_, v___f_5921_, v___x_5922_, v_hasTrace_5916_, v___x_5923_, v_options_5915_, v___x_5925_, v___y_5946_, v___f_5919_, v___x_5954_);
lean_inc(v_a_5855_);
lean_inc_ref(v_a_5854_);
lean_inc(v_a_5853_);
lean_inc_ref(v_a_5852_);
lean_inc(v_a_5851_);
lean_inc_ref(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
lean_inc(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
v___x_5956_ = lean_apply_12(v___x_28896__overap_5955_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, lean_box(0));
return v___x_5956_;
}
v___jp_5957_:
{
lean_object* v___x_28853__overap_5958_; lean_object* v___x_5959_; 
lean_inc_ref(v___x_5903_);
v___x_28853__overap_5958_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5903_, v___x_5904_);
lean_inc(v_a_5855_);
lean_inc_ref(v_a_5854_);
lean_inc(v_a_5853_);
lean_inc_ref(v_a_5852_);
lean_inc(v_a_5851_);
lean_inc_ref(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
lean_inc(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
v___x_5959_ = lean_apply_12(v___x_28853__overap_5958_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, lean_box(0));
if (lean_obj_tag(v___x_5959_) == 0)
{
lean_object* v_a_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; uint8_t v___x_5963_; 
v_a_5960_ = lean_ctor_get(v___x_5959_, 0);
lean_inc(v_a_5960_);
lean_dec_ref_known(v___x_5959_, 1);
v___x_5961_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5962_ = l_Lean_Option_get___redArg(v___x_5913_, v_options_5915_, v___x_5961_);
v___x_5963_ = lean_unbox(v___x_5962_);
lean_dec(v___x_5962_);
if (v___x_5963_ == 0)
{
lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5964_ = lean_io_mono_nanos_now();
lean_inc(v_a_5855_);
lean_inc_ref(v_a_5854_);
lean_inc(v_a_5853_);
lean_inc_ref(v_a_5852_);
lean_inc(v_a_5851_);
lean_inc_ref(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
lean_inc(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
v___x_5965_ = lean_apply_12(v_run_x27_5909_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, lean_box(0));
if (lean_obj_tag(v___x_5965_) == 0)
{
lean_object* v_a_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5973_; 
v_a_5966_ = lean_ctor_get(v___x_5965_, 0);
v_isSharedCheck_5973_ = !lean_is_exclusive(v___x_5965_);
if (v_isSharedCheck_5973_ == 0)
{
v___x_5968_ = v___x_5965_;
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_a_5966_);
lean_dec(v___x_5965_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5971_; 
if (v_isShared_5969_ == 0)
{
lean_ctor_set_tag(v___x_5968_, 1);
v___x_5971_ = v___x_5968_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_a_5966_);
v___x_5971_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
v___y_5927_ = v_a_5960_;
v___y_5928_ = v___x_5964_;
v_a_5929_ = v___x_5971_;
goto v___jp_5926_;
}
}
}
else
{
lean_object* v_a_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5981_; 
v_a_5974_ = lean_ctor_get(v___x_5965_, 0);
v_isSharedCheck_5981_ = !lean_is_exclusive(v___x_5965_);
if (v_isSharedCheck_5981_ == 0)
{
v___x_5976_ = v___x_5965_;
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_a_5974_);
lean_dec(v___x_5965_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5979_; 
if (v_isShared_5977_ == 0)
{
lean_ctor_set_tag(v___x_5976_, 0);
v___x_5979_ = v___x_5976_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
v___x_5979_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
v___y_5927_ = v_a_5960_;
v___y_5928_ = v___x_5964_;
v_a_5929_ = v___x_5979_;
goto v___jp_5926_;
}
}
}
}
else
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
lean_del_object(v___x_5911_);
v___x_5982_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5855_);
lean_inc_ref(v_a_5854_);
lean_inc(v_a_5853_);
lean_inc_ref(v_a_5852_);
lean_inc(v_a_5851_);
lean_inc_ref(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
lean_inc(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
v___x_5983_ = lean_apply_12(v_run_x27_5909_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, lean_box(0));
if (lean_obj_tag(v___x_5983_) == 0)
{
lean_object* v_a_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5991_; 
v_a_5984_ = lean_ctor_get(v___x_5983_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_5991_ == 0)
{
v___x_5986_ = v___x_5983_;
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_a_5984_);
lean_dec(v___x_5983_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5989_; 
if (v_isShared_5987_ == 0)
{
lean_ctor_set_tag(v___x_5986_, 1);
v___x_5989_ = v___x_5986_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
v___x_5989_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
v___y_5945_ = v___x_5982_;
v___y_5946_ = v_a_5960_;
v_a_5947_ = v___x_5989_;
goto v___jp_5944_;
}
}
}
else
{
lean_object* v_a_5992_; lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_5999_; 
v_a_5992_ = lean_ctor_get(v___x_5983_, 0);
v_isSharedCheck_5999_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_5999_ == 0)
{
v___x_5994_ = v___x_5983_;
v_isShared_5995_ = v_isSharedCheck_5999_;
goto v_resetjp_5993_;
}
else
{
lean_inc(v_a_5992_);
lean_dec(v___x_5983_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_5999_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
lean_object* v___x_5997_; 
if (v_isShared_5995_ == 0)
{
lean_ctor_set_tag(v___x_5994_, 0);
v___x_5997_ = v___x_5994_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_5998_; 
v_reuseFailAlloc_5998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_a_5992_);
v___x_5997_ = v_reuseFailAlloc_5998_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
v___y_5945_ = v___x_5982_;
v___y_5946_ = v_a_5960_;
v_a_5947_ = v___x_5997_;
goto v___jp_5944_;
}
}
}
}
}
else
{
lean_object* v_a_6000_; lean_object* v___x_6002_; uint8_t v_isShared_6003_; uint8_t v_isSharedCheck_6007_; 
lean_dec_ref(v___f_5919_);
lean_del_object(v___x_5911_);
lean_dec_ref(v_run_x27_5909_);
lean_dec_ref(v___x_5903_);
v_a_6000_ = lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_6007_ = !lean_is_exclusive(v___x_5959_);
if (v_isSharedCheck_6007_ == 0)
{
v___x_6002_ = v___x_5959_;
v_isShared_6003_ = v_isSharedCheck_6007_;
goto v_resetjp_6001_;
}
else
{
lean_inc(v_a_6000_);
lean_dec(v___x_5959_);
v___x_6002_ = lean_box(0);
v_isShared_6003_ = v_isSharedCheck_6007_;
goto v_resetjp_6001_;
}
v_resetjp_6001_:
{
lean_object* v___x_6005_; 
if (v_isShared_6003_ == 0)
{
v___x_6005_ = v___x_6002_;
goto v_reusejp_6004_;
}
else
{
lean_object* v_reuseFailAlloc_6006_; 
v_reuseFailAlloc_6006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6006_, 0, v_a_6000_);
v___x_6005_ = v_reuseFailAlloc_6006_;
goto v_reusejp_6004_;
}
v_reusejp_6004_:
{
return v___x_6005_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_){
_start:
{
lean_object* v_res_6032_; 
v_res_6032_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_);
lean_dec(v_a_6030_);
lean_dec_ref(v_a_6029_);
lean_dec(v_a_6028_);
lean_dec_ref(v_a_6027_);
lean_dec(v_a_6026_);
lean_dec_ref(v_a_6025_);
lean_dec(v_a_6024_);
lean_dec_ref(v_a_6023_);
lean_dec(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec_ref(v_a_6020_);
return v_res_6032_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; 
v___x_6033_ = lean_unsigned_to_nat(32u);
v___x_6034_ = lean_mk_empty_array_with_capacity(v___x_6033_);
v___x_6035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
return v___x_6035_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; 
v___x_6036_ = ((size_t)5ULL);
v___x_6037_ = lean_unsigned_to_nat(0u);
v___x_6038_ = lean_unsigned_to_nat(32u);
v___x_6039_ = lean_mk_empty_array_with_capacity(v___x_6038_);
v___x_6040_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6041_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
lean_ctor_set(v___x_6041_, 1, v___x_6039_);
lean_ctor_set(v___x_6041_, 2, v___x_6037_);
lean_ctor_set(v___x_6041_, 3, v___x_6037_);
lean_ctor_set_usize(v___x_6041_, 4, v___x_6036_);
return v___x_6041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6042_){
_start:
{
lean_object* v___x_6044_; lean_object* v_traceState_6045_; lean_object* v_traces_6046_; lean_object* v___x_6047_; lean_object* v_traceState_6048_; lean_object* v_env_6049_; lean_object* v_nextMacroScope_6050_; lean_object* v_ngen_6051_; lean_object* v_auxDeclNGen_6052_; lean_object* v_cache_6053_; lean_object* v_recordedDeps_6054_; lean_object* v_messages_6055_; lean_object* v_infoState_6056_; lean_object* v_snapshotTasks_6057_; lean_object* v___x_6059_; uint8_t v_isShared_6060_; uint8_t v_isSharedCheck_6076_; 
v___x_6044_ = lean_st_ref_get(v___y_6042_);
v_traceState_6045_ = lean_ctor_get(v___x_6044_, 4);
lean_inc_ref(v_traceState_6045_);
lean_dec(v___x_6044_);
v_traces_6046_ = lean_ctor_get(v_traceState_6045_, 0);
lean_inc_ref(v_traces_6046_);
lean_dec_ref(v_traceState_6045_);
v___x_6047_ = lean_st_ref_take(v___y_6042_);
v_traceState_6048_ = lean_ctor_get(v___x_6047_, 4);
v_env_6049_ = lean_ctor_get(v___x_6047_, 0);
v_nextMacroScope_6050_ = lean_ctor_get(v___x_6047_, 1);
v_ngen_6051_ = lean_ctor_get(v___x_6047_, 2);
v_auxDeclNGen_6052_ = lean_ctor_get(v___x_6047_, 3);
v_cache_6053_ = lean_ctor_get(v___x_6047_, 5);
v_recordedDeps_6054_ = lean_ctor_get(v___x_6047_, 6);
v_messages_6055_ = lean_ctor_get(v___x_6047_, 7);
v_infoState_6056_ = lean_ctor_get(v___x_6047_, 8);
v_snapshotTasks_6057_ = lean_ctor_get(v___x_6047_, 9);
v_isSharedCheck_6076_ = !lean_is_exclusive(v___x_6047_);
if (v_isSharedCheck_6076_ == 0)
{
v___x_6059_ = v___x_6047_;
v_isShared_6060_ = v_isSharedCheck_6076_;
goto v_resetjp_6058_;
}
else
{
lean_inc(v_snapshotTasks_6057_);
lean_inc(v_infoState_6056_);
lean_inc(v_messages_6055_);
lean_inc(v_recordedDeps_6054_);
lean_inc(v_cache_6053_);
lean_inc(v_traceState_6048_);
lean_inc(v_auxDeclNGen_6052_);
lean_inc(v_ngen_6051_);
lean_inc(v_nextMacroScope_6050_);
lean_inc(v_env_6049_);
lean_dec(v___x_6047_);
v___x_6059_ = lean_box(0);
v_isShared_6060_ = v_isSharedCheck_6076_;
goto v_resetjp_6058_;
}
v_resetjp_6058_:
{
uint64_t v_tid_6061_; lean_object* v___x_6063_; uint8_t v_isShared_6064_; uint8_t v_isSharedCheck_6074_; 
v_tid_6061_ = lean_ctor_get_uint64(v_traceState_6048_, sizeof(void*)*1);
v_isSharedCheck_6074_ = !lean_is_exclusive(v_traceState_6048_);
if (v_isSharedCheck_6074_ == 0)
{
lean_object* v_unused_6075_; 
v_unused_6075_ = lean_ctor_get(v_traceState_6048_, 0);
lean_dec(v_unused_6075_);
v___x_6063_ = v_traceState_6048_;
v_isShared_6064_ = v_isSharedCheck_6074_;
goto v_resetjp_6062_;
}
else
{
lean_dec(v_traceState_6048_);
v___x_6063_ = lean_box(0);
v_isShared_6064_ = v_isSharedCheck_6074_;
goto v_resetjp_6062_;
}
v_resetjp_6062_:
{
lean_object* v___x_6065_; lean_object* v___x_6067_; 
v___x_6065_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6064_ == 0)
{
lean_ctor_set(v___x_6063_, 0, v___x_6065_);
v___x_6067_ = v___x_6063_;
goto v_reusejp_6066_;
}
else
{
lean_object* v_reuseFailAlloc_6073_; 
v_reuseFailAlloc_6073_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6073_, 0, v___x_6065_);
lean_ctor_set_uint64(v_reuseFailAlloc_6073_, sizeof(void*)*1, v_tid_6061_);
v___x_6067_ = v_reuseFailAlloc_6073_;
goto v_reusejp_6066_;
}
v_reusejp_6066_:
{
lean_object* v___x_6069_; 
if (v_isShared_6060_ == 0)
{
lean_ctor_set(v___x_6059_, 4, v___x_6067_);
v___x_6069_ = v___x_6059_;
goto v_reusejp_6068_;
}
else
{
lean_object* v_reuseFailAlloc_6072_; 
v_reuseFailAlloc_6072_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_env_6049_);
lean_ctor_set(v_reuseFailAlloc_6072_, 1, v_nextMacroScope_6050_);
lean_ctor_set(v_reuseFailAlloc_6072_, 2, v_ngen_6051_);
lean_ctor_set(v_reuseFailAlloc_6072_, 3, v_auxDeclNGen_6052_);
lean_ctor_set(v_reuseFailAlloc_6072_, 4, v___x_6067_);
lean_ctor_set(v_reuseFailAlloc_6072_, 5, v_cache_6053_);
lean_ctor_set(v_reuseFailAlloc_6072_, 6, v_recordedDeps_6054_);
lean_ctor_set(v_reuseFailAlloc_6072_, 7, v_messages_6055_);
lean_ctor_set(v_reuseFailAlloc_6072_, 8, v_infoState_6056_);
lean_ctor_set(v_reuseFailAlloc_6072_, 9, v_snapshotTasks_6057_);
v___x_6069_ = v_reuseFailAlloc_6072_;
goto v_reusejp_6068_;
}
v_reusejp_6068_:
{
lean_object* v___x_6070_; lean_object* v___x_6071_; 
v___x_6070_ = lean_st_ref_put(v___y_6042_, v___x_6069_);
v___x_6071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6071_, 0, v_traces_6046_);
return v___x_6071_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6077_, lean_object* v___y_6078_){
_start:
{
lean_object* v_res_6079_; 
v_res_6079_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6077_);
lean_dec(v___y_6077_);
return v_res_6079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_){
_start:
{
lean_object* v___x_6092_; 
v___x_6092_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6090_);
return v___x_6092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_){
_start:
{
lean_object* v_res_6105_; 
v_res_6105_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_, v___y_6103_);
lean_dec(v___y_6103_);
lean_dec_ref(v___y_6102_);
lean_dec(v___y_6101_);
lean_dec_ref(v___y_6100_);
lean_dec(v___y_6099_);
lean_dec_ref(v___y_6098_);
lean_dec(v___y_6097_);
lean_dec_ref(v___y_6096_);
lean_dec(v___y_6095_);
lean_dec(v___y_6094_);
lean_dec_ref(v___y_6093_);
return v_res_6105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6106_, lean_object* v_opt_6107_){
_start:
{
lean_object* v_name_6108_; lean_object* v_defValue_6109_; lean_object* v_map_6110_; lean_object* v___x_6111_; 
v_name_6108_ = lean_ctor_get(v_opt_6107_, 0);
v_defValue_6109_ = lean_ctor_get(v_opt_6107_, 1);
v_map_6110_ = lean_ctor_get(v_opts_6106_, 0);
v___x_6111_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6110_, v_name_6108_);
if (lean_obj_tag(v___x_6111_) == 0)
{
uint8_t v___x_6112_; 
v___x_6112_ = lean_unbox(v_defValue_6109_);
return v___x_6112_;
}
else
{
lean_object* v_val_6113_; 
v_val_6113_ = lean_ctor_get(v___x_6111_, 0);
lean_inc(v_val_6113_);
lean_dec_ref_known(v___x_6111_, 1);
if (lean_obj_tag(v_val_6113_) == 1)
{
uint8_t v_v_6114_; 
v_v_6114_ = lean_ctor_get_uint8(v_val_6113_, 0);
lean_dec_ref_known(v_val_6113_, 0);
return v_v_6114_;
}
else
{
uint8_t v___x_6115_; 
lean_dec(v_val_6113_);
v___x_6115_ = lean_unbox(v_defValue_6109_);
return v___x_6115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6116_, lean_object* v_opt_6117_){
_start:
{
uint8_t v_res_6118_; lean_object* v_r_6119_; 
v_res_6118_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6116_, v_opt_6117_);
lean_dec_ref(v_opt_6117_);
lean_dec_ref(v_opts_6116_);
v_r_6119_ = lean_box(v_res_6118_);
return v_r_6119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6120_, lean_object* v_msg_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_){
_start:
{
lean_object* v_ref_6127_; lean_object* v___x_6128_; lean_object* v_a_6129_; lean_object* v___x_6131_; uint8_t v_isShared_6132_; uint8_t v_isSharedCheck_6174_; 
v_ref_6127_ = lean_ctor_get(v___y_6124_, 2);
v___x_6128_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
v_a_6129_ = lean_ctor_get(v___x_6128_, 0);
v_isSharedCheck_6174_ = !lean_is_exclusive(v___x_6128_);
if (v_isSharedCheck_6174_ == 0)
{
v___x_6131_ = v___x_6128_;
v_isShared_6132_ = v_isSharedCheck_6174_;
goto v_resetjp_6130_;
}
else
{
lean_inc(v_a_6129_);
lean_dec(v___x_6128_);
v___x_6131_ = lean_box(0);
v_isShared_6132_ = v_isSharedCheck_6174_;
goto v_resetjp_6130_;
}
v_resetjp_6130_:
{
lean_object* v___x_6133_; lean_object* v_traceState_6134_; lean_object* v_env_6135_; lean_object* v_nextMacroScope_6136_; lean_object* v_ngen_6137_; lean_object* v_auxDeclNGen_6138_; lean_object* v_cache_6139_; lean_object* v_recordedDeps_6140_; lean_object* v_messages_6141_; lean_object* v_infoState_6142_; lean_object* v_snapshotTasks_6143_; lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6173_; 
v___x_6133_ = lean_st_ref_take(v___y_6125_);
v_traceState_6134_ = lean_ctor_get(v___x_6133_, 4);
v_env_6135_ = lean_ctor_get(v___x_6133_, 0);
v_nextMacroScope_6136_ = lean_ctor_get(v___x_6133_, 1);
v_ngen_6137_ = lean_ctor_get(v___x_6133_, 2);
v_auxDeclNGen_6138_ = lean_ctor_get(v___x_6133_, 3);
v_cache_6139_ = lean_ctor_get(v___x_6133_, 5);
v_recordedDeps_6140_ = lean_ctor_get(v___x_6133_, 6);
v_messages_6141_ = lean_ctor_get(v___x_6133_, 7);
v_infoState_6142_ = lean_ctor_get(v___x_6133_, 8);
v_snapshotTasks_6143_ = lean_ctor_get(v___x_6133_, 9);
v_isSharedCheck_6173_ = !lean_is_exclusive(v___x_6133_);
if (v_isSharedCheck_6173_ == 0)
{
v___x_6145_ = v___x_6133_;
v_isShared_6146_ = v_isSharedCheck_6173_;
goto v_resetjp_6144_;
}
else
{
lean_inc(v_snapshotTasks_6143_);
lean_inc(v_infoState_6142_);
lean_inc(v_messages_6141_);
lean_inc(v_recordedDeps_6140_);
lean_inc(v_cache_6139_);
lean_inc(v_traceState_6134_);
lean_inc(v_auxDeclNGen_6138_);
lean_inc(v_ngen_6137_);
lean_inc(v_nextMacroScope_6136_);
lean_inc(v_env_6135_);
lean_dec(v___x_6133_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6173_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
uint64_t v_tid_6147_; lean_object* v_traces_6148_; lean_object* v___x_6150_; uint8_t v_isShared_6151_; uint8_t v_isSharedCheck_6172_; 
v_tid_6147_ = lean_ctor_get_uint64(v_traceState_6134_, sizeof(void*)*1);
v_traces_6148_ = lean_ctor_get(v_traceState_6134_, 0);
v_isSharedCheck_6172_ = !lean_is_exclusive(v_traceState_6134_);
if (v_isSharedCheck_6172_ == 0)
{
v___x_6150_ = v_traceState_6134_;
v_isShared_6151_ = v_isSharedCheck_6172_;
goto v_resetjp_6149_;
}
else
{
lean_inc(v_traces_6148_);
lean_dec(v_traceState_6134_);
v___x_6150_ = lean_box(0);
v_isShared_6151_ = v_isSharedCheck_6172_;
goto v_resetjp_6149_;
}
v_resetjp_6149_:
{
lean_object* v___x_6152_; lean_object* v___x_6153_; double v___x_6154_; uint8_t v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6163_; 
v___x_6152_ = lean_box(0);
v___x_6153_ = lean_box(0);
v___x_6154_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6155_ = 0;
v___x_6156_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6157_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6157_, 0, v_cls_6120_);
lean_ctor_set(v___x_6157_, 1, v___x_6153_);
lean_ctor_set(v___x_6157_, 2, v___x_6156_);
lean_ctor_set_float(v___x_6157_, sizeof(void*)*3, v___x_6154_);
lean_ctor_set_float(v___x_6157_, sizeof(void*)*3 + 8, v___x_6154_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*3 + 16, v___x_6155_);
v___x_6158_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6159_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6157_);
lean_ctor_set(v___x_6159_, 1, v_a_6129_);
lean_ctor_set(v___x_6159_, 2, v___x_6158_);
lean_inc(v_ref_6127_);
v___x_6160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6160_, 0, v_ref_6127_);
lean_ctor_set(v___x_6160_, 1, v___x_6159_);
v___x_6161_ = l_Lean_PersistentArray_push___redArg(v_traces_6148_, v___x_6160_);
if (v_isShared_6151_ == 0)
{
lean_ctor_set(v___x_6150_, 0, v___x_6161_);
v___x_6163_ = v___x_6150_;
goto v_reusejp_6162_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v___x_6161_);
lean_ctor_set_uint64(v_reuseFailAlloc_6171_, sizeof(void*)*1, v_tid_6147_);
v___x_6163_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6162_;
}
v_reusejp_6162_:
{
lean_object* v___x_6165_; 
if (v_isShared_6146_ == 0)
{
lean_ctor_set(v___x_6145_, 4, v___x_6163_);
v___x_6165_ = v___x_6145_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6170_; 
v_reuseFailAlloc_6170_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6170_, 0, v_env_6135_);
lean_ctor_set(v_reuseFailAlloc_6170_, 1, v_nextMacroScope_6136_);
lean_ctor_set(v_reuseFailAlloc_6170_, 2, v_ngen_6137_);
lean_ctor_set(v_reuseFailAlloc_6170_, 3, v_auxDeclNGen_6138_);
lean_ctor_set(v_reuseFailAlloc_6170_, 4, v___x_6163_);
lean_ctor_set(v_reuseFailAlloc_6170_, 5, v_cache_6139_);
lean_ctor_set(v_reuseFailAlloc_6170_, 6, v_recordedDeps_6140_);
lean_ctor_set(v_reuseFailAlloc_6170_, 7, v_messages_6141_);
lean_ctor_set(v_reuseFailAlloc_6170_, 8, v_infoState_6142_);
lean_ctor_set(v_reuseFailAlloc_6170_, 9, v_snapshotTasks_6143_);
v___x_6165_ = v_reuseFailAlloc_6170_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
lean_object* v___x_6166_; lean_object* v___x_6168_; 
v___x_6166_ = lean_st_ref_put(v___y_6125_, v___x_6165_);
if (v_isShared_6132_ == 0)
{
lean_ctor_set(v___x_6131_, 0, v___x_6152_);
v___x_6168_ = v___x_6131_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6152_);
v___x_6168_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
return v___x_6168_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6175_, lean_object* v_msg_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_){
_start:
{
lean_object* v_res_6182_; 
v_res_6182_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6175_, v_msg_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
lean_dec(v___y_6178_);
lean_dec_ref(v___y_6177_);
return v_res_6182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6183_){
_start:
{
if (lean_obj_tag(v_e_6183_) == 0)
{
uint8_t v___x_6184_; 
v___x_6184_ = 2;
return v___x_6184_;
}
else
{
lean_object* v_a_6185_; uint8_t v___x_6186_; 
v_a_6185_ = lean_ctor_get(v_e_6183_, 0);
v___x_6186_ = lean_unbox(v_a_6185_);
if (v___x_6186_ == 0)
{
uint8_t v___x_6187_; 
v___x_6187_ = 1;
return v___x_6187_;
}
else
{
uint8_t v___x_6188_; 
v___x_6188_ = 0;
return v___x_6188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6189_){
_start:
{
uint8_t v_res_6190_; lean_object* v_r_6191_; 
v_res_6190_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6189_);
lean_dec_ref(v_e_6189_);
v_r_6191_ = lean_box(v_res_6190_);
return v_r_6191_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6192_){
_start:
{
if (lean_obj_tag(v_x_6192_) == 0)
{
lean_object* v_a_6194_; lean_object* v___x_6196_; uint8_t v_isShared_6197_; uint8_t v_isSharedCheck_6201_; 
v_a_6194_ = lean_ctor_get(v_x_6192_, 0);
v_isSharedCheck_6201_ = !lean_is_exclusive(v_x_6192_);
if (v_isSharedCheck_6201_ == 0)
{
v___x_6196_ = v_x_6192_;
v_isShared_6197_ = v_isSharedCheck_6201_;
goto v_resetjp_6195_;
}
else
{
lean_inc(v_a_6194_);
lean_dec(v_x_6192_);
v___x_6196_ = lean_box(0);
v_isShared_6197_ = v_isSharedCheck_6201_;
goto v_resetjp_6195_;
}
v_resetjp_6195_:
{
lean_object* v___x_6199_; 
if (v_isShared_6197_ == 0)
{
lean_ctor_set_tag(v___x_6196_, 1);
v___x_6199_ = v___x_6196_;
goto v_reusejp_6198_;
}
else
{
lean_object* v_reuseFailAlloc_6200_; 
v_reuseFailAlloc_6200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6200_, 0, v_a_6194_);
v___x_6199_ = v_reuseFailAlloc_6200_;
goto v_reusejp_6198_;
}
v_reusejp_6198_:
{
return v___x_6199_;
}
}
}
else
{
lean_object* v_a_6202_; lean_object* v___x_6204_; uint8_t v_isShared_6205_; uint8_t v_isSharedCheck_6209_; 
v_a_6202_ = lean_ctor_get(v_x_6192_, 0);
v_isSharedCheck_6209_ = !lean_is_exclusive(v_x_6192_);
if (v_isSharedCheck_6209_ == 0)
{
v___x_6204_ = v_x_6192_;
v_isShared_6205_ = v_isSharedCheck_6209_;
goto v_resetjp_6203_;
}
else
{
lean_inc(v_a_6202_);
lean_dec(v_x_6192_);
v___x_6204_ = lean_box(0);
v_isShared_6205_ = v_isSharedCheck_6209_;
goto v_resetjp_6203_;
}
v_resetjp_6203_:
{
lean_object* v___x_6207_; 
if (v_isShared_6205_ == 0)
{
lean_ctor_set_tag(v___x_6204_, 0);
v___x_6207_ = v___x_6204_;
goto v_reusejp_6206_;
}
else
{
lean_object* v_reuseFailAlloc_6208_; 
v_reuseFailAlloc_6208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_a_6202_);
v___x_6207_ = v_reuseFailAlloc_6208_;
goto v_reusejp_6206_;
}
v_reusejp_6206_:
{
return v___x_6207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6210_, lean_object* v___y_6211_){
_start:
{
lean_object* v_res_6212_; 
v_res_6212_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6210_);
return v_res_6212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6213_, lean_object* v_opt_6214_){
_start:
{
lean_object* v_name_6215_; lean_object* v_defValue_6216_; lean_object* v_map_6217_; lean_object* v___x_6218_; 
v_name_6215_ = lean_ctor_get(v_opt_6214_, 0);
v_defValue_6216_ = lean_ctor_get(v_opt_6214_, 1);
v_map_6217_ = lean_ctor_get(v_opts_6213_, 0);
v___x_6218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6217_, v_name_6215_);
if (lean_obj_tag(v___x_6218_) == 0)
{
lean_inc(v_defValue_6216_);
return v_defValue_6216_;
}
else
{
lean_object* v_val_6219_; 
v_val_6219_ = lean_ctor_get(v___x_6218_, 0);
lean_inc(v_val_6219_);
lean_dec_ref_known(v___x_6218_, 1);
if (lean_obj_tag(v_val_6219_) == 3)
{
lean_object* v_v_6220_; 
v_v_6220_ = lean_ctor_get(v_val_6219_, 0);
lean_inc(v_v_6220_);
lean_dec_ref_known(v_val_6219_, 1);
return v_v_6220_;
}
else
{
lean_dec(v_val_6219_);
lean_inc(v_defValue_6216_);
return v_defValue_6216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6221_, lean_object* v_opt_6222_){
_start:
{
lean_object* v_res_6223_; 
v_res_6223_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6221_, v_opt_6222_);
lean_dec_ref(v_opt_6222_);
lean_dec_ref(v_opts_6221_);
return v_res_6223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6224_, size_t v_i_6225_, lean_object* v_bs_6226_){
_start:
{
uint8_t v___x_6227_; 
v___x_6227_ = lean_usize_dec_lt(v_i_6225_, v_sz_6224_);
if (v___x_6227_ == 0)
{
return v_bs_6226_;
}
else
{
lean_object* v_v_6228_; lean_object* v_msg_6229_; lean_object* v___x_6230_; lean_object* v_bs_x27_6231_; size_t v___x_6232_; size_t v___x_6233_; lean_object* v___x_6234_; 
v_v_6228_ = lean_array_uget_borrowed(v_bs_6226_, v_i_6225_);
v_msg_6229_ = lean_ctor_get(v_v_6228_, 1);
lean_inc_ref(v_msg_6229_);
v___x_6230_ = lean_unsigned_to_nat(0u);
v_bs_x27_6231_ = lean_array_uset(v_bs_6226_, v_i_6225_, v___x_6230_);
v___x_6232_ = ((size_t)1ULL);
v___x_6233_ = lean_usize_add(v_i_6225_, v___x_6232_);
v___x_6234_ = lean_array_uset(v_bs_x27_6231_, v_i_6225_, v_msg_6229_);
v_i_6225_ = v___x_6233_;
v_bs_6226_ = v___x_6234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6236_, lean_object* v_i_6237_, lean_object* v_bs_6238_){
_start:
{
size_t v_sz_boxed_6239_; size_t v_i_boxed_6240_; lean_object* v_res_6241_; 
v_sz_boxed_6239_ = lean_unbox_usize(v_sz_6236_);
lean_dec(v_sz_6236_);
v_i_boxed_6240_ = lean_unbox_usize(v_i_6237_);
lean_dec(v_i_6237_);
v_res_6241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6239_, v_i_boxed_6240_, v_bs_6238_);
return v_res_6241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6242_, lean_object* v_data_6243_, lean_object* v_ref_6244_, lean_object* v_msg_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_){
_start:
{
lean_object* v_toCold_6251_; lean_object* v_currRecDepth_6252_; lean_object* v_ref_6253_; uint16_t v_optionFlags_6254_; uint8_t v_suppressElabErrors_6255_; uint8_t v_isRecordingDeps_6256_; lean_object* v_ref_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v_traceState_6260_; lean_object* v_traces_6261_; lean_object* v___x_6262_; size_t v_sz_6263_; size_t v___x_6264_; lean_object* v___x_6265_; lean_object* v_msg_6266_; lean_object* v___x_6267_; lean_object* v_a_6268_; lean_object* v___x_6270_; uint8_t v_isShared_6271_; uint8_t v_isSharedCheck_6306_; 
v_toCold_6251_ = lean_ctor_get(v___y_6248_, 0);
v_currRecDepth_6252_ = lean_ctor_get(v___y_6248_, 1);
v_ref_6253_ = lean_ctor_get(v___y_6248_, 2);
v_optionFlags_6254_ = lean_ctor_get_uint16(v___y_6248_, sizeof(void*)*3);
v_suppressElabErrors_6255_ = lean_ctor_get_uint8(v___y_6248_, sizeof(void*)*3 + 2);
v_isRecordingDeps_6256_ = lean_ctor_get_uint8(v___y_6248_, sizeof(void*)*3 + 3);
v_ref_6257_ = l_Lean_replaceRef(v_ref_6244_, v_ref_6253_);
lean_inc(v_currRecDepth_6252_);
lean_inc_ref(v_toCold_6251_);
v___x_6258_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_6258_, 0, v_toCold_6251_);
lean_ctor_set(v___x_6258_, 1, v_currRecDepth_6252_);
lean_ctor_set(v___x_6258_, 2, v_ref_6257_);
lean_ctor_set_uint16(v___x_6258_, sizeof(void*)*3, v_optionFlags_6254_);
lean_ctor_set_uint8(v___x_6258_, sizeof(void*)*3 + 2, v_suppressElabErrors_6255_);
lean_ctor_set_uint8(v___x_6258_, sizeof(void*)*3 + 3, v_isRecordingDeps_6256_);
v___x_6259_ = lean_st_ref_get(v___y_6249_);
v_traceState_6260_ = lean_ctor_get(v___x_6259_, 4);
lean_inc_ref(v_traceState_6260_);
lean_dec(v___x_6259_);
v_traces_6261_ = lean_ctor_get(v_traceState_6260_, 0);
lean_inc_ref(v_traces_6261_);
lean_dec_ref(v_traceState_6260_);
v___x_6262_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6261_);
lean_dec_ref(v_traces_6261_);
v_sz_6263_ = lean_array_size(v___x_6262_);
v___x_6264_ = ((size_t)0ULL);
v___x_6265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6263_, v___x_6264_, v___x_6262_);
v_msg_6266_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6266_, 0, v_data_6243_);
lean_ctor_set(v_msg_6266_, 1, v_msg_6245_);
lean_ctor_set(v_msg_6266_, 2, v___x_6265_);
v___x_6267_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6266_, v___y_6246_, v___y_6247_, v___x_6258_, v___y_6249_);
lean_dec_ref_known(v___x_6258_, 3);
v_a_6268_ = lean_ctor_get(v___x_6267_, 0);
v_isSharedCheck_6306_ = !lean_is_exclusive(v___x_6267_);
if (v_isSharedCheck_6306_ == 0)
{
v___x_6270_ = v___x_6267_;
v_isShared_6271_ = v_isSharedCheck_6306_;
goto v_resetjp_6269_;
}
else
{
lean_inc(v_a_6268_);
lean_dec(v___x_6267_);
v___x_6270_ = lean_box(0);
v_isShared_6271_ = v_isSharedCheck_6306_;
goto v_resetjp_6269_;
}
v_resetjp_6269_:
{
lean_object* v___x_6272_; lean_object* v_traceState_6273_; lean_object* v_env_6274_; lean_object* v_nextMacroScope_6275_; lean_object* v_ngen_6276_; lean_object* v_auxDeclNGen_6277_; lean_object* v_cache_6278_; lean_object* v_recordedDeps_6279_; lean_object* v_messages_6280_; lean_object* v_infoState_6281_; lean_object* v_snapshotTasks_6282_; lean_object* v___x_6284_; uint8_t v_isShared_6285_; uint8_t v_isSharedCheck_6305_; 
v___x_6272_ = lean_st_ref_take(v___y_6249_);
v_traceState_6273_ = lean_ctor_get(v___x_6272_, 4);
v_env_6274_ = lean_ctor_get(v___x_6272_, 0);
v_nextMacroScope_6275_ = lean_ctor_get(v___x_6272_, 1);
v_ngen_6276_ = lean_ctor_get(v___x_6272_, 2);
v_auxDeclNGen_6277_ = lean_ctor_get(v___x_6272_, 3);
v_cache_6278_ = lean_ctor_get(v___x_6272_, 5);
v_recordedDeps_6279_ = lean_ctor_get(v___x_6272_, 6);
v_messages_6280_ = lean_ctor_get(v___x_6272_, 7);
v_infoState_6281_ = lean_ctor_get(v___x_6272_, 8);
v_snapshotTasks_6282_ = lean_ctor_get(v___x_6272_, 9);
v_isSharedCheck_6305_ = !lean_is_exclusive(v___x_6272_);
if (v_isSharedCheck_6305_ == 0)
{
v___x_6284_ = v___x_6272_;
v_isShared_6285_ = v_isSharedCheck_6305_;
goto v_resetjp_6283_;
}
else
{
lean_inc(v_snapshotTasks_6282_);
lean_inc(v_infoState_6281_);
lean_inc(v_messages_6280_);
lean_inc(v_recordedDeps_6279_);
lean_inc(v_cache_6278_);
lean_inc(v_traceState_6273_);
lean_inc(v_auxDeclNGen_6277_);
lean_inc(v_ngen_6276_);
lean_inc(v_nextMacroScope_6275_);
lean_inc(v_env_6274_);
lean_dec(v___x_6272_);
v___x_6284_ = lean_box(0);
v_isShared_6285_ = v_isSharedCheck_6305_;
goto v_resetjp_6283_;
}
v_resetjp_6283_:
{
uint64_t v_tid_6286_; lean_object* v___x_6288_; uint8_t v_isShared_6289_; uint8_t v_isSharedCheck_6303_; 
v_tid_6286_ = lean_ctor_get_uint64(v_traceState_6273_, sizeof(void*)*1);
v_isSharedCheck_6303_ = !lean_is_exclusive(v_traceState_6273_);
if (v_isSharedCheck_6303_ == 0)
{
lean_object* v_unused_6304_; 
v_unused_6304_ = lean_ctor_get(v_traceState_6273_, 0);
lean_dec(v_unused_6304_);
v___x_6288_ = v_traceState_6273_;
v_isShared_6289_ = v_isSharedCheck_6303_;
goto v_resetjp_6287_;
}
else
{
lean_dec(v_traceState_6273_);
v___x_6288_ = lean_box(0);
v_isShared_6289_ = v_isSharedCheck_6303_;
goto v_resetjp_6287_;
}
v_resetjp_6287_:
{
lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6294_; 
v___x_6290_ = lean_box(0);
v___x_6291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6291_, 0, v_ref_6244_);
lean_ctor_set(v___x_6291_, 1, v_a_6268_);
v___x_6292_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6242_, v___x_6291_);
if (v_isShared_6289_ == 0)
{
lean_ctor_set(v___x_6288_, 0, v___x_6292_);
v___x_6294_ = v___x_6288_;
goto v_reusejp_6293_;
}
else
{
lean_object* v_reuseFailAlloc_6302_; 
v_reuseFailAlloc_6302_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6302_, 0, v___x_6292_);
lean_ctor_set_uint64(v_reuseFailAlloc_6302_, sizeof(void*)*1, v_tid_6286_);
v___x_6294_ = v_reuseFailAlloc_6302_;
goto v_reusejp_6293_;
}
v_reusejp_6293_:
{
lean_object* v___x_6296_; 
if (v_isShared_6285_ == 0)
{
lean_ctor_set(v___x_6284_, 4, v___x_6294_);
v___x_6296_ = v___x_6284_;
goto v_reusejp_6295_;
}
else
{
lean_object* v_reuseFailAlloc_6301_; 
v_reuseFailAlloc_6301_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6301_, 0, v_env_6274_);
lean_ctor_set(v_reuseFailAlloc_6301_, 1, v_nextMacroScope_6275_);
lean_ctor_set(v_reuseFailAlloc_6301_, 2, v_ngen_6276_);
lean_ctor_set(v_reuseFailAlloc_6301_, 3, v_auxDeclNGen_6277_);
lean_ctor_set(v_reuseFailAlloc_6301_, 4, v___x_6294_);
lean_ctor_set(v_reuseFailAlloc_6301_, 5, v_cache_6278_);
lean_ctor_set(v_reuseFailAlloc_6301_, 6, v_recordedDeps_6279_);
lean_ctor_set(v_reuseFailAlloc_6301_, 7, v_messages_6280_);
lean_ctor_set(v_reuseFailAlloc_6301_, 8, v_infoState_6281_);
lean_ctor_set(v_reuseFailAlloc_6301_, 9, v_snapshotTasks_6282_);
v___x_6296_ = v_reuseFailAlloc_6301_;
goto v_reusejp_6295_;
}
v_reusejp_6295_:
{
lean_object* v___x_6297_; lean_object* v___x_6299_; 
v___x_6297_ = lean_st_ref_put(v___y_6249_, v___x_6296_);
if (v_isShared_6271_ == 0)
{
lean_ctor_set(v___x_6270_, 0, v___x_6290_);
v___x_6299_ = v___x_6270_;
goto v_reusejp_6298_;
}
else
{
lean_object* v_reuseFailAlloc_6300_; 
v_reuseFailAlloc_6300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6300_, 0, v___x_6290_);
v___x_6299_ = v_reuseFailAlloc_6300_;
goto v_reusejp_6298_;
}
v_reusejp_6298_:
{
return v___x_6299_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6307_, lean_object* v_data_6308_, lean_object* v_ref_6309_, lean_object* v_msg_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_){
_start:
{
lean_object* v_res_6316_; 
v_res_6316_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6307_, v_data_6308_, v_ref_6309_, v_msg_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_);
lean_dec(v___y_6314_);
lean_dec_ref(v___y_6313_);
lean_dec(v___y_6312_);
lean_dec_ref(v___y_6311_);
return v_res_6316_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6318_; lean_object* v___x_6319_; 
v___x_6318_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6319_ = l_Lean_stringToMessageData(v___x_6318_);
return v___x_6319_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6320_; double v___x_6321_; 
v___x_6320_ = lean_unsigned_to_nat(1000u);
v___x_6321_ = lean_float_of_nat(v___x_6320_);
return v___x_6321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6322_, uint8_t v_collapsed_6323_, lean_object* v_tag_6324_, lean_object* v_opts_6325_, uint8_t v_clsEnabled_6326_, lean_object* v_oldTraces_6327_, lean_object* v_msg_6328_, lean_object* v_resStartStop_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_){
_start:
{
lean_object* v_fst_6342_; lean_object* v_snd_6343_; lean_object* v___y_6345_; lean_object* v___y_6346_; lean_object* v_data_6347_; lean_object* v_fst_6358_; lean_object* v_snd_6359_; lean_object* v___x_6360_; uint8_t v___x_6361_; lean_object* v___y_6363_; lean_object* v_a_6364_; uint8_t v___y_6379_; double v___y_6411_; 
v_fst_6342_ = lean_ctor_get(v_resStartStop_6329_, 0);
lean_inc(v_fst_6342_);
v_snd_6343_ = lean_ctor_get(v_resStartStop_6329_, 1);
lean_inc(v_snd_6343_);
lean_dec_ref(v_resStartStop_6329_);
v_fst_6358_ = lean_ctor_get(v_snd_6343_, 0);
lean_inc(v_fst_6358_);
v_snd_6359_ = lean_ctor_get(v_snd_6343_, 1);
lean_inc(v_snd_6359_);
lean_dec(v_snd_6343_);
v___x_6360_ = l_Lean_trace_profiler;
v___x_6361_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6325_, v___x_6360_);
if (v___x_6361_ == 0)
{
v___y_6379_ = v___x_6361_;
goto v___jp_6378_;
}
else
{
lean_object* v___x_6416_; uint8_t v___x_6417_; 
v___x_6416_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6417_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6325_, v___x_6416_);
if (v___x_6417_ == 0)
{
lean_object* v___x_6418_; lean_object* v___x_6419_; double v___x_6420_; double v___x_6421_; double v___x_6422_; 
v___x_6418_ = l_Lean_trace_profiler_threshold;
v___x_6419_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6325_, v___x_6418_);
v___x_6420_ = lean_float_of_nat(v___x_6419_);
v___x_6421_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6422_ = lean_float_div(v___x_6420_, v___x_6421_);
v___y_6411_ = v___x_6422_;
goto v___jp_6410_;
}
else
{
lean_object* v___x_6423_; lean_object* v___x_6424_; double v___x_6425_; 
v___x_6423_ = l_Lean_trace_profiler_threshold;
v___x_6424_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6325_, v___x_6423_);
v___x_6425_ = lean_float_of_nat(v___x_6424_);
v___y_6411_ = v___x_6425_;
goto v___jp_6410_;
}
}
v___jp_6344_:
{
lean_object* v___x_6348_; 
lean_inc(v___y_6345_);
v___x_6348_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6327_, v_data_6347_, v___y_6345_, v___y_6346_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
if (lean_obj_tag(v___x_6348_) == 0)
{
lean_object* v___x_6349_; 
lean_dec_ref_known(v___x_6348_, 1);
v___x_6349_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6342_);
return v___x_6349_;
}
else
{
lean_object* v_a_6350_; lean_object* v___x_6352_; uint8_t v_isShared_6353_; uint8_t v_isSharedCheck_6357_; 
lean_dec(v_fst_6342_);
v_a_6350_ = lean_ctor_get(v___x_6348_, 0);
v_isSharedCheck_6357_ = !lean_is_exclusive(v___x_6348_);
if (v_isSharedCheck_6357_ == 0)
{
v___x_6352_ = v___x_6348_;
v_isShared_6353_ = v_isSharedCheck_6357_;
goto v_resetjp_6351_;
}
else
{
lean_inc(v_a_6350_);
lean_dec(v___x_6348_);
v___x_6352_ = lean_box(0);
v_isShared_6353_ = v_isSharedCheck_6357_;
goto v_resetjp_6351_;
}
v_resetjp_6351_:
{
lean_object* v___x_6355_; 
if (v_isShared_6353_ == 0)
{
v___x_6355_ = v___x_6352_;
goto v_reusejp_6354_;
}
else
{
lean_object* v_reuseFailAlloc_6356_; 
v_reuseFailAlloc_6356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6356_, 0, v_a_6350_);
v___x_6355_ = v_reuseFailAlloc_6356_;
goto v_reusejp_6354_;
}
v_reusejp_6354_:
{
return v___x_6355_;
}
}
}
}
v___jp_6362_:
{
uint8_t v_result_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; double v___x_6368_; lean_object* v_data_6369_; 
v_result_6365_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6342_);
v___x_6366_ = lean_box(v_result_6365_);
v___x_6367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6367_, 0, v___x_6366_);
v___x_6368_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6324_);
lean_inc_ref(v___x_6367_);
lean_inc(v_cls_6322_);
v_data_6369_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6369_, 0, v_cls_6322_);
lean_ctor_set(v_data_6369_, 1, v___x_6367_);
lean_ctor_set(v_data_6369_, 2, v_tag_6324_);
lean_ctor_set_float(v_data_6369_, sizeof(void*)*3, v___x_6368_);
lean_ctor_set_float(v_data_6369_, sizeof(void*)*3 + 8, v___x_6368_);
lean_ctor_set_uint8(v_data_6369_, sizeof(void*)*3 + 16, v_collapsed_6323_);
if (v___x_6361_ == 0)
{
lean_dec_ref_known(v___x_6367_, 1);
lean_dec(v_snd_6359_);
lean_dec(v_fst_6358_);
lean_dec_ref(v_tag_6324_);
lean_dec(v_cls_6322_);
v___y_6345_ = v___y_6363_;
v___y_6346_ = v_a_6364_;
v_data_6347_ = v_data_6369_;
goto v___jp_6344_;
}
else
{
lean_object* v_data_6370_; double v___x_6371_; double v___x_6372_; 
lean_dec_ref_known(v_data_6369_, 3);
v_data_6370_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6370_, 0, v_cls_6322_);
lean_ctor_set(v_data_6370_, 1, v___x_6367_);
lean_ctor_set(v_data_6370_, 2, v_tag_6324_);
v___x_6371_ = lean_unbox_float(v_fst_6358_);
lean_dec(v_fst_6358_);
lean_ctor_set_float(v_data_6370_, sizeof(void*)*3, v___x_6371_);
v___x_6372_ = lean_unbox_float(v_snd_6359_);
lean_dec(v_snd_6359_);
lean_ctor_set_float(v_data_6370_, sizeof(void*)*3 + 8, v___x_6372_);
lean_ctor_set_uint8(v_data_6370_, sizeof(void*)*3 + 16, v_collapsed_6323_);
v___y_6345_ = v___y_6363_;
v___y_6346_ = v_a_6364_;
v_data_6347_ = v_data_6370_;
goto v___jp_6344_;
}
}
v___jp_6373_:
{
lean_object* v_ref_6374_; lean_object* v___x_6375_; 
v_ref_6374_ = lean_ctor_get(v___y_6339_, 2);
lean_inc(v___y_6340_);
lean_inc_ref(v___y_6339_);
lean_inc(v___y_6338_);
lean_inc_ref(v___y_6337_);
lean_inc(v___y_6336_);
lean_inc_ref(v___y_6335_);
lean_inc(v___y_6334_);
lean_inc_ref(v___y_6333_);
lean_inc(v___y_6332_);
lean_inc(v___y_6331_);
lean_inc_ref(v___y_6330_);
lean_inc(v_fst_6342_);
v___x_6375_ = lean_apply_13(v_msg_6328_, v_fst_6342_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_, lean_box(0));
if (lean_obj_tag(v___x_6375_) == 0)
{
lean_object* v_a_6376_; 
v_a_6376_ = lean_ctor_get(v___x_6375_, 0);
lean_inc(v_a_6376_);
lean_dec_ref_known(v___x_6375_, 1);
v___y_6363_ = v_ref_6374_;
v_a_6364_ = v_a_6376_;
goto v___jp_6362_;
}
else
{
lean_object* v___x_6377_; 
lean_dec_ref_known(v___x_6375_, 1);
v___x_6377_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6363_ = v_ref_6374_;
v_a_6364_ = v___x_6377_;
goto v___jp_6362_;
}
}
v___jp_6378_:
{
if (v_clsEnabled_6326_ == 0)
{
if (v___y_6379_ == 0)
{
lean_object* v___x_6380_; lean_object* v_traceState_6381_; lean_object* v_env_6382_; lean_object* v_nextMacroScope_6383_; lean_object* v_ngen_6384_; lean_object* v_auxDeclNGen_6385_; lean_object* v_cache_6386_; lean_object* v_recordedDeps_6387_; lean_object* v_messages_6388_; lean_object* v_infoState_6389_; lean_object* v_snapshotTasks_6390_; lean_object* v___x_6392_; uint8_t v_isShared_6393_; uint8_t v_isSharedCheck_6409_; 
lean_dec(v_snd_6359_);
lean_dec(v_fst_6358_);
lean_dec_ref(v_msg_6328_);
lean_dec_ref(v_tag_6324_);
lean_dec(v_cls_6322_);
v___x_6380_ = lean_st_ref_take(v___y_6340_);
v_traceState_6381_ = lean_ctor_get(v___x_6380_, 4);
v_env_6382_ = lean_ctor_get(v___x_6380_, 0);
v_nextMacroScope_6383_ = lean_ctor_get(v___x_6380_, 1);
v_ngen_6384_ = lean_ctor_get(v___x_6380_, 2);
v_auxDeclNGen_6385_ = lean_ctor_get(v___x_6380_, 3);
v_cache_6386_ = lean_ctor_get(v___x_6380_, 5);
v_recordedDeps_6387_ = lean_ctor_get(v___x_6380_, 6);
v_messages_6388_ = lean_ctor_get(v___x_6380_, 7);
v_infoState_6389_ = lean_ctor_get(v___x_6380_, 8);
v_snapshotTasks_6390_ = lean_ctor_get(v___x_6380_, 9);
v_isSharedCheck_6409_ = !lean_is_exclusive(v___x_6380_);
if (v_isSharedCheck_6409_ == 0)
{
v___x_6392_ = v___x_6380_;
v_isShared_6393_ = v_isSharedCheck_6409_;
goto v_resetjp_6391_;
}
else
{
lean_inc(v_snapshotTasks_6390_);
lean_inc(v_infoState_6389_);
lean_inc(v_messages_6388_);
lean_inc(v_recordedDeps_6387_);
lean_inc(v_cache_6386_);
lean_inc(v_traceState_6381_);
lean_inc(v_auxDeclNGen_6385_);
lean_inc(v_ngen_6384_);
lean_inc(v_nextMacroScope_6383_);
lean_inc(v_env_6382_);
lean_dec(v___x_6380_);
v___x_6392_ = lean_box(0);
v_isShared_6393_ = v_isSharedCheck_6409_;
goto v_resetjp_6391_;
}
v_resetjp_6391_:
{
uint64_t v_tid_6394_; lean_object* v_traces_6395_; lean_object* v___x_6397_; uint8_t v_isShared_6398_; uint8_t v_isSharedCheck_6408_; 
v_tid_6394_ = lean_ctor_get_uint64(v_traceState_6381_, sizeof(void*)*1);
v_traces_6395_ = lean_ctor_get(v_traceState_6381_, 0);
v_isSharedCheck_6408_ = !lean_is_exclusive(v_traceState_6381_);
if (v_isSharedCheck_6408_ == 0)
{
v___x_6397_ = v_traceState_6381_;
v_isShared_6398_ = v_isSharedCheck_6408_;
goto v_resetjp_6396_;
}
else
{
lean_inc(v_traces_6395_);
lean_dec(v_traceState_6381_);
v___x_6397_ = lean_box(0);
v_isShared_6398_ = v_isSharedCheck_6408_;
goto v_resetjp_6396_;
}
v_resetjp_6396_:
{
lean_object* v___x_6399_; lean_object* v___x_6401_; 
v___x_6399_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6327_, v_traces_6395_);
lean_dec_ref(v_traces_6395_);
if (v_isShared_6398_ == 0)
{
lean_ctor_set(v___x_6397_, 0, v___x_6399_);
v___x_6401_ = v___x_6397_;
goto v_reusejp_6400_;
}
else
{
lean_object* v_reuseFailAlloc_6407_; 
v_reuseFailAlloc_6407_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6407_, 0, v___x_6399_);
lean_ctor_set_uint64(v_reuseFailAlloc_6407_, sizeof(void*)*1, v_tid_6394_);
v___x_6401_ = v_reuseFailAlloc_6407_;
goto v_reusejp_6400_;
}
v_reusejp_6400_:
{
lean_object* v___x_6403_; 
if (v_isShared_6393_ == 0)
{
lean_ctor_set(v___x_6392_, 4, v___x_6401_);
v___x_6403_ = v___x_6392_;
goto v_reusejp_6402_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v_env_6382_);
lean_ctor_set(v_reuseFailAlloc_6406_, 1, v_nextMacroScope_6383_);
lean_ctor_set(v_reuseFailAlloc_6406_, 2, v_ngen_6384_);
lean_ctor_set(v_reuseFailAlloc_6406_, 3, v_auxDeclNGen_6385_);
lean_ctor_set(v_reuseFailAlloc_6406_, 4, v___x_6401_);
lean_ctor_set(v_reuseFailAlloc_6406_, 5, v_cache_6386_);
lean_ctor_set(v_reuseFailAlloc_6406_, 6, v_recordedDeps_6387_);
lean_ctor_set(v_reuseFailAlloc_6406_, 7, v_messages_6388_);
lean_ctor_set(v_reuseFailAlloc_6406_, 8, v_infoState_6389_);
lean_ctor_set(v_reuseFailAlloc_6406_, 9, v_snapshotTasks_6390_);
v___x_6403_ = v_reuseFailAlloc_6406_;
goto v_reusejp_6402_;
}
v_reusejp_6402_:
{
lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6404_ = lean_st_ref_put(v___y_6340_, v___x_6403_);
v___x_6405_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6342_);
return v___x_6405_;
}
}
}
}
}
else
{
goto v___jp_6373_;
}
}
else
{
goto v___jp_6373_;
}
}
v___jp_6410_:
{
double v___x_6412_; double v___x_6413_; double v___x_6414_; uint8_t v___x_6415_; 
v___x_6412_ = lean_unbox_float(v_snd_6359_);
v___x_6413_ = lean_unbox_float(v_fst_6358_);
v___x_6414_ = lean_float_sub(v___x_6412_, v___x_6413_);
v___x_6415_ = lean_float_decLt(v___y_6411_, v___x_6414_);
v___y_6379_ = v___x_6415_;
goto v___jp_6378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6426_ = _args[0];
lean_object* v_collapsed_6427_ = _args[1];
lean_object* v_tag_6428_ = _args[2];
lean_object* v_opts_6429_ = _args[3];
lean_object* v_clsEnabled_6430_ = _args[4];
lean_object* v_oldTraces_6431_ = _args[5];
lean_object* v_msg_6432_ = _args[6];
lean_object* v_resStartStop_6433_ = _args[7];
lean_object* v___y_6434_ = _args[8];
lean_object* v___y_6435_ = _args[9];
lean_object* v___y_6436_ = _args[10];
lean_object* v___y_6437_ = _args[11];
lean_object* v___y_6438_ = _args[12];
lean_object* v___y_6439_ = _args[13];
lean_object* v___y_6440_ = _args[14];
lean_object* v___y_6441_ = _args[15];
lean_object* v___y_6442_ = _args[16];
lean_object* v___y_6443_ = _args[17];
lean_object* v___y_6444_ = _args[18];
lean_object* v___y_6445_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6446_; uint8_t v_clsEnabled_boxed_6447_; lean_object* v_res_6448_; 
v_collapsed_boxed_6446_ = lean_unbox(v_collapsed_6427_);
v_clsEnabled_boxed_6447_ = lean_unbox(v_clsEnabled_6430_);
v_res_6448_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6426_, v_collapsed_boxed_6446_, v_tag_6428_, v_opts_6429_, v_clsEnabled_boxed_6447_, v_oldTraces_6431_, v_msg_6432_, v_resStartStop_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_);
lean_dec(v___y_6444_);
lean_dec_ref(v___y_6443_);
lean_dec(v___y_6442_);
lean_dec_ref(v___y_6441_);
lean_dec(v___y_6440_);
lean_dec_ref(v___y_6439_);
lean_dec(v___y_6438_);
lean_dec_ref(v___y_6437_);
lean_dec(v___y_6436_);
lean_dec(v___y_6435_);
lean_dec_ref(v___y_6434_);
lean_dec_ref(v_opts_6429_);
return v_res_6448_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6454_ = l_Lean_stringToMessageData(v___x_6453_);
return v___x_6454_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6455_, lean_object* v_b_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_){
_start:
{
if (lean_obj_tag(v_as_x27_6455_) == 0)
{
lean_object* v___x_6469_; 
v___x_6469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6469_, 0, v_b_6456_);
return v___x_6469_;
}
else
{
lean_object* v_head_6470_; lean_object* v_toCold_6471_; lean_object* v_options_6472_; lean_object* v_tail_6473_; lean_object* v_name_6474_; lean_object* v_run_x27_6475_; lean_object* v_inheritedTraceOptions_6476_; uint8_t v_hasTrace_6477_; lean_object* v___x_6478_; uint8_t v___y_6480_; lean_object* v___x_6485_; lean_object* v___y_6487_; 
lean_dec_ref(v_b_6456_);
v_head_6470_ = lean_ctor_get(v_as_x27_6455_, 0);
v_toCold_6471_ = lean_ctor_get(v___y_6466_, 0);
v_options_6472_ = lean_ctor_get(v_toCold_6471_, 2);
v_tail_6473_ = lean_ctor_get(v_as_x27_6455_, 1);
v_name_6474_ = lean_ctor_get(v_head_6470_, 0);
v_run_x27_6475_ = lean_ctor_get(v_head_6470_, 1);
v_inheritedTraceOptions_6476_ = lean_ctor_get(v_toCold_6471_, 11);
v_hasTrace_6477_ = lean_ctor_get_uint8(v_options_6472_, sizeof(void*)*1);
v___x_6478_ = lean_box(0);
v___x_6485_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6477_ == 0)
{
lean_object* v___x_6515_; 
lean_inc_ref(v_run_x27_6475_);
lean_inc(v___y_6467_);
lean_inc_ref(v___y_6466_);
lean_inc(v___y_6465_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6463_);
lean_inc_ref(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
v___x_6515_ = lean_apply_12(v_run_x27_6475_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, lean_box(0));
v___y_6487_ = v___x_6515_;
goto v___jp_6486_;
}
else
{
lean_object* v___f_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; uint8_t v___x_6520_; lean_object* v___y_6522_; lean_object* v___y_6523_; lean_object* v_a_6524_; lean_object* v___y_6537_; lean_object* v___y_6538_; lean_object* v_a_6539_; 
lean_inc(v_name_6474_);
v___f_6516_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6516_, 0, v_name_6474_);
v___x_6517_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6518_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6519_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6520_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6476_, v_options_6472_, v___x_6519_);
if (v___x_6520_ == 0)
{
lean_object* v___x_6589_; uint8_t v___x_6590_; 
v___x_6589_ = l_Lean_trace_profiler;
v___x_6590_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6472_, v___x_6589_);
if (v___x_6590_ == 0)
{
lean_object* v___x_6591_; 
lean_dec_ref(v___f_6516_);
lean_inc_ref(v_run_x27_6475_);
lean_inc(v___y_6467_);
lean_inc_ref(v___y_6466_);
lean_inc(v___y_6465_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6463_);
lean_inc_ref(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
v___x_6591_ = lean_apply_12(v_run_x27_6475_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, lean_box(0));
v___y_6487_ = v___x_6591_;
goto v___jp_6486_;
}
else
{
goto v___jp_6548_;
}
}
else
{
goto v___jp_6548_;
}
v___jp_6521_:
{
lean_object* v___x_6525_; double v___x_6526_; double v___x_6527_; double v___x_6528_; double v___x_6529_; double v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; 
v___x_6525_ = lean_io_mono_nanos_now();
v___x_6526_ = lean_float_of_nat(v___y_6523_);
v___x_6527_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6528_ = lean_float_div(v___x_6526_, v___x_6527_);
v___x_6529_ = lean_float_of_nat(v___x_6525_);
v___x_6530_ = lean_float_div(v___x_6529_, v___x_6527_);
v___x_6531_ = lean_box_float(v___x_6528_);
v___x_6532_ = lean_box_float(v___x_6530_);
v___x_6533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6533_, 0, v___x_6531_);
lean_ctor_set(v___x_6533_, 1, v___x_6532_);
v___x_6534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6534_, 0, v_a_6524_);
lean_ctor_set(v___x_6534_, 1, v___x_6533_);
v___x_6535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6517_, v_hasTrace_6477_, v___x_6518_, v_options_6472_, v___x_6520_, v___y_6522_, v___f_6516_, v___x_6534_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_);
v___y_6487_ = v___x_6535_;
goto v___jp_6486_;
}
v___jp_6536_:
{
lean_object* v___x_6540_; double v___x_6541_; double v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; 
v___x_6540_ = lean_io_get_num_heartbeats();
v___x_6541_ = lean_float_of_nat(v___y_6538_);
v___x_6542_ = lean_float_of_nat(v___x_6540_);
v___x_6543_ = lean_box_float(v___x_6541_);
v___x_6544_ = lean_box_float(v___x_6542_);
v___x_6545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6545_, 0, v___x_6543_);
lean_ctor_set(v___x_6545_, 1, v___x_6544_);
v___x_6546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6546_, 0, v_a_6539_);
lean_ctor_set(v___x_6546_, 1, v___x_6545_);
v___x_6547_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6517_, v_hasTrace_6477_, v___x_6518_, v_options_6472_, v___x_6520_, v___y_6537_, v___f_6516_, v___x_6546_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_);
v___y_6487_ = v___x_6547_;
goto v___jp_6486_;
}
v___jp_6548_:
{
lean_object* v___x_6549_; lean_object* v_a_6550_; lean_object* v___x_6551_; uint8_t v___x_6552_; 
v___x_6549_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6467_);
v_a_6550_ = lean_ctor_get(v___x_6549_, 0);
lean_inc(v_a_6550_);
lean_dec_ref(v___x_6549_);
v___x_6551_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6552_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6472_, v___x_6551_);
if (v___x_6552_ == 0)
{
lean_object* v___x_6553_; lean_object* v___x_6554_; 
v___x_6553_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_6475_);
lean_inc(v___y_6467_);
lean_inc_ref(v___y_6466_);
lean_inc(v___y_6465_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6463_);
lean_inc_ref(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
v___x_6554_ = lean_apply_12(v_run_x27_6475_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, lean_box(0));
if (lean_obj_tag(v___x_6554_) == 0)
{
lean_object* v_a_6555_; lean_object* v___x_6557_; uint8_t v_isShared_6558_; uint8_t v_isSharedCheck_6562_; 
v_a_6555_ = lean_ctor_get(v___x_6554_, 0);
v_isSharedCheck_6562_ = !lean_is_exclusive(v___x_6554_);
if (v_isSharedCheck_6562_ == 0)
{
v___x_6557_ = v___x_6554_;
v_isShared_6558_ = v_isSharedCheck_6562_;
goto v_resetjp_6556_;
}
else
{
lean_inc(v_a_6555_);
lean_dec(v___x_6554_);
v___x_6557_ = lean_box(0);
v_isShared_6558_ = v_isSharedCheck_6562_;
goto v_resetjp_6556_;
}
v_resetjp_6556_:
{
lean_object* v___x_6560_; 
if (v_isShared_6558_ == 0)
{
lean_ctor_set_tag(v___x_6557_, 1);
v___x_6560_ = v___x_6557_;
goto v_reusejp_6559_;
}
else
{
lean_object* v_reuseFailAlloc_6561_; 
v_reuseFailAlloc_6561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6561_, 0, v_a_6555_);
v___x_6560_ = v_reuseFailAlloc_6561_;
goto v_reusejp_6559_;
}
v_reusejp_6559_:
{
v___y_6522_ = v_a_6550_;
v___y_6523_ = v___x_6553_;
v_a_6524_ = v___x_6560_;
goto v___jp_6521_;
}
}
}
else
{
lean_object* v_a_6563_; lean_object* v___x_6565_; uint8_t v_isShared_6566_; uint8_t v_isSharedCheck_6570_; 
v_a_6563_ = lean_ctor_get(v___x_6554_, 0);
v_isSharedCheck_6570_ = !lean_is_exclusive(v___x_6554_);
if (v_isSharedCheck_6570_ == 0)
{
v___x_6565_ = v___x_6554_;
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
else
{
lean_inc(v_a_6563_);
lean_dec(v___x_6554_);
v___x_6565_ = lean_box(0);
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
v_resetjp_6564_:
{
lean_object* v___x_6568_; 
if (v_isShared_6566_ == 0)
{
lean_ctor_set_tag(v___x_6565_, 0);
v___x_6568_ = v___x_6565_;
goto v_reusejp_6567_;
}
else
{
lean_object* v_reuseFailAlloc_6569_; 
v_reuseFailAlloc_6569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6569_, 0, v_a_6563_);
v___x_6568_ = v_reuseFailAlloc_6569_;
goto v_reusejp_6567_;
}
v_reusejp_6567_:
{
v___y_6522_ = v_a_6550_;
v___y_6523_ = v___x_6553_;
v_a_6524_ = v___x_6568_;
goto v___jp_6521_;
}
}
}
}
else
{
lean_object* v___x_6571_; lean_object* v___x_6572_; 
v___x_6571_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_6475_);
lean_inc(v___y_6467_);
lean_inc_ref(v___y_6466_);
lean_inc(v___y_6465_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6463_);
lean_inc_ref(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
v___x_6572_ = lean_apply_12(v_run_x27_6475_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, lean_box(0));
if (lean_obj_tag(v___x_6572_) == 0)
{
lean_object* v_a_6573_; lean_object* v___x_6575_; uint8_t v_isShared_6576_; uint8_t v_isSharedCheck_6580_; 
v_a_6573_ = lean_ctor_get(v___x_6572_, 0);
v_isSharedCheck_6580_ = !lean_is_exclusive(v___x_6572_);
if (v_isSharedCheck_6580_ == 0)
{
v___x_6575_ = v___x_6572_;
v_isShared_6576_ = v_isSharedCheck_6580_;
goto v_resetjp_6574_;
}
else
{
lean_inc(v_a_6573_);
lean_dec(v___x_6572_);
v___x_6575_ = lean_box(0);
v_isShared_6576_ = v_isSharedCheck_6580_;
goto v_resetjp_6574_;
}
v_resetjp_6574_:
{
lean_object* v___x_6578_; 
if (v_isShared_6576_ == 0)
{
lean_ctor_set_tag(v___x_6575_, 1);
v___x_6578_ = v___x_6575_;
goto v_reusejp_6577_;
}
else
{
lean_object* v_reuseFailAlloc_6579_; 
v_reuseFailAlloc_6579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_a_6573_);
v___x_6578_ = v_reuseFailAlloc_6579_;
goto v_reusejp_6577_;
}
v_reusejp_6577_:
{
v___y_6537_ = v_a_6550_;
v___y_6538_ = v___x_6571_;
v_a_6539_ = v___x_6578_;
goto v___jp_6536_;
}
}
}
else
{
lean_object* v_a_6581_; lean_object* v___x_6583_; uint8_t v_isShared_6584_; uint8_t v_isSharedCheck_6588_; 
v_a_6581_ = lean_ctor_get(v___x_6572_, 0);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___x_6572_);
if (v_isSharedCheck_6588_ == 0)
{
v___x_6583_ = v___x_6572_;
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
else
{
lean_inc(v_a_6581_);
lean_dec(v___x_6572_);
v___x_6583_ = lean_box(0);
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
v_resetjp_6582_:
{
lean_object* v___x_6586_; 
if (v_isShared_6584_ == 0)
{
lean_ctor_set_tag(v___x_6583_, 0);
v___x_6586_ = v___x_6583_;
goto v_reusejp_6585_;
}
else
{
lean_object* v_reuseFailAlloc_6587_; 
v_reuseFailAlloc_6587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6587_, 0, v_a_6581_);
v___x_6586_ = v_reuseFailAlloc_6587_;
goto v_reusejp_6585_;
}
v_reusejp_6585_:
{
v___y_6537_ = v_a_6550_;
v___y_6538_ = v___x_6571_;
v_a_6539_ = v___x_6586_;
goto v___jp_6536_;
}
}
}
}
}
}
v___jp_6479_:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v___x_6481_ = lean_box(v___y_6480_);
v___x_6482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6482_, 0, v___x_6481_);
v___x_6483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6483_, 0, v___x_6482_);
lean_ctor_set(v___x_6483_, 1, v___x_6478_);
v___x_6484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6484_, 0, v___x_6483_);
return v___x_6484_;
}
v___jp_6486_:
{
if (lean_obj_tag(v___y_6487_) == 0)
{
lean_object* v_a_6488_; uint8_t v___x_6489_; 
v_a_6488_ = lean_ctor_get(v___y_6487_, 0);
lean_inc(v_a_6488_);
lean_dec_ref_known(v___y_6487_, 1);
v___x_6489_ = lean_unbox(v_a_6488_);
if (v___x_6489_ == 0)
{
lean_dec(v_a_6488_);
v_as_x27_6455_ = v_tail_6473_;
v_b_6456_ = v___x_6485_;
goto _start;
}
else
{
if (v_hasTrace_6477_ == 0)
{
uint8_t v___x_6491_; 
v___x_6491_ = lean_unbox(v_a_6488_);
lean_dec(v_a_6488_);
v___y_6480_ = v___x_6491_;
goto v___jp_6479_;
}
else
{
lean_object* v___x_6492_; lean_object* v___x_6493_; uint8_t v___x_6494_; 
v___x_6492_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6493_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6494_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6476_, v_options_6472_, v___x_6493_);
if (v___x_6494_ == 0)
{
uint8_t v___x_6495_; 
v___x_6495_ = lean_unbox(v_a_6488_);
lean_dec(v_a_6488_);
v___y_6480_ = v___x_6495_;
goto v___jp_6479_;
}
else
{
lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6496_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_6497_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6492_, v___x_6496_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_);
if (lean_obj_tag(v___x_6497_) == 0)
{
uint8_t v___x_6498_; 
lean_dec_ref_known(v___x_6497_, 1);
v___x_6498_ = lean_unbox(v_a_6488_);
lean_dec(v_a_6488_);
v___y_6480_ = v___x_6498_;
goto v___jp_6479_;
}
else
{
lean_object* v_a_6499_; lean_object* v___x_6501_; uint8_t v_isShared_6502_; uint8_t v_isSharedCheck_6506_; 
lean_dec(v_a_6488_);
v_a_6499_ = lean_ctor_get(v___x_6497_, 0);
v_isSharedCheck_6506_ = !lean_is_exclusive(v___x_6497_);
if (v_isSharedCheck_6506_ == 0)
{
v___x_6501_ = v___x_6497_;
v_isShared_6502_ = v_isSharedCheck_6506_;
goto v_resetjp_6500_;
}
else
{
lean_inc(v_a_6499_);
lean_dec(v___x_6497_);
v___x_6501_ = lean_box(0);
v_isShared_6502_ = v_isSharedCheck_6506_;
goto v_resetjp_6500_;
}
v_resetjp_6500_:
{
lean_object* v___x_6504_; 
if (v_isShared_6502_ == 0)
{
v___x_6504_ = v___x_6501_;
goto v_reusejp_6503_;
}
else
{
lean_object* v_reuseFailAlloc_6505_; 
v_reuseFailAlloc_6505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6505_, 0, v_a_6499_);
v___x_6504_ = v_reuseFailAlloc_6505_;
goto v_reusejp_6503_;
}
v_reusejp_6503_:
{
return v___x_6504_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6507_; lean_object* v___x_6509_; uint8_t v_isShared_6510_; uint8_t v_isSharedCheck_6514_; 
v_a_6507_ = lean_ctor_get(v___y_6487_, 0);
v_isSharedCheck_6514_ = !lean_is_exclusive(v___y_6487_);
if (v_isSharedCheck_6514_ == 0)
{
v___x_6509_ = v___y_6487_;
v_isShared_6510_ = v_isSharedCheck_6514_;
goto v_resetjp_6508_;
}
else
{
lean_inc(v_a_6507_);
lean_dec(v___y_6487_);
v___x_6509_ = lean_box(0);
v_isShared_6510_ = v_isSharedCheck_6514_;
goto v_resetjp_6508_;
}
v_resetjp_6508_:
{
lean_object* v___x_6512_; 
if (v_isShared_6510_ == 0)
{
v___x_6512_ = v___x_6509_;
goto v_reusejp_6511_;
}
else
{
lean_object* v_reuseFailAlloc_6513_; 
v_reuseFailAlloc_6513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6513_, 0, v_a_6507_);
v___x_6512_ = v_reuseFailAlloc_6513_;
goto v_reusejp_6511_;
}
v_reusejp_6511_:
{
return v___x_6512_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_6592_, lean_object* v_b_6593_, lean_object* v___y_6594_, lean_object* v___y_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_, lean_object* v___y_6604_, lean_object* v___y_6605_){
_start:
{
lean_object* v_res_6606_; 
v_res_6606_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6592_, v_b_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_);
lean_dec(v___y_6604_);
lean_dec_ref(v___y_6603_);
lean_dec(v___y_6602_);
lean_dec_ref(v___y_6601_);
lean_dec(v___y_6600_);
lean_dec_ref(v___y_6599_);
lean_dec(v___y_6598_);
lean_dec_ref(v___y_6597_);
lean_dec(v___y_6596_);
lean_dec(v___y_6595_);
lean_dec_ref(v___y_6594_);
lean_dec(v_as_x27_6592_);
return v_res_6606_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_6609_; lean_object* v___x_6610_; 
v___x_6609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_6610_ = l_Lean_stringToMessageData(v___x_6609_);
return v___x_6610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_6612_; lean_object* v___x_6613_; 
v___x_6612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_6613_ = l_Lean_stringToMessageData(v___x_6612_);
return v___x_6613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_){
_start:
{
lean_object* v___x_6627_; lean_object* v___x_6628_; 
v___x_6627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_6628_ = l_Lean_Core_checkSystem(v___x_6627_, v_a_6624_, v_a_6625_);
if (lean_obj_tag(v___x_6628_) == 0)
{
lean_object* v___x_6629_; lean_object* v_caches_6630_; lean_object* v_typeAnalysis_6631_; lean_object* v_target_6632_; lean_object* v_hypotheses_6633_; lean_object* v___x_6635_; uint8_t v_isShared_6636_; uint8_t v_isSharedCheck_6718_; 
lean_dec_ref_known(v___x_6628_, 1);
v___x_6629_ = lean_st_ref_take(v_a_6616_);
v_caches_6630_ = lean_ctor_get(v___x_6629_, 0);
v_typeAnalysis_6631_ = lean_ctor_get(v___x_6629_, 1);
v_target_6632_ = lean_ctor_get(v___x_6629_, 2);
v_hypotheses_6633_ = lean_ctor_get(v___x_6629_, 3);
v_isSharedCheck_6718_ = !lean_is_exclusive(v___x_6629_);
if (v_isSharedCheck_6718_ == 0)
{
v___x_6635_ = v___x_6629_;
v_isShared_6636_ = v_isSharedCheck_6718_;
goto v_resetjp_6634_;
}
else
{
lean_inc(v_hypotheses_6633_);
lean_inc(v_target_6632_);
lean_inc(v_typeAnalysis_6631_);
lean_inc(v_caches_6630_);
lean_dec(v___x_6629_);
v___x_6635_ = lean_box(0);
v_isShared_6636_ = v_isSharedCheck_6718_;
goto v_resetjp_6634_;
}
v_resetjp_6634_:
{
uint8_t v___x_6637_; lean_object* v___x_6639_; 
v___x_6637_ = 0;
if (v_isShared_6636_ == 0)
{
v___x_6639_ = v___x_6635_;
goto v_reusejp_6638_;
}
else
{
lean_object* v_reuseFailAlloc_6717_; 
v_reuseFailAlloc_6717_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6717_, 0, v_caches_6630_);
lean_ctor_set(v_reuseFailAlloc_6717_, 1, v_typeAnalysis_6631_);
lean_ctor_set(v_reuseFailAlloc_6717_, 2, v_target_6632_);
lean_ctor_set(v_reuseFailAlloc_6717_, 3, v_hypotheses_6633_);
v___x_6639_ = v_reuseFailAlloc_6717_;
goto v_reusejp_6638_;
}
v_reusejp_6638_:
{
lean_object* v___x_6640_; lean_object* v___x_6641_; lean_object* v___x_6642_; 
lean_ctor_set_uint8(v___x_6639_, sizeof(void*)*4, v___x_6637_);
v___x_6640_ = lean_st_ref_put(v_a_6616_, v___x_6639_);
v___x_6641_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_6642_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_6614_, v___x_6641_, v_a_6615_, v_a_6616_, v_a_6617_, v_a_6618_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_, v_a_6623_, v_a_6624_, v_a_6625_);
if (lean_obj_tag(v___x_6642_) == 0)
{
lean_object* v_a_6643_; lean_object* v___x_6645_; uint8_t v_isShared_6646_; uint8_t v_isSharedCheck_6708_; 
v_a_6643_ = lean_ctor_get(v___x_6642_, 0);
v_isSharedCheck_6708_ = !lean_is_exclusive(v___x_6642_);
if (v_isSharedCheck_6708_ == 0)
{
v___x_6645_ = v___x_6642_;
v_isShared_6646_ = v_isSharedCheck_6708_;
goto v_resetjp_6644_;
}
else
{
lean_inc(v_a_6643_);
lean_dec(v___x_6642_);
v___x_6645_ = lean_box(0);
v_isShared_6646_ = v_isSharedCheck_6708_;
goto v_resetjp_6644_;
}
v_resetjp_6644_:
{
lean_object* v_fst_6647_; 
v_fst_6647_ = lean_ctor_get(v_a_6643_, 0);
lean_inc(v_fst_6647_);
lean_dec(v_a_6643_);
if (lean_obj_tag(v_fst_6647_) == 0)
{
lean_object* v___x_6648_; uint8_t v_didChange_6649_; 
v___x_6648_ = lean_st_ref_get(v_a_6616_);
v_didChange_6649_ = lean_ctor_get_uint8(v___x_6648_, sizeof(void*)*4);
lean_dec(v___x_6648_);
if (v_didChange_6649_ == 0)
{
lean_object* v_toCold_6650_; lean_object* v_options_6651_; uint8_t v_hasTrace_6652_; 
v_toCold_6650_ = lean_ctor_get(v_a_6624_, 0);
v_options_6651_ = lean_ctor_get(v_toCold_6650_, 2);
v_hasTrace_6652_ = lean_ctor_get_uint8(v_options_6651_, sizeof(void*)*1);
if (v_hasTrace_6652_ == 0)
{
lean_object* v___x_6653_; lean_object* v___x_6655_; 
v___x_6653_ = lean_box(v_didChange_6649_);
if (v_isShared_6646_ == 0)
{
lean_ctor_set(v___x_6645_, 0, v___x_6653_);
v___x_6655_ = v___x_6645_;
goto v_reusejp_6654_;
}
else
{
lean_object* v_reuseFailAlloc_6656_; 
v_reuseFailAlloc_6656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6656_, 0, v___x_6653_);
v___x_6655_ = v_reuseFailAlloc_6656_;
goto v_reusejp_6654_;
}
v_reusejp_6654_:
{
return v___x_6655_;
}
}
else
{
lean_object* v_inheritedTraceOptions_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; uint8_t v___x_6660_; 
v_inheritedTraceOptions_6657_ = lean_ctor_get(v_toCold_6650_, 11);
v___x_6658_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6659_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6657_, v_options_6651_, v___x_6659_);
if (v___x_6660_ == 0)
{
lean_object* v___x_6661_; lean_object* v___x_6663_; 
v___x_6661_ = lean_box(v_didChange_6649_);
if (v_isShared_6646_ == 0)
{
lean_ctor_set(v___x_6645_, 0, v___x_6661_);
v___x_6663_ = v___x_6645_;
goto v_reusejp_6662_;
}
else
{
lean_object* v_reuseFailAlloc_6664_; 
v_reuseFailAlloc_6664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6664_, 0, v___x_6661_);
v___x_6663_ = v_reuseFailAlloc_6664_;
goto v_reusejp_6662_;
}
v_reusejp_6662_:
{
return v___x_6663_;
}
}
else
{
lean_object* v___x_6665_; lean_object* v___x_6666_; 
lean_del_object(v___x_6645_);
v___x_6665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6666_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6658_, v___x_6665_, v_a_6622_, v_a_6623_, v_a_6624_, v_a_6625_);
if (lean_obj_tag(v___x_6666_) == 0)
{
lean_object* v___x_6668_; uint8_t v_isShared_6669_; uint8_t v_isSharedCheck_6674_; 
v_isSharedCheck_6674_ = !lean_is_exclusive(v___x_6666_);
if (v_isSharedCheck_6674_ == 0)
{
lean_object* v_unused_6675_; 
v_unused_6675_ = lean_ctor_get(v___x_6666_, 0);
lean_dec(v_unused_6675_);
v___x_6668_ = v___x_6666_;
v_isShared_6669_ = v_isSharedCheck_6674_;
goto v_resetjp_6667_;
}
else
{
lean_dec(v___x_6666_);
v___x_6668_ = lean_box(0);
v_isShared_6669_ = v_isSharedCheck_6674_;
goto v_resetjp_6667_;
}
v_resetjp_6667_:
{
lean_object* v___x_6670_; lean_object* v___x_6672_; 
v___x_6670_ = lean_box(v_didChange_6649_);
if (v_isShared_6669_ == 0)
{
lean_ctor_set(v___x_6668_, 0, v___x_6670_);
v___x_6672_ = v___x_6668_;
goto v_reusejp_6671_;
}
else
{
lean_object* v_reuseFailAlloc_6673_; 
v_reuseFailAlloc_6673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6673_, 0, v___x_6670_);
v___x_6672_ = v_reuseFailAlloc_6673_;
goto v_reusejp_6671_;
}
v_reusejp_6671_:
{
return v___x_6672_;
}
}
}
else
{
lean_object* v_a_6676_; lean_object* v___x_6678_; uint8_t v_isShared_6679_; uint8_t v_isSharedCheck_6683_; 
v_a_6676_ = lean_ctor_get(v___x_6666_, 0);
v_isSharedCheck_6683_ = !lean_is_exclusive(v___x_6666_);
if (v_isSharedCheck_6683_ == 0)
{
v___x_6678_ = v___x_6666_;
v_isShared_6679_ = v_isSharedCheck_6683_;
goto v_resetjp_6677_;
}
else
{
lean_inc(v_a_6676_);
lean_dec(v___x_6666_);
v___x_6678_ = lean_box(0);
v_isShared_6679_ = v_isSharedCheck_6683_;
goto v_resetjp_6677_;
}
v_resetjp_6677_:
{
lean_object* v___x_6681_; 
if (v_isShared_6679_ == 0)
{
v___x_6681_ = v___x_6678_;
goto v_reusejp_6680_;
}
else
{
lean_object* v_reuseFailAlloc_6682_; 
v_reuseFailAlloc_6682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6682_, 0, v_a_6676_);
v___x_6681_ = v_reuseFailAlloc_6682_;
goto v_reusejp_6680_;
}
v_reusejp_6680_:
{
return v___x_6681_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_6684_; lean_object* v_options_6685_; uint8_t v_hasTrace_6686_; 
lean_del_object(v___x_6645_);
v_toCold_6684_ = lean_ctor_get(v_a_6624_, 0);
v_options_6685_ = lean_ctor_get(v_toCold_6684_, 2);
v_hasTrace_6686_ = lean_ctor_get_uint8(v_options_6685_, sizeof(void*)*1);
if (v_hasTrace_6686_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; uint8_t v___x_6691_; 
v_inheritedTraceOptions_6688_ = lean_ctor_get(v_toCold_6684_, 11);
v___x_6689_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6690_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6691_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6688_, v_options_6685_, v___x_6690_);
if (v___x_6691_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6693_; lean_object* v___x_6694_; 
v___x_6693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6694_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6689_, v___x_6693_, v_a_6622_, v_a_6623_, v_a_6624_, v_a_6625_);
if (lean_obj_tag(v___x_6694_) == 0)
{
lean_dec_ref_known(v___x_6694_, 1);
goto _start;
}
else
{
lean_object* v_a_6696_; lean_object* v___x_6698_; uint8_t v_isShared_6699_; uint8_t v_isSharedCheck_6703_; 
v_a_6696_ = lean_ctor_get(v___x_6694_, 0);
v_isSharedCheck_6703_ = !lean_is_exclusive(v___x_6694_);
if (v_isSharedCheck_6703_ == 0)
{
v___x_6698_ = v___x_6694_;
v_isShared_6699_ = v_isSharedCheck_6703_;
goto v_resetjp_6697_;
}
else
{
lean_inc(v_a_6696_);
lean_dec(v___x_6694_);
v___x_6698_ = lean_box(0);
v_isShared_6699_ = v_isSharedCheck_6703_;
goto v_resetjp_6697_;
}
v_resetjp_6697_:
{
lean_object* v___x_6701_; 
if (v_isShared_6699_ == 0)
{
v___x_6701_ = v___x_6698_;
goto v_reusejp_6700_;
}
else
{
lean_object* v_reuseFailAlloc_6702_; 
v_reuseFailAlloc_6702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_a_6696_);
v___x_6701_ = v_reuseFailAlloc_6702_;
goto v_reusejp_6700_;
}
v_reusejp_6700_:
{
return v___x_6701_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_6704_; lean_object* v___x_6706_; 
v_val_6704_ = lean_ctor_get(v_fst_6647_, 0);
lean_inc(v_val_6704_);
lean_dec_ref_known(v_fst_6647_, 1);
if (v_isShared_6646_ == 0)
{
lean_ctor_set(v___x_6645_, 0, v_val_6704_);
v___x_6706_ = v___x_6645_;
goto v_reusejp_6705_;
}
else
{
lean_object* v_reuseFailAlloc_6707_; 
v_reuseFailAlloc_6707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6707_, 0, v_val_6704_);
v___x_6706_ = v_reuseFailAlloc_6707_;
goto v_reusejp_6705_;
}
v_reusejp_6705_:
{
return v___x_6706_;
}
}
}
}
else
{
lean_object* v_a_6709_; lean_object* v___x_6711_; uint8_t v_isShared_6712_; uint8_t v_isSharedCheck_6716_; 
v_a_6709_ = lean_ctor_get(v___x_6642_, 0);
v_isSharedCheck_6716_ = !lean_is_exclusive(v___x_6642_);
if (v_isSharedCheck_6716_ == 0)
{
v___x_6711_ = v___x_6642_;
v_isShared_6712_ = v_isSharedCheck_6716_;
goto v_resetjp_6710_;
}
else
{
lean_inc(v_a_6709_);
lean_dec(v___x_6642_);
v___x_6711_ = lean_box(0);
v_isShared_6712_ = v_isSharedCheck_6716_;
goto v_resetjp_6710_;
}
v_resetjp_6710_:
{
lean_object* v___x_6714_; 
if (v_isShared_6712_ == 0)
{
v___x_6714_ = v___x_6711_;
goto v_reusejp_6713_;
}
else
{
lean_object* v_reuseFailAlloc_6715_; 
v_reuseFailAlloc_6715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6715_, 0, v_a_6709_);
v___x_6714_ = v_reuseFailAlloc_6715_;
goto v_reusejp_6713_;
}
v_reusejp_6713_:
{
return v___x_6714_;
}
}
}
}
}
}
else
{
lean_object* v_a_6719_; lean_object* v___x_6721_; uint8_t v_isShared_6722_; uint8_t v_isSharedCheck_6726_; 
v_a_6719_ = lean_ctor_get(v___x_6628_, 0);
v_isSharedCheck_6726_ = !lean_is_exclusive(v___x_6628_);
if (v_isSharedCheck_6726_ == 0)
{
v___x_6721_ = v___x_6628_;
v_isShared_6722_ = v_isSharedCheck_6726_;
goto v_resetjp_6720_;
}
else
{
lean_inc(v_a_6719_);
lean_dec(v___x_6628_);
v___x_6721_ = lean_box(0);
v_isShared_6722_ = v_isSharedCheck_6726_;
goto v_resetjp_6720_;
}
v_resetjp_6720_:
{
lean_object* v___x_6724_; 
if (v_isShared_6722_ == 0)
{
v___x_6724_ = v___x_6721_;
goto v_reusejp_6723_;
}
else
{
lean_object* v_reuseFailAlloc_6725_; 
v_reuseFailAlloc_6725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6725_, 0, v_a_6719_);
v___x_6724_ = v_reuseFailAlloc_6725_;
goto v_reusejp_6723_;
}
v_reusejp_6723_:
{
return v___x_6724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6727_, lean_object* v_a_6728_, lean_object* v_a_6729_, lean_object* v_a_6730_, lean_object* v_a_6731_, lean_object* v_a_6732_, lean_object* v_a_6733_, lean_object* v_a_6734_, lean_object* v_a_6735_, lean_object* v_a_6736_, lean_object* v_a_6737_, lean_object* v_a_6738_, lean_object* v_a_6739_){
_start:
{
lean_object* v_res_6740_; 
v_res_6740_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6727_, v_a_6728_, v_a_6729_, v_a_6730_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_, v_a_6735_, v_a_6736_, v_a_6737_, v_a_6738_);
lean_dec(v_a_6738_);
lean_dec_ref(v_a_6737_);
lean_dec(v_a_6736_);
lean_dec_ref(v_a_6735_);
lean_dec(v_a_6734_);
lean_dec_ref(v_a_6733_);
lean_dec(v_a_6732_);
lean_dec_ref(v_a_6731_);
lean_dec(v_a_6730_);
lean_dec(v_a_6729_);
lean_dec_ref(v_a_6728_);
lean_dec(v_passes_6727_);
return v_res_6740_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6741_, lean_object* v_msg_6742_, lean_object* v___y_6743_, lean_object* v___y_6744_, lean_object* v___y_6745_, lean_object* v___y_6746_, lean_object* v___y_6747_, lean_object* v___y_6748_, lean_object* v___y_6749_, lean_object* v___y_6750_, lean_object* v___y_6751_, lean_object* v___y_6752_, lean_object* v___y_6753_){
_start:
{
lean_object* v___x_6755_; 
v___x_6755_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6741_, v_msg_6742_, v___y_6750_, v___y_6751_, v___y_6752_, v___y_6753_);
return v___x_6755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6756_, lean_object* v_msg_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_, lean_object* v___y_6761_, lean_object* v___y_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_, lean_object* v___y_6765_, lean_object* v___y_6766_, lean_object* v___y_6767_, lean_object* v___y_6768_, lean_object* v___y_6769_){
_start:
{
lean_object* v_res_6770_; 
v_res_6770_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6756_, v_msg_6757_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_);
lean_dec(v___y_6768_);
lean_dec_ref(v___y_6767_);
lean_dec(v___y_6766_);
lean_dec_ref(v___y_6765_);
lean_dec(v___y_6764_);
lean_dec_ref(v___y_6763_);
lean_dec(v___y_6762_);
lean_dec_ref(v___y_6761_);
lean_dec(v___y_6760_);
lean_dec(v___y_6759_);
lean_dec_ref(v___y_6758_);
return v_res_6770_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6771_, lean_object* v_x_6772_, lean_object* v___y_6773_, lean_object* v___y_6774_, lean_object* v___y_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_){
_start:
{
lean_object* v___x_6785_; 
v___x_6785_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6772_);
return v___x_6785_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6786_, lean_object* v_x_6787_, lean_object* v___y_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_, lean_object* v___y_6799_){
_start:
{
lean_object* v_res_6800_; 
v_res_6800_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6786_, v_x_6787_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_);
lean_dec(v___y_6798_);
lean_dec_ref(v___y_6797_);
lean_dec(v___y_6796_);
lean_dec_ref(v___y_6795_);
lean_dec(v___y_6794_);
lean_dec_ref(v___y_6793_);
lean_dec(v___y_6792_);
lean_dec_ref(v___y_6791_);
lean_dec(v___y_6790_);
lean_dec(v___y_6789_);
lean_dec_ref(v___y_6788_);
return v_res_6800_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6801_, lean_object* v_as_x27_6802_, lean_object* v_b_6803_, lean_object* v_a_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_, lean_object* v___y_6809_, lean_object* v___y_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_){
_start:
{
lean_object* v___x_6817_; 
v___x_6817_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6802_, v_b_6803_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_, v___y_6813_, v___y_6814_, v___y_6815_);
return v___x_6817_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6818_, lean_object* v_as_x27_6819_, lean_object* v_b_6820_, lean_object* v_a_6821_, lean_object* v___y_6822_, lean_object* v___y_6823_, lean_object* v___y_6824_, lean_object* v___y_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_){
_start:
{
lean_object* v_res_6834_; 
v_res_6834_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6818_, v_as_x27_6819_, v_b_6820_, v_a_6821_, v___y_6822_, v___y_6823_, v___y_6824_, v___y_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_);
lean_dec(v___y_6832_);
lean_dec_ref(v___y_6831_);
lean_dec(v___y_6830_);
lean_dec_ref(v___y_6829_);
lean_dec(v___y_6828_);
lean_dec_ref(v___y_6827_);
lean_dec(v___y_6826_);
lean_dec_ref(v___y_6825_);
lean_dec(v___y_6824_);
lean_dec(v___y_6823_);
lean_dec_ref(v___y_6822_);
lean_dec(v_as_x27_6819_);
lean_dec(v_as_6818_);
return v_res_6834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6835_, lean_object* v_data_6836_, lean_object* v_ref_6837_, lean_object* v_msg_6838_, lean_object* v___y_6839_, lean_object* v___y_6840_, lean_object* v___y_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_, lean_object* v___y_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_){
_start:
{
lean_object* v___x_6851_; 
v___x_6851_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6835_, v_data_6836_, v_ref_6837_, v_msg_6838_, v___y_6846_, v___y_6847_, v___y_6848_, v___y_6849_);
return v___x_6851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6852_, lean_object* v_data_6853_, lean_object* v_ref_6854_, lean_object* v_msg_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_){
_start:
{
lean_object* v_res_6868_; 
v_res_6868_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6852_, v_data_6853_, v_ref_6854_, v_msg_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_);
lean_dec(v___y_6866_);
lean_dec_ref(v___y_6865_);
lean_dec(v___y_6864_);
lean_dec_ref(v___y_6863_);
lean_dec(v___y_6862_);
lean_dec_ref(v___y_6861_);
lean_dec(v___y_6860_);
lean_dec_ref(v___y_6859_);
lean_dec(v___y_6858_);
lean_dec(v___y_6857_);
lean_dec_ref(v___y_6856_);
return v_res_6868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_, lean_object* v_a_6878_, lean_object* v_a_6879_, lean_object* v_a_6880_){
_start:
{
lean_object* v___x_6882_; 
v___x_6882_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6869_, v_a_6870_, v_a_6871_, v_a_6872_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_, v_a_6877_, v_a_6878_, v_a_6879_, v_a_6880_);
if (lean_obj_tag(v___x_6882_) == 0)
{
lean_object* v_a_6883_; lean_object* v___x_6884_; lean_object* v___x_6886_; uint8_t v_isShared_6887_; uint8_t v_isSharedCheck_6891_; 
v_a_6883_ = lean_ctor_get(v___x_6882_, 0);
lean_inc(v_a_6883_);
lean_dec_ref_known(v___x_6882_, 1);
v___x_6884_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_6870_, v_a_6871_);
v_isSharedCheck_6891_ = !lean_is_exclusive(v___x_6884_);
if (v_isSharedCheck_6891_ == 0)
{
lean_object* v_unused_6892_; 
v_unused_6892_ = lean_ctor_get(v___x_6884_, 0);
lean_dec(v_unused_6892_);
v___x_6886_ = v___x_6884_;
v_isShared_6887_ = v_isSharedCheck_6891_;
goto v_resetjp_6885_;
}
else
{
lean_dec(v___x_6884_);
v___x_6886_ = lean_box(0);
v_isShared_6887_ = v_isSharedCheck_6891_;
goto v_resetjp_6885_;
}
v_resetjp_6885_:
{
lean_object* v___x_6889_; 
if (v_isShared_6887_ == 0)
{
lean_ctor_set(v___x_6886_, 0, v_a_6883_);
v___x_6889_ = v___x_6886_;
goto v_reusejp_6888_;
}
else
{
lean_object* v_reuseFailAlloc_6890_; 
v_reuseFailAlloc_6890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6890_, 0, v_a_6883_);
v___x_6889_ = v_reuseFailAlloc_6890_;
goto v_reusejp_6888_;
}
v_reusejp_6888_:
{
return v___x_6889_;
}
}
}
else
{
return v___x_6882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6893_, lean_object* v_a_6894_, lean_object* v_a_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_, lean_object* v_a_6903_, lean_object* v_a_6904_, lean_object* v_a_6905_){
_start:
{
lean_object* v_res_6906_; 
v_res_6906_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6893_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_);
lean_dec(v_a_6904_);
lean_dec_ref(v_a_6903_);
lean_dec(v_a_6902_);
lean_dec_ref(v_a_6901_);
lean_dec(v_a_6900_);
lean_dec_ref(v_a_6899_);
lean_dec(v_a_6898_);
lean_dec_ref(v_a_6897_);
lean_dec(v_a_6896_);
lean_dec(v_a_6895_);
lean_dec_ref(v_a_6894_);
lean_dec(v_passes_6893_);
return v_res_6906_;
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
