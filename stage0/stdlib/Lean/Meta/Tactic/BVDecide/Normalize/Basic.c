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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_instMonadControlReaderT(lean_object*, lean_object*);
lean_object* l_instMonadControlStateRefT_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_GoalM_runCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
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
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0;
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
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object*, lean_object*);
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
static uint64_t _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0(void){
_start:
{
uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; 
v___x_213_ = 1723ULL;
v___x_214_ = 1ULL;
v___x_215_ = lean_uint64_mix_hash(v___x_214_, v___x_213_);
return v___x_215_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object* v_x_216_){
_start:
{
switch(lean_obj_tag(v_x_216_))
{
case 0:
{
lean_object* v_fvar_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; 
v_fvar_217_ = lean_ctor_get(v_x_216_, 0);
v___x_218_ = 0ULL;
v___x_219_ = l_Lean_instHashableFVarId_hash(v_fvar_217_);
v___x_220_ = lean_uint64_mix_hash(v___x_218_, v___x_219_);
return v___x_220_;
}
case 1:
{
lean_object* v_n_221_; uint64_t v___x_222_; 
v_n_221_ = lean_ctor_get(v_x_216_, 0);
v___x_222_ = 1ULL;
if (lean_obj_tag(v_n_221_) == 0)
{
uint64_t v___x_223_; 
v___x_223_ = lean_uint64_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0);
return v___x_223_;
}
else
{
uint64_t v_hash_224_; uint64_t v___x_225_; 
v_hash_224_ = lean_ctor_get_uint64(v_n_221_, sizeof(void*)*2);
v___x_225_ = lean_uint64_mix_hash(v___x_222_, v_hash_224_);
return v___x_225_;
}
}
case 2:
{
lean_object* v_e_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; 
v_e_226_ = lean_ctor_get(v_x_216_, 0);
v___x_227_ = 2ULL;
v___x_228_ = l_Lean_Expr_hash(v_e_226_);
v___x_229_ = lean_uint64_mix_hash(v___x_227_, v___x_228_);
return v___x_229_;
}
case 3:
{
lean_object* v_s_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; 
v_s_230_ = lean_ctor_get(v_x_216_, 0);
v___x_231_ = 3ULL;
v___x_232_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_s_230_);
v___x_233_ = lean_uint64_mix_hash(v___x_231_, v___x_232_);
return v___x_233_;
}
default: 
{
uint64_t v___x_234_; 
v___x_234_ = 4ULL;
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object* v_x_235_){
_start:
{
uint64_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_235_);
lean_dec(v_x_235_);
v_r_237_ = lean_box_uint64(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
switch(lean_obj_tag(v_x_240_))
{
case 0:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v_fvar_242_; lean_object* v_fvar_243_; uint8_t v___x_244_; 
v_fvar_242_ = lean_ctor_get(v_x_240_, 0);
v_fvar_243_ = lean_ctor_get(v_x_241_, 0);
v___x_244_ = l_Lean_instBEqFVarId_beq(v_fvar_242_, v_fvar_243_);
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
}
case 1:
{
if (lean_obj_tag(v_x_241_) == 1)
{
lean_object* v_n_246_; lean_object* v_n_247_; uint8_t v___x_248_; 
v_n_246_ = lean_ctor_get(v_x_240_, 0);
v_n_247_ = lean_ctor_get(v_x_241_, 0);
v___x_248_ = lean_name_eq(v_n_246_, v_n_247_);
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
}
case 2:
{
if (lean_obj_tag(v_x_241_) == 2)
{
lean_object* v_e_250_; lean_object* v_e_251_; uint8_t v___x_252_; 
v_e_250_ = lean_ctor_get(v_x_240_, 0);
v_e_251_ = lean_ctor_get(v_x_241_, 0);
v___x_252_ = lean_expr_eqv(v_e_250_, v_e_251_);
return v___x_252_;
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
}
case 3:
{
if (lean_obj_tag(v_x_241_) == 3)
{
lean_object* v_s_254_; lean_object* v_s_255_; 
v_s_254_ = lean_ctor_get(v_x_240_, 0);
v_s_255_ = lean_ctor_get(v_x_241_, 0);
v_x_240_ = v_s_254_;
v_x_241_ = v_s_255_;
goto _start;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
default: 
{
if (lean_obj_tag(v_x_241_) == 4)
{
uint8_t v___x_258_; 
v___x_258_ = 1;
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = 0;
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec(v_x_260_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object* v_s_266_){
_start:
{
if (lean_obj_tag(v_s_266_) == 3)
{
lean_object* v_s_267_; 
v_s_267_ = lean_ctor_get(v_s_266_, 0);
v_s_266_ = v_s_267_;
goto _start;
}
else
{
lean_inc(v_s_266_);
return v_s_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object* v_s_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_269_);
lean_dec(v_s_269_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2));
v___x_276_ = l_Lean_stringToMessageData(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6));
v___x_282_ = l_Lean_stringToMessageData(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8));
v___x_285_ = l_Lean_stringToMessageData(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object* v_s_286_){
_start:
{
switch(lean_obj_tag(v_s_286_))
{
case 0:
{
lean_object* v_fvar_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_fvar_287_ = lean_ctor_get(v_s_286_, 0);
lean_inc(v_fvar_287_);
lean_dec_ref_known(v_s_286_, 1);
v___x_288_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1);
v___x_289_ = l_Lean_mkFVar(v_fvar_287_);
v___x_290_ = l_Lean_MessageData_ofExpr(v___x_289_);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_288_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
case 1:
{
lean_object* v_n_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_n_292_ = lean_ctor_get(v_s_286_, 0);
lean_inc(v_n_292_);
lean_dec_ref_known(v_s_286_, 1);
v___x_293_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3);
v___x_294_ = l_Lean_MessageData_ofName(v_n_292_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
case 2:
{
lean_object* v_e_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_e_296_ = lean_ctor_get(v_s_286_, 0);
lean_inc_ref(v_e_296_);
lean_dec_ref_known(v_s_286_, 1);
v___x_297_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5);
v___x_298_ = l_Lean_MessageData_ofExpr(v_e_296_);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
case 3:
{
lean_object* v_s_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_s_300_ = lean_ctor_get(v_s_286_, 0);
lean_inc(v_s_300_);
lean_dec_ref_known(v_s_286_, 1);
v___x_301_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7);
v___x_302_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_300_);
lean_dec(v_s_300_);
v___x_303_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v___x_302_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_301_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
return v___x_304_;
}
default: 
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9);
return v___x_305_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1));
v___x_313_ = l_Lean_Expr_const___override(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default));
v___x_315_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2);
v___x_316_ = lean_box(0);
v___x_317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
lean_ctor_set(v___x_317_, 2, v___x_315_);
lean_ctor_set(v___x_317_, 3, v___x_314_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
return v___x_319_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object* v_lhs_320_, lean_object* v_rhs_321_){
_start:
{
lean_object* v_type_322_; lean_object* v_type_323_; uint8_t v___x_324_; 
v_type_322_ = lean_ctor_get(v_lhs_320_, 1);
v_type_323_ = lean_ctor_get(v_rhs_321_, 1);
v___x_324_ = lean_expr_eqv(v_type_322_, v_type_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object* v_lhs_325_, lean_object* v_rhs_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_325_, v_rhs_326_);
lean_dec_ref(v_rhs_326_);
lean_dec_ref(v_lhs_325_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object* v_hyp_331_){
_start:
{
lean_object* v_type_332_; uint64_t v___x_333_; 
v_type_332_ = lean_ctor_get(v_hyp_331_, 1);
v___x_333_ = l_Lean_Expr_hash(v_type_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object* v_hyp_334_){
_start:
{
uint64_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_334_);
lean_dec_ref(v_hyp_334_);
v_r_336_ = lean_box_uint64(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object* v_hyp_339_){
_start:
{
lean_object* v_type_340_; lean_object* v___x_341_; 
v_type_340_ = lean_ctor_get(v_hyp_339_, 1);
lean_inc_ref(v_type_340_);
lean_dec_ref(v_hyp_339_);
v___x_341_ = l_Lean_MessageData_ofExpr(v_type_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx(lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_unsigned_to_nat(0u);
return v___x_345_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(1u);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___boxed(lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx(v_x_347_);
lean_dec(v_x_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(lean_object* v_t_349_, lean_object* v_k_350_){
_start:
{
if (lean_obj_tag(v_t_349_) == 0)
{
lean_object* v_restrictedTypes_351_; lean_object* v___x_352_; 
v_restrictedTypes_351_ = lean_ctor_get(v_t_349_, 0);
lean_inc(v_restrictedTypes_351_);
lean_dec_ref_known(v_t_349_, 1);
v___x_352_ = lean_apply_1(v_k_350_, v_restrictedTypes_351_);
return v___x_352_;
}
else
{
return v_k_350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(lean_object* v_motive_353_, lean_object* v_ctorIdx_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_k_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_355_, v_k_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___boxed(lean_object* v_motive_359_, lean_object* v_ctorIdx_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_k_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(v_motive_359_, v_ctorIdx_360_, v_t_361_, v_h_362_, v_k_363_);
lean_dec(v_ctorIdx_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim___redArg(lean_object* v_t_365_, lean_object* v_solve_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_365_, v_solve_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim(lean_object* v_motive_368_, lean_object* v_t_369_, lean_object* v_h_370_, lean_object* v_solve_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_369_, v_solve_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim___redArg(lean_object* v_t_373_, lean_object* v_push_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_373_, v_push_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim(lean_object* v_motive_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_push_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_377_, v_push_379_);
return v___x_380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
uint8_t v___x_382_; 
v___x_382_ = 0;
return v___x_382_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = 1;
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush___boxed(lean_object* v_x_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_x_384_);
lean_dec(v_x_384_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
lean_object* v_restrictedTypes_388_; 
v_restrictedTypes_388_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_restrictedTypes_388_);
return v_restrictedTypes_388_;
}
else
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes___boxed(lean_object* v_x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_x_390_);
lean_dec(v_x_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(lean_object* v_mode_392_, lean_object* v_config_393_){
_start:
{
if (lean_obj_tag(v_mode_392_) == 0)
{
return v_config_393_;
}
else
{
lean_object* v_timeout_394_; uint8_t v_trimProofs_395_; uint8_t v_binaryProofs_396_; uint8_t v_acNf_397_; uint8_t v_graphviz_398_; lean_object* v_maxSteps_399_; uint8_t v_shortCircuit_400_; uint8_t v_solverMode_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_timeout_394_ = lean_ctor_get(v_config_393_, 0);
v_trimProofs_395_ = lean_ctor_get_uint8(v_config_393_, sizeof(void*)*2);
v_binaryProofs_396_ = lean_ctor_get_uint8(v_config_393_, sizeof(void*)*2 + 1);
v_acNf_397_ = lean_ctor_get_uint8(v_config_393_, sizeof(void*)*2 + 2);
v_graphviz_398_ = lean_ctor_get_uint8(v_config_393_, sizeof(void*)*2 + 8);
v_maxSteps_399_ = lean_ctor_get(v_config_393_, 1);
v_shortCircuit_400_ = lean_ctor_get_uint8(v_config_393_, sizeof(void*)*2 + 9);
v_solverMode_401_ = lean_ctor_get_uint8(v_config_393_, sizeof(void*)*2 + 10);
v_isSharedCheck_409_ = !lean_is_exclusive(v_config_393_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v_config_393_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_maxSteps_399_);
lean_inc(v_timeout_394_);
lean_dec(v_config_393_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
uint8_t v___x_405_; lean_object* v___x_407_; 
v___x_405_ = 0;
if (v_isShared_404_ == 0)
{
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_timeout_394_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_maxSteps_399_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*2, v_trimProofs_395_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*2 + 1, v_binaryProofs_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*2 + 2, v_acNf_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*2 + 8, v_graphviz_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*2 + 9, v_shortCircuit_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*2 + 10, v_solverMode_401_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*2 + 3, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*2 + 4, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*2 + 5, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*2 + 6, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*2 + 7, v___x_405_);
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig___boxed(lean_object* v_mode_410_, lean_object* v_config_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_410_, v_config_411_);
lean_dec(v_mode_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object* v_mode_413_, lean_object* v_config_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_413_, v_config_414_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_mode_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx(uint8_t v_x_417_){
_start:
{
if (v_x_417_ == 0)
{
lean_object* v___x_418_; 
v___x_418_ = lean_unsigned_to_nat(0u);
return v___x_418_;
}
else
{
lean_object* v___x_419_; 
v___x_419_ = lean_unsigned_to_nat(1u);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___boxed(lean_object* v_x_420_){
_start:
{
uint8_t v_x_boxed_421_; lean_object* v_res_422_; 
v_x_boxed_421_ = lean_unbox(v_x_420_);
v_res_422_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx(v_x_boxed_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(lean_object* v_k_423_){
_start:
{
lean_inc(v_k_423_);
return v_k_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(v_k_424_);
lean_dec(v_k_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(lean_object* v_motive_426_, lean_object* v_ctorIdx_427_, uint8_t v_t_428_, lean_object* v_h_429_, lean_object* v_k_430_){
_start:
{
lean_inc(v_k_430_);
return v_k_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___boxed(lean_object* v_motive_431_, lean_object* v_ctorIdx_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_k_435_){
_start:
{
uint8_t v_t_boxed_436_; lean_object* v_res_437_; 
v_t_boxed_436_ = lean_unbox(v_t_433_);
v_res_437_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(v_motive_431_, v_ctorIdx_432_, v_t_boxed_436_, v_h_434_, v_k_435_);
lean_dec(v_k_435_);
lean_dec(v_ctorIdx_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_438_){
_start:
{
lean_inc(v_rewrite_438_);
return v_rewrite_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(v_rewrite_439_);
lean_dec(v_rewrite_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(lean_object* v_motive_441_, uint8_t v_t_442_, lean_object* v_h_443_, lean_object* v_rewrite_444_){
_start:
{
lean_inc(v_rewrite_444_);
return v_rewrite_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___boxed(lean_object* v_motive_445_, lean_object* v_t_446_, lean_object* v_h_447_, lean_object* v_rewrite_448_){
_start:
{
uint8_t v_t_boxed_449_; lean_object* v_res_450_; 
v_t_boxed_449_ = lean_unbox(v_t_446_);
v_res_450_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(v_motive_445_, v_t_boxed_449_, v_h_447_, v_rewrite_448_);
lean_dec(v_rewrite_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(lean_object* v_ac_451_){
_start:
{
lean_inc(v_ac_451_);
return v_ac_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg___boxed(lean_object* v_ac_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(v_ac_452_);
lean_dec(v_ac_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(lean_object* v_motive_454_, uint8_t v_t_455_, lean_object* v_h_456_, lean_object* v_ac_457_){
_start:
{
lean_inc(v_ac_457_);
return v_ac_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___boxed(lean_object* v_motive_458_, lean_object* v_t_459_, lean_object* v_h_460_, lean_object* v_ac_461_){
_start:
{
uint8_t v_t_boxed_462_; lean_object* v_res_463_; 
v_t_boxed_462_ = lean_unbox(v_t_459_);
v_res_463_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(v_motive_458_, v_t_boxed_462_, v_h_460_, v_ac_461_);
lean_dec(v_ac_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx(uint8_t v_x_464_){
_start:
{
if (v_x_464_ == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_unsigned_to_nat(0u);
return v___x_465_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = lean_unsigned_to_nat(1u);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___boxed(lean_object* v_x_467_){
_start:
{
uint8_t v_x_boxed_468_; lean_object* v_res_469_; 
v_x_boxed_468_ = lean_unbox(v_x_467_);
v_res_469_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx(v_x_boxed_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(lean_object* v_k_470_){
_start:
{
lean_inc(v_k_470_);
return v_k_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(v_k_471_);
lean_dec(v_k_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(lean_object* v_motive_473_, lean_object* v_ctorIdx_474_, uint8_t v_t_475_, lean_object* v_h_476_, lean_object* v_k_477_){
_start:
{
lean_inc(v_k_477_);
return v_k_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___boxed(lean_object* v_motive_478_, lean_object* v_ctorIdx_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_k_482_){
_start:
{
uint8_t v_t_boxed_483_; lean_object* v_res_484_; 
v_t_boxed_483_ = lean_unbox(v_t_480_);
v_res_484_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(v_motive_478_, v_ctorIdx_479_, v_t_boxed_483_, v_h_481_, v_k_482_);
lean_dec(v_k_482_);
lean_dec(v_ctorIdx_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_485_){
_start:
{
lean_inc(v_rewrite_485_);
return v_rewrite_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(v_rewrite_486_);
lean_dec(v_rewrite_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(lean_object* v_motive_488_, uint8_t v_t_489_, lean_object* v_h_490_, lean_object* v_rewrite_491_){
_start:
{
lean_inc(v_rewrite_491_);
return v_rewrite_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___boxed(lean_object* v_motive_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_rewrite_495_){
_start:
{
uint8_t v_t_boxed_496_; lean_object* v_res_497_; 
v_t_boxed_496_ = lean_unbox(v_t_493_);
v_res_497_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(v_motive_492_, v_t_boxed_496_, v_h_494_, v_rewrite_495_);
lean_dec(v_rewrite_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(lean_object* v_reduction_498_){
_start:
{
lean_inc(v_reduction_498_);
return v_reduction_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg___boxed(lean_object* v_reduction_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(v_reduction_499_);
lean_dec(v_reduction_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(lean_object* v_motive_501_, uint8_t v_t_502_, lean_object* v_h_503_, lean_object* v_reduction_504_){
_start:
{
lean_inc(v_reduction_504_);
return v_reduction_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___boxed(lean_object* v_motive_505_, lean_object* v_t_506_, lean_object* v_h_507_, lean_object* v_reduction_508_){
_start:
{
uint8_t v_t_boxed_509_; lean_object* v_res_510_; 
v_t_boxed_509_ = lean_unbox(v_t_506_);
v_res_510_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(v_motive_505_, v_t_boxed_509_, v_h_507_, v_reduction_508_);
lean_dec(v_reduction_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(uint8_t v_x_511_, lean_object* v_x_512_){
_start:
{
if (v_x_511_ == 0)
{
lean_object* v_rewriteSimp_513_; 
v_rewriteSimp_513_ = lean_ctor_get(v_x_512_, 1);
lean_inc_ref(v_rewriteSimp_513_);
return v_rewriteSimp_513_;
}
else
{
lean_object* v_ac_514_; 
v_ac_514_ = lean_ctor_get(v_x_512_, 3);
lean_inc_ref(v_ac_514_);
return v_ac_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get___boxed(lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
uint8_t v_x_15__boxed_517_; lean_object* v_res_518_; 
v_x_15__boxed_517_ = lean_unbox(v_x_515_);
v_res_518_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_x_15__boxed_517_, v_x_516_);
lean_dec_ref(v_x_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(uint8_t v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
if (v_x_519_ == 0)
{
lean_object* v_reduction_522_; lean_object* v_rewriteDSimp_523_; lean_object* v_ac_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_reduction_522_ = lean_ctor_get(v_x_521_, 0);
v_rewriteDSimp_523_ = lean_ctor_get(v_x_521_, 2);
v_ac_524_ = lean_ctor_get(v_x_521_, 3);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_x_521_, 1);
lean_dec(v_unused_532_);
v___x_526_ = v_x_521_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_ac_524_);
lean_inc(v_rewriteDSimp_523_);
lean_inc(v_reduction_522_);
lean_dec(v_x_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_x_520_);
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_reduction_522_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_x_520_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_rewriteDSimp_523_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v_ac_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_object* v_reduction_533_; lean_object* v_rewriteSimp_534_; lean_object* v_rewriteDSimp_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_reduction_533_ = lean_ctor_get(v_x_521_, 0);
v_rewriteSimp_534_ = lean_ctor_get(v_x_521_, 1);
v_rewriteDSimp_535_ = lean_ctor_get(v_x_521_, 2);
v_isSharedCheck_542_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_x_521_, 3);
lean_dec(v_unused_543_);
v___x_537_ = v_x_521_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_rewriteDSimp_535_);
lean_inc(v_rewriteSimp_534_);
lean_inc(v_reduction_533_);
lean_dec(v_x_521_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 3, v_x_520_);
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_reduction_533_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_rewriteSimp_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_rewriteDSimp_535_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_x_520_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set___boxed(lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
uint8_t v_x_28__boxed_547_; lean_object* v_res_548_; 
v_x_28__boxed_547_ = lean_unbox(v_x_544_);
v_res_548_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_x_28__boxed_547_, v_x_545_, v_x_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(uint8_t v_x_549_, lean_object* v_x_550_){
_start:
{
if (v_x_549_ == 0)
{
lean_object* v_rewriteDSimp_551_; 
v_rewriteDSimp_551_ = lean_ctor_get(v_x_550_, 2);
lean_inc_ref(v_rewriteDSimp_551_);
return v_rewriteDSimp_551_;
}
else
{
lean_object* v_reduction_552_; 
v_reduction_552_ = lean_ctor_get(v_x_550_, 0);
lean_inc_ref(v_reduction_552_);
return v_reduction_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get___boxed(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
uint8_t v_x_15__boxed_555_; lean_object* v_res_556_; 
v_x_15__boxed_555_ = lean_unbox(v_x_553_);
v_res_556_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_x_15__boxed_555_, v_x_554_);
lean_dec_ref(v_x_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(uint8_t v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
if (v_x_557_ == 0)
{
lean_object* v_reduction_560_; lean_object* v_rewriteSimp_561_; lean_object* v_ac_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_reduction_560_ = lean_ctor_get(v_x_559_, 0);
v_rewriteSimp_561_ = lean_ctor_get(v_x_559_, 1);
v_ac_562_ = lean_ctor_get(v_x_559_, 3);
v_isSharedCheck_569_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v_x_559_, 2);
lean_dec(v_unused_570_);
v___x_564_ = v_x_559_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_ac_562_);
lean_inc(v_rewriteSimp_561_);
lean_inc(v_reduction_560_);
lean_dec(v_x_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 2, v_x_558_);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_reduction_560_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_rewriteSimp_561_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_x_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_ac_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_object* v_rewriteSimp_571_; lean_object* v_rewriteDSimp_572_; lean_object* v_ac_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_rewriteSimp_571_ = lean_ctor_get(v_x_559_, 1);
v_rewriteDSimp_572_ = lean_ctor_get(v_x_559_, 2);
v_ac_573_ = lean_ctor_get(v_x_559_, 3);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_x_559_, 0);
lean_dec(v_unused_581_);
v___x_575_ = v_x_559_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_ac_573_);
lean_inc(v_rewriteDSimp_572_);
lean_inc(v_rewriteSimp_571_);
lean_dec(v_x_559_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_x_558_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_x_558_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_rewriteSimp_571_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_rewriteDSimp_572_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v_ac_573_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set___boxed(lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
uint8_t v_x_28__boxed_585_; lean_object* v_res_586_; 
v_x_28__boxed_585_ = lean_unbox(v_x_582_);
v_res_586_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_x_28__boxed_585_, v_x_583_, v_x_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object* v_hyp_592_, lean_object* v_result_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
if (lean_obj_tag(v_result_593_) == 0)
{
lean_object* v___x_600_; 
lean_dec_ref_known(v_result_593_, 0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_hyp_592_);
return v___x_600_;
}
else
{
lean_object* v_e_x27_601_; lean_object* v_proof_602_; lean_object* v_name_603_; lean_object* v_type_604_; lean_object* v_value_605_; lean_object* v_source_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_635_; 
v_e_x27_601_ = lean_ctor_get(v_result_593_, 0);
lean_inc_ref(v_e_x27_601_);
v_proof_602_ = lean_ctor_get(v_result_593_, 1);
lean_inc_ref(v_proof_602_);
lean_dec_ref_known(v_result_593_, 2);
v_name_603_ = lean_ctor_get(v_hyp_592_, 0);
v_type_604_ = lean_ctor_get(v_hyp_592_, 1);
v_value_605_ = lean_ctor_get(v_hyp_592_, 2);
v_source_606_ = lean_ctor_get(v_hyp_592_, 3);
v_isSharedCheck_635_ = !lean_is_exclusive(v_hyp_592_);
if (v_isSharedCheck_635_ == 0)
{
v___x_608_ = v_hyp_592_;
v_isShared_609_ = v_isSharedCheck_635_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_source_606_);
lean_inc(v_value_605_);
lean_inc(v_type_604_);
lean_inc(v_name_603_);
lean_dec(v_hyp_592_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_635_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; 
lean_inc_ref(v_type_604_);
v___x_610_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_604_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_626_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_626_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_626_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_626_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_615_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2));
v___x_616_ = lean_box(0);
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v_a_611_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_mkConst(v___x_615_, v___x_617_);
lean_inc_ref(v_e_x27_601_);
v___x_619_ = l_Lean_mkApp4(v___x_618_, v_type_604_, v_e_x27_601_, v_proof_602_, v_value_605_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 2, v___x_619_);
lean_ctor_set(v___x_608_, 1, v_e_x27_601_);
v___x_621_ = v___x_608_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_name_603_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_e_x27_601_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_source_606_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_621_);
v___x_623_ = v___x_613_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_del_object(v___x_608_);
lean_dec(v_source_606_);
lean_dec_ref(v_value_605_);
lean_dec_ref(v_type_604_);
lean_dec(v_name_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_e_x27_601_);
v_a_627_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_610_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_610_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object* v_hyp_636_, lean_object* v_result_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_636_, v_result_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object* v_hyp_645_, lean_object* v_result_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_645_, v_result_646_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object* v_hyp_655_, lean_object* v_result_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_655_, v_result_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object* v_hyp_665_, lean_object* v_result_666_){
_start:
{
lean_object* v_name_668_; lean_object* v_type_669_; lean_object* v_value_670_; lean_object* v_source_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_680_; 
v_name_668_ = lean_ctor_get(v_hyp_665_, 0);
v_type_669_ = lean_ctor_get(v_hyp_665_, 1);
v_value_670_ = lean_ctor_get(v_hyp_665_, 2);
v_source_671_ = lean_ctor_get(v_hyp_665_, 3);
v_isSharedCheck_680_ = !lean_is_exclusive(v_hyp_665_);
if (v_isSharedCheck_680_ == 0)
{
v___x_673_ = v_hyp_665_;
v_isShared_674_ = v_isSharedCheck_680_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_source_671_);
lean_inc(v_value_670_);
lean_inc(v_type_669_);
lean_inc(v_name_668_);
lean_dec(v_hyp_665_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_680_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_type_669_, v_result_666_);
lean_dec_ref(v_type_669_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_name_668_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_value_670_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_source_671_);
v___x_677_ = v_reuseFailAlloc_679_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object* v_hyp_681_, lean_object* v_result_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_681_, v_result_682_);
lean_dec_ref(v_result_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object* v_hyp_685_, lean_object* v_result_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_685_, v_result_686_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object* v_hyp_695_, lean_object* v_result_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_695_, v_result_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_result_696_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_705_){
_start:
{
lean_object* v_config_707_; lean_object* v___x_708_; 
v_config_707_ = lean_ctor_get(v_a_705_, 0);
lean_inc_ref(v_config_707_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_config_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_709_);
lean_dec_ref(v_a_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_config_724_; lean_object* v___x_725_; 
v_config_724_ = lean_ctor_get(v_a_712_, 0);
lean_inc_ref(v_config_724_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_config_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(lean_object* v_a_739_){
_start:
{
lean_object* v_mode_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_mode_741_ = lean_ctor_get(v_a_739_, 1);
v___x_742_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg___boxed(lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(v_a_744_);
lean_dec_ref(v_a_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_mode_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_mode_759_ = lean_ctor_get(v_a_747_, 1);
v___x_760_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___boxed(lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(lean_object* v_a_775_){
_start:
{
lean_object* v_mode_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_mode_777_ = lean_ctor_get(v_a_775_, 1);
v___x_778_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_777_);
v___x_779_ = lean_box(v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg___boxed(lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(v_a_781_);
lean_dec_ref(v_a_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_mode_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_mode_796_ = lean_ctor_get(v_a_784_, 1);
v___x_797_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_796_);
v___x_798_ = lean_box(v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___boxed(lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_target_816_; lean_object* v___x_817_; 
v___x_815_ = lean_st_ref_get(v_a_813_);
v_target_816_ = lean_ctor_get(v___x_815_, 2);
lean_inc_ref(v_target_816_);
lean_dec(v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v_target_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg___boxed(lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(v_a_818_);
lean_dec(v_a_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_target_834_; lean_object* v___x_835_; 
v___x_833_ = lean_st_ref_get(v_a_822_);
v_target_834_ = lean_ctor_get(v___x_833_, 2);
lean_inc_ref(v_target_834_);
lean_dec(v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v_target_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___boxed(lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_target_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_851_ = lean_st_ref_get(v_a_849_);
v_target_852_ = lean_ctor_get(v___x_851_, 2);
lean_inc_ref(v_target_852_);
lean_dec(v___x_851_);
v___x_853_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_852_);
lean_dec_ref(v_target_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg___boxed(lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(v_a_855_);
lean_dec(v_a_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_target_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = lean_st_ref_get(v_a_859_);
v_target_871_ = lean_ctor_get(v___x_870_, 2);
lean_inc_ref(v_target_871_);
lean_dec(v___x_870_);
v___x_872_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_871_);
lean_dec_ref(v_target_871_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed(lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(lean_object* v_target_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; lean_object* v_caches_891_; lean_object* v_typeAnalysis_892_; lean_object* v_hypotheses_893_; uint8_t v_didChange_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_904_; 
v___x_890_ = lean_st_ref_take(v_a_888_);
v_caches_891_ = lean_ctor_get(v___x_890_, 0);
v_typeAnalysis_892_ = lean_ctor_get(v___x_890_, 1);
v_hypotheses_893_ = lean_ctor_get(v___x_890_, 3);
v_didChange_894_ = lean_ctor_get_uint8(v___x_890_, sizeof(void*)*4);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_890_, 2);
lean_dec(v_unused_905_);
v___x_896_ = v___x_890_;
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_hypotheses_893_);
lean_inc(v_typeAnalysis_892_);
lean_inc(v_caches_891_);
lean_dec(v___x_890_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v_target_887_);
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_caches_891_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_typeAnalysis_892_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_target_887_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_hypotheses_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*4, v_didChange_894_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_st_ref_put(v_a_888_, v___x_899_);
v___x_901_ = lean_box(0);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg___boxed(lean_object* v_target_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(v_target_906_, v_a_907_);
lean_dec(v_a_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(lean_object* v_target_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_923_; lean_object* v_caches_924_; lean_object* v_typeAnalysis_925_; lean_object* v_hypotheses_926_; uint8_t v_didChange_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_937_; 
v___x_923_ = lean_st_ref_take(v_a_912_);
v_caches_924_ = lean_ctor_get(v___x_923_, 0);
v_typeAnalysis_925_ = lean_ctor_get(v___x_923_, 1);
v_hypotheses_926_ = lean_ctor_get(v___x_923_, 3);
v_didChange_927_ = lean_ctor_get_uint8(v___x_923_, sizeof(void*)*4);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___x_923_, 2);
lean_dec(v_unused_938_);
v___x_929_ = v___x_923_;
v_isShared_930_ = v_isSharedCheck_937_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_hypotheses_926_);
lean_inc(v_typeAnalysis_925_);
lean_inc(v_caches_924_);
lean_dec(v___x_923_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_937_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 2, v_target_910_);
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_caches_924_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_typeAnalysis_925_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_target_910_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_hypotheses_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*4, v_didChange_927_);
v___x_932_ = v_reuseFailAlloc_936_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_st_ref_put(v_a_912_, v___x_932_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___boxed(lean_object* v_target_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(v_target_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_952_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0(void){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_instMonadControlReaderT(lean_box(0), lean_box(0));
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1(void){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_instMonadControlStateRefT_x27(lean_box(0), lean_box(0), lean_box(0));
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2(void){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_instMonadEIO(lean_box(0));
return v___x_955_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2);
v___x_957_ = l_StateRefT_x27_instMonad___redArg(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(lean_object* v_x_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_974_; lean_object* v_target_975_; 
v___x_974_ = lean_st_ref_get(v_a_963_);
v_target_975_ = lean_ctor_get(v___x_974_, 2);
lean_inc_ref(v_target_975_);
lean_dec(v___x_974_);
if (lean_obj_tag(v_target_975_) == 1)
{
lean_object* v_goal_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1104_; 
v_goal_976_ = lean_ctor_get(v_target_975_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_target_975_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_978_ = v_target_975_;
v_isShared_979_ = v_isSharedCheck_1104_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_goal_976_);
lean_dec(v_target_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1104_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_toApplicative_983_; lean_object* v_toFunctor_984_; lean_object* v_toSeq_985_; lean_object* v_toSeqLeft_986_; lean_object* v_toSeqRight_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v_toApplicative_1016_; lean_object* v_toFunctor_1017_; lean_object* v_toSeq_1018_; lean_object* v_toSeqLeft_1019_; lean_object* v_toSeqRight_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_toApplicative_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1102_; 
v___x_980_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_981_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_982_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_983_ = lean_ctor_get(v___x_982_, 0);
v_toFunctor_984_ = lean_ctor_get(v_toApplicative_983_, 0);
v_toSeq_985_ = lean_ctor_get(v_toApplicative_983_, 2);
v_toSeqLeft_986_ = lean_ctor_get(v_toApplicative_983_, 3);
v_toSeqRight_987_ = lean_ctor_get(v_toApplicative_983_, 4);
v___f_988_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_989_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_984_, 2);
v___f_990_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_990_, 0, v_toFunctor_984_);
v___f_991_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_991_, 0, v_toFunctor_984_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___f_990_);
lean_ctor_set(v___x_992_, 1, v___f_991_);
lean_inc(v_toSeqRight_987_);
v___f_993_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_993_, 0, v_toSeqRight_987_);
lean_inc(v_toSeqLeft_986_);
v___f_994_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_994_, 0, v_toSeqLeft_986_);
lean_inc(v_toSeq_985_);
v___f_995_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_995_, 0, v_toSeq_985_);
v___x_996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_996_, 0, v___x_992_);
lean_ctor_set(v___x_996_, 1, v___f_988_);
lean_ctor_set(v___x_996_, 2, v___f_995_);
lean_ctor_set(v___x_996_, 3, v___f_994_);
lean_ctor_set(v___x_996_, 4, v___f_993_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___f_989_);
v___x_998_ = l_StateRefT_x27_instMonad___redArg(v___x_997_);
v___x_999_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_999_, 0, lean_box(0));
lean_closure_set(v___x_999_, 1, lean_box(0));
lean_closure_set(v___x_999_, 2, v___x_998_);
v___x_1000_ = l_instMonadControlTOfPure___redArg(v___x_999_);
lean_inc_ref(v___x_1000_);
v___f_1001_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1001_, 0, v___x_981_);
lean_closure_set(v___f_1001_, 1, v___x_1000_);
v___f_1002_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1002_, 0, v___x_981_);
lean_closure_set(v___f_1002_, 1, v___x_1000_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___f_1001_);
lean_ctor_set(v___x_1003_, 1, v___f_1002_);
lean_inc_ref(v___x_1003_);
v___f_1004_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1004_, 0, v___x_980_);
lean_closure_set(v___f_1004_, 1, v___x_1003_);
v___f_1005_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1005_, 0, v___x_980_);
lean_closure_set(v___f_1005_, 1, v___x_1003_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___f_1004_);
lean_ctor_set(v___x_1006_, 1, v___f_1005_);
lean_inc_ref(v___x_1006_);
v___f_1007_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1007_, 0, v___x_981_);
lean_closure_set(v___f_1007_, 1, v___x_1006_);
v___f_1008_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1008_, 0, v___x_981_);
lean_closure_set(v___f_1008_, 1, v___x_1006_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___f_1007_);
lean_ctor_set(v___x_1009_, 1, v___f_1008_);
lean_inc_ref(v___x_1009_);
v___f_1010_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1010_, 0, v___x_980_);
lean_closure_set(v___f_1010_, 1, v___x_1009_);
v___f_1011_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1011_, 0, v___x_980_);
lean_closure_set(v___f_1011_, 1, v___x_1009_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___f_1010_);
lean_ctor_set(v___x_1012_, 1, v___f_1011_);
lean_inc_ref(v___x_1012_);
v___f_1013_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1013_, 0, v___x_980_);
lean_closure_set(v___f_1013_, 1, v___x_1012_);
v___f_1014_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1014_, 0, v___x_980_);
lean_closure_set(v___f_1014_, 1, v___x_1012_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___f_1013_);
lean_ctor_set(v___x_1015_, 1, v___f_1014_);
v_toApplicative_1016_ = lean_ctor_get(v___x_982_, 0);
v_toFunctor_1017_ = lean_ctor_get(v_toApplicative_1016_, 0);
v_toSeq_1018_ = lean_ctor_get(v_toApplicative_1016_, 2);
v_toSeqLeft_1019_ = lean_ctor_get(v_toApplicative_1016_, 3);
v_toSeqRight_1020_ = lean_ctor_get(v_toApplicative_1016_, 4);
lean_inc_ref_n(v_toFunctor_1017_, 2);
v___f_1021_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1021_, 0, v_toFunctor_1017_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toFunctor_1017_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___f_1021_);
lean_ctor_set(v___x_1023_, 1, v___f_1022_);
lean_inc(v_toSeqRight_1020_);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toSeqRight_1020_);
lean_inc(v_toSeqLeft_1019_);
v___f_1025_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1025_, 0, v_toSeqLeft_1019_);
lean_inc(v_toSeq_1018_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toSeq_1018_);
v___x_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1023_);
lean_ctor_set(v___x_1027_, 1, v___f_988_);
lean_ctor_set(v___x_1027_, 2, v___f_1026_);
lean_ctor_set(v___x_1027_, 3, v___f_1025_);
lean_ctor_set(v___x_1027_, 4, v___f_1024_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___f_989_);
v___x_1029_ = l_StateRefT_x27_instMonad___redArg(v___x_1028_);
v_toApplicative_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v___x_1029_, 1);
lean_dec(v_unused_1103_);
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1102_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_toApplicative_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1102_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_toFunctor_1034_; lean_object* v_toSeq_1035_; lean_object* v_toSeqLeft_1036_; lean_object* v_toSeqRight_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1100_; 
v_toFunctor_1034_ = lean_ctor_get(v_toApplicative_1030_, 0);
v_toSeq_1035_ = lean_ctor_get(v_toApplicative_1030_, 2);
v_toSeqLeft_1036_ = lean_ctor_get(v_toApplicative_1030_, 3);
v_toSeqRight_1037_ = lean_ctor_get(v_toApplicative_1030_, 4);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_toApplicative_1030_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v_toApplicative_1030_, 1);
lean_dec(v_unused_1101_);
v___x_1039_ = v_toApplicative_1030_;
v_isShared_1040_ = v_isSharedCheck_1100_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_toSeqRight_1037_);
lean_inc(v_toSeqLeft_1036_);
lean_inc(v_toSeq_1035_);
lean_inc(v_toFunctor_1034_);
lean_dec(v_toApplicative_1030_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1100_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___x_1050_; 
v___f_1041_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1042_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1034_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toFunctor_1034_);
v___f_1044_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1044_, 0, v_toFunctor_1034_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___f_1043_);
lean_ctor_set(v___x_1045_, 1, v___f_1044_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toSeqRight_1037_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toSeqLeft_1036_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toSeq_1035_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___f_1046_);
lean_ctor_set(v___x_1039_, 3, v___f_1047_);
lean_ctor_set(v___x_1039_, 2, v___f_1048_);
lean_ctor_set(v___x_1039_, 1, v___f_1041_);
lean_ctor_set(v___x_1039_, 0, v___x_1045_);
v___x_1050_ = v___x_1039_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___f_1041_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v___f_1048_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v___f_1047_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v___f_1046_);
v___x_1050_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___f_1042_);
lean_ctor_set(v___x_1032_, 0, v___x_1050_);
v___x_1052_ = v___x_1032_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___f_1042_);
v___x_1052_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_mvarId_1058_; lean_object* v___x_1059_; lean_object* v___x_5044__overap_1060_; lean_object* v___x_1061_; 
v___x_1053_ = l_StateRefT_x27_instMonad___redArg(v___x_1052_);
v___x_1054_ = l_ReaderT_instMonad___redArg(v___x_1053_);
v___x_1055_ = l_StateRefT_x27_instMonad___redArg(v___x_1054_);
v___x_1056_ = l_ReaderT_instMonad___redArg(v___x_1055_);
v___x_1057_ = l_ReaderT_instMonad___redArg(v___x_1056_);
v_mvarId_1058_ = lean_ctor_get(v_goal_976_, 1);
lean_inc(v_mvarId_1058_);
v___x_1059_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1059_, 0, lean_box(0));
lean_closure_set(v___x_1059_, 1, v_goal_976_);
lean_closure_set(v___x_1059_, 2, v_x_962_);
v___x_5044__overap_1060_ = l_Lean_MVarId_withContext___redArg(v___x_1015_, v___x_1057_, v_mvarId_1058_, v___x_1059_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_a_966_);
lean_inc_ref(v_a_965_);
lean_inc(v_a_964_);
v___x_1061_ = lean_apply_10(v___x_5044__overap_1060_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1089_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1089_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1089_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1068_; lean_object* v_caches_1069_; lean_object* v_typeAnalysis_1070_; lean_object* v_hypotheses_1071_; uint8_t v_didChange_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1087_; 
v_fst_1066_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_fst_1066_);
v_snd_1067_ = lean_ctor_get(v_a_1062_, 1);
lean_inc(v_snd_1067_);
lean_dec(v_a_1062_);
v___x_1068_ = lean_st_ref_take(v_a_963_);
v_caches_1069_ = lean_ctor_get(v___x_1068_, 0);
v_typeAnalysis_1070_ = lean_ctor_get(v___x_1068_, 1);
v_hypotheses_1071_ = lean_ctor_get(v___x_1068_, 3);
v_didChange_1072_ = lean_ctor_get_uint8(v___x_1068_, sizeof(void*)*4);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v___x_1068_, 2);
lean_dec(v_unused_1088_);
v___x_1074_ = v___x_1068_;
v_isShared_1075_ = v_isSharedCheck_1087_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_hypotheses_1071_);
lean_inc(v_typeAnalysis_1070_);
lean_inc(v_caches_1069_);
lean_dec(v___x_1068_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1087_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_snd_1067_);
v___x_1077_ = v___x_978_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_snd_1067_);
v___x_1077_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 2, v___x_1077_);
v___x_1079_ = v___x_1074_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_caches_1069_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_typeAnalysis_1070_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_hypotheses_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*4, v_didChange_1072_);
v___x_1079_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = lean_st_ref_put(v_a_963_, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_fst_1066_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1081_);
v___x_1083_ = v___x_1064_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_del_object(v___x_978_);
v_a_1090_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1061_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1061_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
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
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec_ref(v_target_975_);
lean_dec_ref(v_x_962_);
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___boxed(lean_object* v_x_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(v_x_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec(v_a_1108_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(lean_object* v_00_u03b1_1120_, lean_object* v_x_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_target_1135_; 
v___x_1134_ = lean_st_ref_get(v_a_1123_);
v_target_1135_ = lean_ctor_get(v___x_1134_, 2);
lean_inc_ref(v_target_1135_);
lean_dec(v___x_1134_);
if (lean_obj_tag(v_target_1135_) == 1)
{
lean_object* v_goal_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1264_; 
v_goal_1136_ = lean_ctor_get(v_target_1135_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_target_1135_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1138_ = v_target_1135_;
v_isShared_1139_ = v_isSharedCheck_1264_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_goal_1136_);
lean_dec(v_target_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1264_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_toApplicative_1143_; lean_object* v_toFunctor_1144_; lean_object* v_toSeq_1145_; lean_object* v_toSeqLeft_1146_; lean_object* v_toSeqRight_1147_; lean_object* v___f_1148_; lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v___f_1153_; lean_object* v___f_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___f_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v_toApplicative_1176_; lean_object* v_toFunctor_1177_; lean_object* v_toSeq_1178_; lean_object* v_toSeqLeft_1179_; lean_object* v_toSeqRight_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_toApplicative_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1262_; 
v___x_1140_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_1141_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_1142_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_1143_ = lean_ctor_get(v___x_1142_, 0);
v_toFunctor_1144_ = lean_ctor_get(v_toApplicative_1143_, 0);
v_toSeq_1145_ = lean_ctor_get(v_toApplicative_1143_, 2);
v_toSeqLeft_1146_ = lean_ctor_get(v_toApplicative_1143_, 3);
v_toSeqRight_1147_ = lean_ctor_get(v_toApplicative_1143_, 4);
v___f_1148_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_1149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_1144_, 2);
v___f_1150_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1150_, 0, v_toFunctor_1144_);
v___f_1151_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1151_, 0, v_toFunctor_1144_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___f_1150_);
lean_ctor_set(v___x_1152_, 1, v___f_1151_);
lean_inc(v_toSeqRight_1147_);
v___f_1153_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1153_, 0, v_toSeqRight_1147_);
lean_inc(v_toSeqLeft_1146_);
v___f_1154_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1154_, 0, v_toSeqLeft_1146_);
lean_inc(v_toSeq_1145_);
v___f_1155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1155_, 0, v_toSeq_1145_);
v___x_1156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1152_);
lean_ctor_set(v___x_1156_, 1, v___f_1148_);
lean_ctor_set(v___x_1156_, 2, v___f_1155_);
lean_ctor_set(v___x_1156_, 3, v___f_1154_);
lean_ctor_set(v___x_1156_, 4, v___f_1153_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___f_1149_);
v___x_1158_ = l_StateRefT_x27_instMonad___redArg(v___x_1157_);
v___x_1159_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1159_, 0, lean_box(0));
lean_closure_set(v___x_1159_, 1, lean_box(0));
lean_closure_set(v___x_1159_, 2, v___x_1158_);
v___x_1160_ = l_instMonadControlTOfPure___redArg(v___x_1159_);
lean_inc_ref(v___x_1160_);
v___f_1161_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1161_, 0, v___x_1141_);
lean_closure_set(v___f_1161_, 1, v___x_1160_);
v___f_1162_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1162_, 0, v___x_1141_);
lean_closure_set(v___f_1162_, 1, v___x_1160_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___f_1161_);
lean_ctor_set(v___x_1163_, 1, v___f_1162_);
lean_inc_ref(v___x_1163_);
v___f_1164_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1164_, 0, v___x_1140_);
lean_closure_set(v___f_1164_, 1, v___x_1163_);
v___f_1165_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1165_, 0, v___x_1140_);
lean_closure_set(v___f_1165_, 1, v___x_1163_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___f_1164_);
lean_ctor_set(v___x_1166_, 1, v___f_1165_);
lean_inc_ref(v___x_1166_);
v___f_1167_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1167_, 0, v___x_1141_);
lean_closure_set(v___f_1167_, 1, v___x_1166_);
v___f_1168_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1168_, 0, v___x_1141_);
lean_closure_set(v___f_1168_, 1, v___x_1166_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___f_1167_);
lean_ctor_set(v___x_1169_, 1, v___f_1168_);
lean_inc_ref(v___x_1169_);
v___f_1170_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1170_, 0, v___x_1140_);
lean_closure_set(v___f_1170_, 1, v___x_1169_);
v___f_1171_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1171_, 0, v___x_1140_);
lean_closure_set(v___f_1171_, 1, v___x_1169_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___f_1170_);
lean_ctor_set(v___x_1172_, 1, v___f_1171_);
lean_inc_ref(v___x_1172_);
v___f_1173_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1173_, 0, v___x_1140_);
lean_closure_set(v___f_1173_, 1, v___x_1172_);
v___f_1174_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1174_, 0, v___x_1140_);
lean_closure_set(v___f_1174_, 1, v___x_1172_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___f_1173_);
lean_ctor_set(v___x_1175_, 1, v___f_1174_);
v_toApplicative_1176_ = lean_ctor_get(v___x_1142_, 0);
v_toFunctor_1177_ = lean_ctor_get(v_toApplicative_1176_, 0);
v_toSeq_1178_ = lean_ctor_get(v_toApplicative_1176_, 2);
v_toSeqLeft_1179_ = lean_ctor_get(v_toApplicative_1176_, 3);
v_toSeqRight_1180_ = lean_ctor_get(v_toApplicative_1176_, 4);
lean_inc_ref_n(v_toFunctor_1177_, 2);
v___f_1181_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1181_, 0, v_toFunctor_1177_);
v___f_1182_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1182_, 0, v_toFunctor_1177_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___f_1181_);
lean_ctor_set(v___x_1183_, 1, v___f_1182_);
lean_inc(v_toSeqRight_1180_);
v___f_1184_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1184_, 0, v_toSeqRight_1180_);
lean_inc(v_toSeqLeft_1179_);
v___f_1185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1185_, 0, v_toSeqLeft_1179_);
lean_inc(v_toSeq_1178_);
v___f_1186_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1186_, 0, v_toSeq_1178_);
v___x_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1183_);
lean_ctor_set(v___x_1187_, 1, v___f_1148_);
lean_ctor_set(v___x_1187_, 2, v___f_1186_);
lean_ctor_set(v___x_1187_, 3, v___f_1185_);
lean_ctor_set(v___x_1187_, 4, v___f_1184_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v___f_1149_);
v___x_1189_ = l_StateRefT_x27_instMonad___redArg(v___x_1188_);
v_toApplicative_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1189_, 1);
lean_dec(v_unused_1263_);
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1262_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_toApplicative_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1262_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_toFunctor_1194_; lean_object* v_toSeq_1195_; lean_object* v_toSeqLeft_1196_; lean_object* v_toSeqRight_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1260_; 
v_toFunctor_1194_ = lean_ctor_get(v_toApplicative_1190_, 0);
v_toSeq_1195_ = lean_ctor_get(v_toApplicative_1190_, 2);
v_toSeqLeft_1196_ = lean_ctor_get(v_toApplicative_1190_, 3);
v_toSeqRight_1197_ = lean_ctor_get(v_toApplicative_1190_, 4);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_toApplicative_1190_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_toApplicative_1190_, 1);
lean_dec(v_unused_1261_);
v___x_1199_ = v_toApplicative_1190_;
v_isShared_1200_ = v_isSharedCheck_1260_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_toSeqRight_1197_);
lean_inc(v_toSeqLeft_1196_);
lean_inc(v_toSeq_1195_);
lean_inc(v_toFunctor_1194_);
lean_dec(v_toApplicative_1190_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1260_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1210_; 
v___f_1201_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1202_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1194_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toFunctor_1194_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toFunctor_1194_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___f_1203_);
lean_ctor_set(v___x_1205_, 1, v___f_1204_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toSeqRight_1197_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toSeqLeft_1196_);
v___f_1208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1208_, 0, v_toSeq_1195_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 4, v___f_1206_);
lean_ctor_set(v___x_1199_, 3, v___f_1207_);
lean_ctor_set(v___x_1199_, 2, v___f_1208_);
lean_ctor_set(v___x_1199_, 1, v___f_1201_);
lean_ctor_set(v___x_1199_, 0, v___x_1205_);
v___x_1210_ = v___x_1199_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___f_1201_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v___f_1208_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v___f_1207_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v___f_1206_);
v___x_1210_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___f_1202_);
lean_ctor_set(v___x_1192_, 0, v___x_1210_);
v___x_1212_ = v___x_1192_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___f_1202_);
v___x_1212_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_mvarId_1218_; lean_object* v___x_1219_; lean_object* v___x_5196__overap_1220_; lean_object* v___x_1221_; 
v___x_1213_ = l_StateRefT_x27_instMonad___redArg(v___x_1212_);
v___x_1214_ = l_ReaderT_instMonad___redArg(v___x_1213_);
v___x_1215_ = l_StateRefT_x27_instMonad___redArg(v___x_1214_);
v___x_1216_ = l_ReaderT_instMonad___redArg(v___x_1215_);
v___x_1217_ = l_ReaderT_instMonad___redArg(v___x_1216_);
v_mvarId_1218_ = lean_ctor_get(v_goal_1136_, 1);
lean_inc(v_mvarId_1218_);
v___x_1219_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1219_, 0, lean_box(0));
lean_closure_set(v___x_1219_, 1, v_goal_1136_);
lean_closure_set(v___x_1219_, 2, v_x_1121_);
v___x_5196__overap_1220_ = l_Lean_MVarId_withContext___redArg(v___x_1175_, v___x_1217_, v_mvarId_1218_, v___x_1219_);
lean_inc(v_a_1132_);
lean_inc_ref(v_a_1131_);
lean_inc(v_a_1130_);
lean_inc_ref(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc_ref(v_a_1127_);
lean_inc(v_a_1126_);
lean_inc_ref(v_a_1125_);
lean_inc(v_a_1124_);
v___x_1221_ = lean_apply_10(v___x_5196__overap_1220_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, lean_box(0));
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1249_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1249_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1249_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___x_1228_; lean_object* v_caches_1229_; lean_object* v_typeAnalysis_1230_; lean_object* v_hypotheses_1231_; uint8_t v_didChange_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1247_; 
v_fst_1226_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_fst_1226_);
v_snd_1227_ = lean_ctor_get(v_a_1222_, 1);
lean_inc(v_snd_1227_);
lean_dec(v_a_1222_);
v___x_1228_ = lean_st_ref_take(v_a_1123_);
v_caches_1229_ = lean_ctor_get(v___x_1228_, 0);
v_typeAnalysis_1230_ = lean_ctor_get(v___x_1228_, 1);
v_hypotheses_1231_ = lean_ctor_get(v___x_1228_, 3);
v_didChange_1232_ = lean_ctor_get_uint8(v___x_1228_, sizeof(void*)*4);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1228_, 2);
lean_dec(v_unused_1248_);
v___x_1234_ = v___x_1228_;
v_isShared_1235_ = v_isSharedCheck_1247_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_hypotheses_1231_);
lean_inc(v_typeAnalysis_1230_);
lean_inc(v_caches_1229_);
lean_dec(v___x_1228_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1247_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_snd_1227_);
v___x_1237_ = v___x_1138_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_snd_1227_);
v___x_1237_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 2, v___x_1237_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_caches_1229_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_typeAnalysis_1230_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_hypotheses_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1245_, sizeof(void*)*4, v_didChange_1232_);
v___x_1239_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1240_ = lean_st_ref_put(v_a_1123_, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_fst_1226_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1241_);
v___x_1243_ = v___x_1224_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_del_object(v___x_1138_);
v_a_1250_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1221_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1221_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
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
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v_target_1135_);
lean_dec_ref(v_x_1121_);
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_x_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(v_00_u03b1_1267_, v_x_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
v___x_1293_ = lean_apply_10(v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, lean_box(0));
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed(lean_object* v_x_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(v_x_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(lean_object* v_mvarId_1306_, lean_object* v_x_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___f_1318_; lean_object* v___x_1319_; 
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
v___f_1318_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1318_, 0, v_x_1307_);
lean_closure_set(v___f_1318_, 1, v___y_1308_);
lean_closure_set(v___f_1318_, 2, v___y_1309_);
lean_closure_set(v___f_1318_, 3, v___y_1310_);
lean_closure_set(v___f_1318_, 4, v___y_1311_);
lean_closure_set(v___f_1318_, 5, v___y_1312_);
v___x_1319_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1306_, v___f_1318_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1319_) == 0)
{
return v___x_1319_;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___boxed(lean_object* v_mvarId_1328_, lean_object* v_x_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1328_, v_x_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(lean_object* v_00_u03b1_1341_, lean_object* v_mvarId_1342_, lean_object* v_x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1342_, v_x_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_mvarId_1356_, lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(v_00_u03b1_1355_, v_mvarId_1356_, v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(lean_object* v_goal_1369_, lean_object* v_falseProof_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_st_mk_ref(v_goal_1369_);
v___x_1382_ = l_Lean_Meta_Grind_closeGoal(v_falseProof_1370_, v___x_1381_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1392_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1392_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1392_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1387_ = lean_st_ref_get(v___x_1381_);
lean_dec(v___x_1381_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_a_1383_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1388_);
v___x_1390_ = v___x_1385_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v___x_1381_);
v_a_1393_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1382_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1382_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed(lean_object* v_goal_1401_, lean_object* v_falseProof_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(v_goal_1401_, v_falseProof_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object* v_falseProof_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1426_; lean_object* v_target_1427_; 
v___x_1426_ = lean_st_ref_get(v_a_1415_);
v_target_1427_ = lean_ctor_get(v___x_1426_, 2);
lean_inc_ref(v_target_1427_);
lean_dec(v___x_1426_);
if (lean_obj_tag(v_target_1427_) == 0)
{
lean_object* v_mvar_1428_; lean_object* v___x_1429_; 
v_mvar_1428_ = lean_ctor_get(v_target_1427_, 0);
lean_inc(v_mvar_1428_);
lean_dec_ref_known(v_target_1427_, 1);
v___x_1429_ = l_Lean_MVarId_assignFalseProof(v_mvar_1428_, v_falseProof_1414_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
return v___x_1429_;
}
else
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1481_; 
v_isSharedCheck_1481_ = !lean_is_exclusive(v_target_1427_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_target_1427_, 0);
lean_dec(v_unused_1482_);
v___x_1431_ = v_target_1427_;
v_isShared_1432_ = v_isSharedCheck_1481_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v_target_1427_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1481_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v_target_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_st_ref_get(v_a_1415_);
v_target_1434_ = lean_ctor_get(v___x_1433_, 2);
lean_inc_ref(v_target_1434_);
lean_dec(v___x_1433_);
v___x_1435_ = lean_box(0);
if (lean_obj_tag(v_target_1434_) == 1)
{
lean_object* v_goal_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1477_; 
lean_del_object(v___x_1431_);
v_goal_1436_ = lean_ctor_get(v_target_1434_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_target_1434_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1438_ = v_target_1434_;
v_isShared_1439_ = v_isSharedCheck_1477_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_goal_1436_);
lean_dec(v_target_1434_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1477_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_mvarId_1440_; lean_object* v___f_1441_; lean_object* v___x_1442_; 
v_mvarId_1440_ = lean_ctor_get(v_goal_1436_, 1);
lean_inc(v_mvarId_1440_);
v___f_1441_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1441_, 0, v_goal_1436_);
lean_closure_set(v___f_1441_, 1, v_falseProof_1414_);
v___x_1442_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1440_, v___f_1441_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1468_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1468_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1468_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v_snd_1447_; lean_object* v___x_1448_; lean_object* v_caches_1449_; lean_object* v_typeAnalysis_1450_; lean_object* v_hypotheses_1451_; uint8_t v_didChange_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1466_; 
v_snd_1447_ = lean_ctor_get(v_a_1443_, 1);
lean_inc(v_snd_1447_);
lean_dec(v_a_1443_);
v___x_1448_ = lean_st_ref_take(v_a_1415_);
v_caches_1449_ = lean_ctor_get(v___x_1448_, 0);
v_typeAnalysis_1450_ = lean_ctor_get(v___x_1448_, 1);
v_hypotheses_1451_ = lean_ctor_get(v___x_1448_, 3);
v_didChange_1452_ = lean_ctor_get_uint8(v___x_1448_, sizeof(void*)*4);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v___x_1448_, 2);
lean_dec(v_unused_1467_);
v___x_1454_ = v___x_1448_;
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_hypotheses_1451_);
lean_inc(v_typeAnalysis_1450_);
lean_inc(v_caches_1449_);
lean_dec(v___x_1448_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v_snd_1447_);
v___x_1457_ = v___x_1438_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_snd_1447_);
v___x_1457_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 2, v___x_1457_);
v___x_1459_ = v___x_1454_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_caches_1449_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_typeAnalysis_1450_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_hypotheses_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*4, v_didChange_1452_);
v___x_1459_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_st_ref_put(v_a_1415_, v___x_1459_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1435_);
v___x_1462_ = v___x_1445_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1435_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_del_object(v___x_1438_);
v_a_1469_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1442_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1442_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
else
{
lean_object* v___x_1479_; 
lean_dec_ref(v_target_1434_);
lean_dec_ref(v_falseProof_1414_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1435_);
v___x_1479_ = v___x_1431_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1435_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___boxed(lean_object* v_falseProof_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec(v_a_1484_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(lean_object* v_falseProof_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1496_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed(lean_object* v_falseProof_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(v_falseProof_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
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
lean_dec_ref(v_a_1511_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1526_; uint8_t v_didChange_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1526_ = lean_st_ref_get(v_a_1524_);
v_didChange_1527_ = lean_ctor_get_uint8(v___x_1526_, sizeof(void*)*4);
lean_dec(v___x_1526_);
v___x_1528_ = lean_box(v_didChange_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_1530_);
lean_dec(v_a_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___x_1545_; uint8_t v_didChange_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1545_ = lean_st_ref_get(v_a_1534_);
v_didChange_1546_ = lean_ctor_get_uint8(v___x_1545_, sizeof(void*)*4);
lean_dec(v___x_1545_);
v___x_1547_ = lean_box(v_didChange_1546_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v_caches_1565_; lean_object* v_typeAnalysis_1566_; lean_object* v_target_1567_; lean_object* v_hypotheses_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1579_; 
v___x_1564_ = lean_st_ref_take(v_a_1562_);
v_caches_1565_ = lean_ctor_get(v___x_1564_, 0);
v_typeAnalysis_1566_ = lean_ctor_get(v___x_1564_, 1);
v_target_1567_ = lean_ctor_get(v___x_1564_, 2);
v_hypotheses_1568_ = lean_ctor_get(v___x_1564_, 3);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1570_ = v___x_1564_;
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_hypotheses_1568_);
lean_inc(v_target_1567_);
lean_inc(v_typeAnalysis_1566_);
lean_inc(v_caches_1565_);
lean_dec(v___x_1564_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
uint8_t v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = 0;
if (v_isShared_1571_ == 0)
{
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_caches_1565_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_typeAnalysis_1566_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_target_1567_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_hypotheses_1568_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*4, v___x_1572_);
v___x_1575_ = lean_st_ref_put(v_a_1562_, v___x_1574_);
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_1580_);
lean_dec(v_a_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v_caches_1596_; lean_object* v_typeAnalysis_1597_; lean_object* v_target_1598_; lean_object* v_hypotheses_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1610_; 
v___x_1595_ = lean_st_ref_take(v_a_1584_);
v_caches_1596_ = lean_ctor_get(v___x_1595_, 0);
v_typeAnalysis_1597_ = lean_ctor_get(v___x_1595_, 1);
v_target_1598_ = lean_ctor_get(v___x_1595_, 2);
v_hypotheses_1599_ = lean_ctor_get(v___x_1595_, 3);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1601_ = v___x_1595_;
v_isShared_1602_ = v_isSharedCheck_1610_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_hypotheses_1599_);
lean_inc(v_target_1598_);
lean_inc(v_typeAnalysis_1597_);
lean_inc(v_caches_1596_);
lean_dec(v___x_1595_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1610_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
uint8_t v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = 0;
if (v_isShared_1602_ == 0)
{
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_caches_1596_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_typeAnalysis_1597_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_target_1598_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_hypotheses_1599_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*4, v___x_1603_);
v___x_1606_ = lean_st_ref_put(v_a_1584_, v___x_1605_);
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v_caches_1627_; lean_object* v_typeAnalysis_1628_; lean_object* v_target_1629_; lean_object* v_hypotheses_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1641_; 
v___x_1626_ = lean_st_ref_take(v_a_1624_);
v_caches_1627_ = lean_ctor_get(v___x_1626_, 0);
v_typeAnalysis_1628_ = lean_ctor_get(v___x_1626_, 1);
v_target_1629_ = lean_ctor_get(v___x_1626_, 2);
v_hypotheses_1630_ = lean_ctor_get(v___x_1626_, 3);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1632_ = v___x_1626_;
v_isShared_1633_ = v_isSharedCheck_1641_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_hypotheses_1630_);
lean_inc(v_target_1629_);
lean_inc(v_typeAnalysis_1628_);
lean_inc(v_caches_1627_);
lean_dec(v___x_1626_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1641_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
uint8_t v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = 1;
if (v_isShared_1633_ == 0)
{
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_caches_1627_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_typeAnalysis_1628_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_target_1629_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_hypotheses_1630_);
v___x_1636_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*4, v___x_1634_);
v___x_1637_ = lean_st_ref_put(v_a_1624_, v___x_1636_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_1642_);
lean_dec(v_a_1642_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v_caches_1658_; lean_object* v_typeAnalysis_1659_; lean_object* v_target_1660_; lean_object* v_hypotheses_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1672_; 
v___x_1657_ = lean_st_ref_take(v_a_1646_);
v_caches_1658_ = lean_ctor_get(v___x_1657_, 0);
v_typeAnalysis_1659_ = lean_ctor_get(v___x_1657_, 1);
v_target_1660_ = lean_ctor_get(v___x_1657_, 2);
v_hypotheses_1661_ = lean_ctor_get(v___x_1657_, 3);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1663_ = v___x_1657_;
v_isShared_1664_ = v_isSharedCheck_1672_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_hypotheses_1661_);
lean_inc(v_target_1660_);
lean_inc(v_typeAnalysis_1659_);
lean_inc(v_caches_1658_);
lean_dec(v___x_1657_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1672_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
uint8_t v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = 1;
if (v_isShared_1664_ == 0)
{
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_caches_1658_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_typeAnalysis_1659_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_target_1660_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_hypotheses_1661_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*4, v___x_1665_);
v___x_1668_ = lean_st_ref_put(v_a_1646_, v___x_1667_);
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v_caches_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_st_ref_get(v_a_1686_);
v_caches_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc_ref(v_caches_1689_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_caches_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg___boxed(lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(v_a_1691_);
lean_dec(v_a_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v_caches_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_st_ref_get(v_a_1695_);
v_caches_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc_ref(v_caches_1707_);
lean_dec(v___x_1706_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_caches_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___boxed(lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(lean_object* v_caches_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v_typeAnalysis_1726_; lean_object* v_target_1727_; lean_object* v_hypotheses_1728_; uint8_t v_didChange_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1739_; 
v___x_1725_ = lean_st_ref_take(v_a_1723_);
v_typeAnalysis_1726_ = lean_ctor_get(v___x_1725_, 1);
v_target_1727_ = lean_ctor_get(v___x_1725_, 2);
v_hypotheses_1728_ = lean_ctor_get(v___x_1725_, 3);
v_didChange_1729_ = lean_ctor_get_uint8(v___x_1725_, sizeof(void*)*4);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v___x_1725_, 0);
lean_dec(v_unused_1740_);
v___x_1731_ = v___x_1725_;
v_isShared_1732_ = v_isSharedCheck_1739_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_hypotheses_1728_);
lean_inc(v_target_1727_);
lean_inc(v_typeAnalysis_1726_);
lean_dec(v___x_1725_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1739_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v_caches_1722_);
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_caches_1722_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_typeAnalysis_1726_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_target_1727_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v_hypotheses_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1738_, sizeof(void*)*4, v_didChange_1729_);
v___x_1734_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_st_ref_put(v_a_1723_, v___x_1734_);
v___x_1736_ = lean_box(0);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg___boxed(lean_object* v_caches_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(v_caches_1741_, v_a_1742_);
lean_dec(v_a_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(lean_object* v_caches_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1758_; lean_object* v_typeAnalysis_1759_; lean_object* v_target_1760_; lean_object* v_hypotheses_1761_; uint8_t v_didChange_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1772_; 
v___x_1758_ = lean_st_ref_take(v_a_1747_);
v_typeAnalysis_1759_ = lean_ctor_get(v___x_1758_, 1);
v_target_1760_ = lean_ctor_get(v___x_1758_, 2);
v_hypotheses_1761_ = lean_ctor_get(v___x_1758_, 3);
v_didChange_1762_ = lean_ctor_get_uint8(v___x_1758_, sizeof(void*)*4);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1773_);
v___x_1764_ = v___x_1758_;
v_isShared_1765_ = v_isSharedCheck_1772_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_hypotheses_1761_);
lean_inc(v_target_1760_);
lean_inc(v_typeAnalysis_1759_);
lean_dec(v___x_1758_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1772_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v_caches_1745_);
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_caches_1745_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_typeAnalysis_1759_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_target_1760_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_hypotheses_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1771_, sizeof(void*)*4, v_didChange_1762_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = lean_st_ref_put(v_a_1747_, v___x_1767_);
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___boxed(lean_object* v_caches_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(v_caches_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1787_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_1792_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
lean_ctor_set(v___x_1792_, 2, v___x_1791_);
lean_ctor_set(v___x_1792_, 3, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_mode_1796_; uint8_t v___x_1797_; 
v_mode_1796_ = lean_ctor_get(v_a_1793_, 1);
v___x_1797_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_typeAnalysis_1800_; lean_object* v_target_1801_; lean_object* v_hypotheses_1802_; uint8_t v_didChange_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1813_; 
v___x_1798_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_1799_ = lean_st_ref_take(v_a_1794_);
v_typeAnalysis_1800_ = lean_ctor_get(v___x_1799_, 1);
v_target_1801_ = lean_ctor_get(v___x_1799_, 2);
v_hypotheses_1802_ = lean_ctor_get(v___x_1799_, 3);
v_didChange_1803_ = lean_ctor_get_uint8(v___x_1799_, sizeof(void*)*4);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1799_, 0);
lean_dec(v_unused_1814_);
v___x_1805_ = v___x_1799_;
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_hypotheses_1802_);
lean_inc(v_target_1801_);
lean_inc(v_typeAnalysis_1800_);
lean_dec(v___x_1799_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1798_);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_typeAnalysis_1800_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_target_1801_);
lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_hypotheses_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1812_, sizeof(void*)*4, v_didChange_1803_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_st_ref_put(v_a_1794_, v___x_1808_);
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___boxed(lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1821_, v_a_1822_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___boxed(lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v_typeAnalysis_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_st_ref_get(v_a_1847_);
v_typeAnalysis_1850_ = lean_ctor_get(v___x_1849_, 1);
lean_inc_ref(v_typeAnalysis_1850_);
lean_dec(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_typeAnalysis_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1852_);
lean_dec(v_a_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v_typeAnalysis_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_st_ref_get(v_a_1856_);
v_typeAnalysis_1868_ = lean_ctor_get(v___x_1867_, 1);
lean_inc_ref(v_typeAnalysis_1868_);
lean_dec(v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_typeAnalysis_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v_typeAnalysis_1892_; lean_object* v_interestingStructures_1893_; lean_object* v_uninteresting_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1891_ = lean_st_ref_get(v_a_1889_);
v_typeAnalysis_1892_ = lean_ctor_get(v___x_1891_, 1);
lean_inc_ref(v_typeAnalysis_1892_);
lean_dec(v___x_1891_);
v_interestingStructures_1893_ = lean_ctor_get(v_typeAnalysis_1892_, 0);
lean_inc_ref(v_interestingStructures_1893_);
v_uninteresting_1894_ = lean_ctor_get(v_typeAnalysis_1892_, 3);
lean_inc_ref(v_uninteresting_1894_);
lean_dec_ref(v_typeAnalysis_1892_);
v___x_1895_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1896_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_1888_);
v___x_1897_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1895_, v___x_1896_, v_uninteresting_1894_, v_n_1888_);
lean_dec_ref(v_uninteresting_1894_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; 
v___x_1898_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1895_, v___x_1896_, v_interestingStructures_1893_, v_n_1888_);
lean_dec_ref(v_interestingStructures_1893_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_box(v___x_1898_);
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec_ref(v_interestingStructures_1893_);
lean_dec(v_n_1888_);
v___x_1904_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1906_, v_a_1907_);
lean_dec(v_a_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v_typeAnalysis_1924_; lean_object* v_interestingStructures_1925_; lean_object* v_uninteresting_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1923_ = lean_st_ref_get(v_a_1912_);
v_typeAnalysis_1924_ = lean_ctor_get(v___x_1923_, 1);
lean_inc_ref(v_typeAnalysis_1924_);
lean_dec(v___x_1923_);
v_interestingStructures_1925_ = lean_ctor_get(v_typeAnalysis_1924_, 0);
lean_inc_ref(v_interestingStructures_1925_);
v_uninteresting_1926_ = lean_ctor_get(v_typeAnalysis_1924_, 3);
lean_inc_ref(v_uninteresting_1926_);
lean_dec_ref(v_typeAnalysis_1924_);
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_1910_);
v___x_1929_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1927_, v___x_1928_, v_uninteresting_1926_, v_n_1910_);
lean_dec_ref(v_uninteresting_1926_);
if (v___x_1929_ == 0)
{
uint8_t v___x_1930_; 
v___x_1930_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1927_, v___x_1928_, v_interestingStructures_1925_, v_n_1910_);
lean_dec_ref(v_interestingStructures_1925_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_box(v___x_1930_);
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec_ref(v_interestingStructures_1925_);
lean_dec(v_n_1910_);
v___x_1936_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v_caches_1956_; lean_object* v_typeAnalysis_1957_; lean_object* v_target_1958_; lean_object* v_hypotheses_1959_; uint8_t v_didChange_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1971_; 
v___x_1955_ = lean_st_ref_take(v_a_1953_);
v_caches_1956_ = lean_ctor_get(v___x_1955_, 0);
v_typeAnalysis_1957_ = lean_ctor_get(v___x_1955_, 1);
v_target_1958_ = lean_ctor_get(v___x_1955_, 2);
v_hypotheses_1959_ = lean_ctor_get(v___x_1955_, 3);
v_didChange_1960_ = lean_ctor_get_uint8(v___x_1955_, sizeof(void*)*4);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1962_ = v___x_1955_;
v_isShared_1963_ = v_isSharedCheck_1971_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_hypotheses_1959_);
lean_inc(v_target_1958_);
lean_inc(v_typeAnalysis_1957_);
lean_inc(v_caches_1956_);
lean_dec(v___x_1955_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1971_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_apply_1(v_f_1952_, v_typeAnalysis_1957_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___x_1964_);
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_caches_1956_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_target_1958_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_hypotheses_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1970_, sizeof(void*)*4, v_didChange_1960_);
v___x_1966_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_st_ref_put(v_a_1953_, v___x_1966_);
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_1972_, v_a_1973_);
lean_dec(v_a_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v___x_1989_; lean_object* v_caches_1990_; lean_object* v_typeAnalysis_1991_; lean_object* v_target_1992_; lean_object* v_hypotheses_1993_; uint8_t v_didChange_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2005_; 
v___x_1989_ = lean_st_ref_take(v_a_1978_);
v_caches_1990_ = lean_ctor_get(v___x_1989_, 0);
v_typeAnalysis_1991_ = lean_ctor_get(v___x_1989_, 1);
v_target_1992_ = lean_ctor_get(v___x_1989_, 2);
v_hypotheses_1993_ = lean_ctor_get(v___x_1989_, 3);
v_didChange_1994_ = lean_ctor_get_uint8(v___x_1989_, sizeof(void*)*4);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1996_ = v___x_1989_;
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_hypotheses_1993_);
lean_inc(v_target_1992_);
lean_inc(v_typeAnalysis_1991_);
lean_inc(v_caches_1990_);
lean_dec(v___x_1989_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = lean_apply_1(v_f_1976_, v_typeAnalysis_1991_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v___x_1998_);
v___x_2000_ = v___x_1996_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_caches_1990_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_target_1992_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_hypotheses_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2004_, sizeof(void*)*4, v_didChange_1994_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = lean_st_ref_put(v_a_1978_, v___x_2000_);
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v_typeAnalysis_2024_; lean_object* v_caches_2025_; lean_object* v_target_2026_; lean_object* v_hypotheses_2027_; uint8_t v_didChange_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2115_; 
v___x_2023_ = lean_st_ref_take(v_a_2021_);
v_typeAnalysis_2024_ = lean_ctor_get(v___x_2023_, 1);
v_caches_2025_ = lean_ctor_get(v___x_2023_, 0);
v_target_2026_ = lean_ctor_get(v___x_2023_, 2);
v_hypotheses_2027_ = lean_ctor_get(v___x_2023_, 3);
v_didChange_2028_ = lean_ctor_get_uint8(v___x_2023_, sizeof(void*)*4);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2030_ = v___x_2023_;
v_isShared_2031_ = v_isSharedCheck_2115_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_hypotheses_2027_);
lean_inc(v_target_2026_);
lean_inc(v_typeAnalysis_2024_);
lean_inc(v_caches_2025_);
lean_dec(v___x_2023_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2115_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_interestingStructures_2032_; lean_object* v_interestingEnums_2033_; lean_object* v_interestingMatchers_2034_; lean_object* v_uninteresting_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2114_; 
v_interestingStructures_2032_ = lean_ctor_get(v_typeAnalysis_2024_, 0);
v_interestingEnums_2033_ = lean_ctor_get(v_typeAnalysis_2024_, 1);
v_interestingMatchers_2034_ = lean_ctor_get(v_typeAnalysis_2024_, 2);
v_uninteresting_2035_ = lean_ctor_get(v_typeAnalysis_2024_, 3);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_typeAnalysis_2024_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2037_ = v_typeAnalysis_2024_;
v_isShared_2038_ = v_isSharedCheck_2114_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_uninteresting_2035_);
lean_inc(v_interestingMatchers_2034_);
lean_inc(v_interestingEnums_2033_);
lean_inc(v_interestingStructures_2032_);
lean_dec(v_typeAnalysis_2024_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2114_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___y_2040_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___y_2054_; lean_object* v_i_2055_; lean_object* v___y_2061_; lean_object* v___y_2071_; lean_object* v_i_2072_; lean_object* v___x_2087_; 
v___x_2050_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2051_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2052_ = lean_box(0);
lean_inc(v_n_2020_);
v___x_2087_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2050_, v___x_2051_, v_interestingStructures_2032_, v_n_2020_);
switch(lean_obj_tag(v___x_2087_))
{
case 0:
{
lean_dec_ref_known(v___x_2087_, 3);
lean_dec(v_n_2020_);
v___y_2040_ = v_interestingStructures_2032_;
goto v___jp_2039_;
}
case 1:
{
lean_object* v_index_2088_; lean_object* v_size_2089_; lean_object* v_keyArray_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_index_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_index_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v_size_2089_ = lean_ctor_get(v_interestingStructures_2032_, 0);
v_keyArray_2090_ = lean_ctor_get(v_interestingStructures_2032_, 1);
v___x_2091_ = lean_unsigned_to_nat(1u);
v___x_2092_ = lean_nat_add(v_size_2089_, v___x_2091_);
v___x_2093_ = lean_array_get_size(v_keyArray_2090_);
v___x_2094_ = lean_nat_dec_lt(v___x_2092_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_dec(v___x_2092_);
lean_dec(v_index_2088_);
goto v___jp_2077_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2095_ = lean_unsigned_to_nat(4u);
v___x_2096_ = lean_nat_mul(v___x_2092_, v___x_2095_);
v___x_2097_ = lean_unsigned_to_nat(3u);
v___x_2098_ = lean_nat_mul(v___x_2093_, v___x_2097_);
v___x_2099_ = lean_nat_dec_le(v___x_2096_, v___x_2098_);
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
if (v___x_2099_ == 0)
{
lean_dec(v___x_2092_);
lean_dec(v_index_2088_);
goto v___jp_2077_;
}
else
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Std_DHashMap_Raw_setEntry___redArg(v_interestingStructures_2032_, v___x_2092_, v_index_2088_, v_n_2020_, v___x_2052_);
lean_dec(v_index_2088_);
v___y_2040_ = v___x_2100_;
goto v___jp_2039_;
}
}
}
default: 
{
lean_object* v_size_2101_; lean_object* v_keyArray_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_size_2101_ = lean_ctor_get(v_interestingStructures_2032_, 0);
v_keyArray_2102_ = lean_ctor_get(v_interestingStructures_2032_, 1);
v___x_2103_ = lean_unsigned_to_nat(1u);
v___x_2104_ = lean_nat_add(v_size_2101_, v___x_2103_);
v___x_2105_ = lean_array_get_size(v_keyArray_2102_);
v___x_2106_ = lean_nat_dec_lt(v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
lean_dec(v___x_2104_);
v___x_2107_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2050_, v___x_2051_, v_interestingStructures_2032_);
v___y_2061_ = v___x_2107_;
goto v___jp_2060_;
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2108_ = lean_unsigned_to_nat(4u);
v___x_2109_ = lean_nat_mul(v___x_2104_, v___x_2108_);
lean_dec(v___x_2104_);
v___x_2110_ = lean_unsigned_to_nat(3u);
v___x_2111_ = lean_nat_mul(v___x_2105_, v___x_2110_);
v___x_2112_ = lean_nat_dec_le(v___x_2109_, v___x_2111_);
lean_dec(v___x_2111_);
lean_dec(v___x_2109_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2050_, v___x_2051_, v_interestingStructures_2032_);
v___y_2061_ = v___x_2113_;
goto v___jp_2060_;
}
else
{
v___y_2061_ = v_interestingStructures_2032_;
goto v___jp_2060_;
}
}
}
}
v___jp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___y_2040_);
v___x_2042_ = v___x_2037_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___y_2040_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_interestingEnums_2033_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_interestingMatchers_2034_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_uninteresting_2035_);
v___x_2042_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2044_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2042_);
v___x_2044_ = v___x_2030_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_caches_2025_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_target_2026_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_hypotheses_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2048_, sizeof(void*)*4, v_didChange_2028_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_st_ref_put(v_a_2021_, v___x_2044_);
v___x_2046_ = lean_box(0);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
}
v___jp_2053_:
{
lean_object* v_size_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_size_2056_ = lean_ctor_get(v___y_2054_, 0);
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = lean_nat_add(v_size_2056_, v___x_2057_);
v___x_2059_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2054_, v___x_2058_, v_i_2055_, v_n_2020_, v___x_2052_);
lean_dec(v_i_2055_);
v___y_2040_ = v___x_2059_;
goto v___jp_2039_;
}
v___jp_2060_:
{
lean_object* v___x_2062_; 
lean_inc(v_n_2020_);
v___x_2062_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2050_, v___x_2051_, v___y_2061_, v_n_2020_);
switch(lean_obj_tag(v___x_2062_))
{
case 0:
{
lean_object* v_index_2063_; lean_object* v_size_2064_; lean_object* v___x_2065_; 
v_index_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_index_2063_);
lean_dec_ref_known(v___x_2062_, 3);
v_size_2064_ = lean_ctor_get(v___y_2061_, 0);
lean_inc(v_size_2064_);
v___x_2065_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2061_, v_size_2064_, v_index_2063_, v_n_2020_, v___x_2052_);
lean_dec(v_index_2063_);
v___y_2040_ = v___x_2065_;
goto v___jp_2039_;
}
case 1:
{
lean_object* v_index_2066_; 
v_index_2066_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_index_2066_);
lean_dec_ref_known(v___x_2062_, 1);
v___y_2054_ = v___y_2061_;
v_i_2055_ = v_index_2066_;
goto v___jp_2053_;
}
default: 
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2061_, v___x_2067_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_index_2069_; 
v_index_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_index_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v___y_2054_ = v___y_2061_;
v_i_2055_ = v_index_2069_;
goto v___jp_2053_;
}
else
{
lean_dec(v_n_2020_);
v___y_2040_ = v___y_2061_;
goto v___jp_2039_;
}
}
}
}
v___jp_2070_:
{
lean_object* v_size_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_size_2073_ = lean_ctor_get(v___y_2071_, 0);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_nat_add(v_size_2073_, v___x_2074_);
v___x_2076_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2071_, v___x_2075_, v_i_2072_, v_n_2020_, v___x_2052_);
lean_dec(v_i_2072_);
v___y_2040_ = v___x_2076_;
goto v___jp_2039_;
}
v___jp_2077_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2050_, v___x_2051_, v_interestingStructures_2032_);
lean_inc(v_n_2020_);
v___x_2079_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2050_, v___x_2051_, v___x_2078_, v_n_2020_);
switch(lean_obj_tag(v___x_2079_))
{
case 0:
{
lean_object* v_index_2080_; lean_object* v_size_2081_; lean_object* v___x_2082_; 
v_index_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_index_2080_);
lean_dec_ref_known(v___x_2079_, 3);
v_size_2081_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_size_2081_);
v___x_2082_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2078_, v_size_2081_, v_index_2080_, v_n_2020_, v___x_2052_);
lean_dec(v_index_2080_);
v___y_2040_ = v___x_2082_;
goto v___jp_2039_;
}
case 1:
{
lean_object* v_index_2083_; 
v_index_2083_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_index_2083_);
lean_dec_ref_known(v___x_2079_, 1);
v___y_2071_ = v___x_2078_;
v_i_2072_ = v_index_2083_;
goto v___jp_2070_;
}
default: 
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2078_, v___x_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_index_2086_; 
v_index_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_index_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___y_2071_ = v___x_2078_;
v_i_2072_ = v_index_2086_;
goto v___jp_2070_;
}
else
{
lean_dec(v_n_2020_);
v___y_2040_ = v___x_2078_;
goto v___jp_2039_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_2116_, v_a_2117_);
lean_dec(v_a_2117_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___x_2133_; lean_object* v_typeAnalysis_2134_; lean_object* v_caches_2135_; lean_object* v_target_2136_; lean_object* v_hypotheses_2137_; uint8_t v_didChange_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2225_; 
v___x_2133_ = lean_st_ref_take(v_a_2122_);
v_typeAnalysis_2134_ = lean_ctor_get(v___x_2133_, 1);
v_caches_2135_ = lean_ctor_get(v___x_2133_, 0);
v_target_2136_ = lean_ctor_get(v___x_2133_, 2);
v_hypotheses_2137_ = lean_ctor_get(v___x_2133_, 3);
v_didChange_2138_ = lean_ctor_get_uint8(v___x_2133_, sizeof(void*)*4);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2140_ = v___x_2133_;
v_isShared_2141_ = v_isSharedCheck_2225_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_hypotheses_2137_);
lean_inc(v_target_2136_);
lean_inc(v_typeAnalysis_2134_);
lean_inc(v_caches_2135_);
lean_dec(v___x_2133_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2225_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_interestingStructures_2142_; lean_object* v_interestingEnums_2143_; lean_object* v_interestingMatchers_2144_; lean_object* v_uninteresting_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2224_; 
v_interestingStructures_2142_ = lean_ctor_get(v_typeAnalysis_2134_, 0);
v_interestingEnums_2143_ = lean_ctor_get(v_typeAnalysis_2134_, 1);
v_interestingMatchers_2144_ = lean_ctor_get(v_typeAnalysis_2134_, 2);
v_uninteresting_2145_ = lean_ctor_get(v_typeAnalysis_2134_, 3);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_typeAnalysis_2134_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2147_ = v_typeAnalysis_2134_;
v_isShared_2148_ = v_isSharedCheck_2224_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_uninteresting_2145_);
lean_inc(v_interestingMatchers_2144_);
lean_inc(v_interestingEnums_2143_);
lean_inc(v_interestingStructures_2142_);
lean_dec(v_typeAnalysis_2134_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2224_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___y_2150_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___y_2164_; lean_object* v_i_2165_; lean_object* v___y_2171_; lean_object* v___y_2181_; lean_object* v_i_2182_; lean_object* v___x_2197_; 
v___x_2160_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2161_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2162_ = lean_box(0);
lean_inc(v_n_2120_);
v___x_2197_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2160_, v___x_2161_, v_interestingStructures_2142_, v_n_2120_);
switch(lean_obj_tag(v___x_2197_))
{
case 0:
{
lean_dec_ref_known(v___x_2197_, 3);
lean_dec(v_n_2120_);
v___y_2150_ = v_interestingStructures_2142_;
goto v___jp_2149_;
}
case 1:
{
lean_object* v_index_2198_; lean_object* v_size_2199_; lean_object* v_keyArray_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_index_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_index_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v_size_2199_ = lean_ctor_get(v_interestingStructures_2142_, 0);
v_keyArray_2200_ = lean_ctor_get(v_interestingStructures_2142_, 1);
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_add(v_size_2199_, v___x_2201_);
v___x_2203_ = lean_array_get_size(v_keyArray_2200_);
v___x_2204_ = lean_nat_dec_lt(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_dec(v___x_2202_);
lean_dec(v_index_2198_);
goto v___jp_2187_;
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2205_ = lean_unsigned_to_nat(4u);
v___x_2206_ = lean_nat_mul(v___x_2202_, v___x_2205_);
v___x_2207_ = lean_unsigned_to_nat(3u);
v___x_2208_ = lean_nat_mul(v___x_2203_, v___x_2207_);
v___x_2209_ = lean_nat_dec_le(v___x_2206_, v___x_2208_);
lean_dec(v___x_2208_);
lean_dec(v___x_2206_);
if (v___x_2209_ == 0)
{
lean_dec(v___x_2202_);
lean_dec(v_index_2198_);
goto v___jp_2187_;
}
else
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Std_DHashMap_Raw_setEntry___redArg(v_interestingStructures_2142_, v___x_2202_, v_index_2198_, v_n_2120_, v___x_2162_);
lean_dec(v_index_2198_);
v___y_2150_ = v___x_2210_;
goto v___jp_2149_;
}
}
}
default: 
{
lean_object* v_size_2211_; lean_object* v_keyArray_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v_size_2211_ = lean_ctor_get(v_interestingStructures_2142_, 0);
v_keyArray_2212_ = lean_ctor_get(v_interestingStructures_2142_, 1);
v___x_2213_ = lean_unsigned_to_nat(1u);
v___x_2214_ = lean_nat_add(v_size_2211_, v___x_2213_);
v___x_2215_ = lean_array_get_size(v_keyArray_2212_);
v___x_2216_ = lean_nat_dec_lt(v___x_2214_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; 
lean_dec(v___x_2214_);
v___x_2217_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2160_, v___x_2161_, v_interestingStructures_2142_);
v___y_2171_ = v___x_2217_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2218_ = lean_unsigned_to_nat(4u);
v___x_2219_ = lean_nat_mul(v___x_2214_, v___x_2218_);
lean_dec(v___x_2214_);
v___x_2220_ = lean_unsigned_to_nat(3u);
v___x_2221_ = lean_nat_mul(v___x_2215_, v___x_2220_);
v___x_2222_ = lean_nat_dec_le(v___x_2219_, v___x_2221_);
lean_dec(v___x_2221_);
lean_dec(v___x_2219_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2160_, v___x_2161_, v_interestingStructures_2142_);
v___y_2171_ = v___x_2223_;
goto v___jp_2170_;
}
else
{
v___y_2171_ = v_interestingStructures_2142_;
goto v___jp_2170_;
}
}
}
}
v___jp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___y_2150_);
v___x_2152_ = v___x_2147_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___y_2150_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_interestingEnums_2143_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_interestingMatchers_2144_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_uninteresting_2145_);
v___x_2152_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 1, v___x_2152_);
v___x_2154_ = v___x_2140_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_caches_2135_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_target_2136_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v_hypotheses_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*4, v_didChange_2138_);
v___x_2154_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_st_ref_put(v_a_2122_, v___x_2154_);
v___x_2156_ = lean_box(0);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
}
v___jp_2163_:
{
lean_object* v_size_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_size_2166_ = lean_ctor_get(v___y_2164_, 0);
v___x_2167_ = lean_unsigned_to_nat(1u);
v___x_2168_ = lean_nat_add(v_size_2166_, v___x_2167_);
v___x_2169_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2164_, v___x_2168_, v_i_2165_, v_n_2120_, v___x_2162_);
lean_dec(v_i_2165_);
v___y_2150_ = v___x_2169_;
goto v___jp_2149_;
}
v___jp_2170_:
{
lean_object* v___x_2172_; 
lean_inc(v_n_2120_);
v___x_2172_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2160_, v___x_2161_, v___y_2171_, v_n_2120_);
switch(lean_obj_tag(v___x_2172_))
{
case 0:
{
lean_object* v_index_2173_; lean_object* v_size_2174_; lean_object* v___x_2175_; 
v_index_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_index_2173_);
lean_dec_ref_known(v___x_2172_, 3);
v_size_2174_ = lean_ctor_get(v___y_2171_, 0);
lean_inc(v_size_2174_);
v___x_2175_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2171_, v_size_2174_, v_index_2173_, v_n_2120_, v___x_2162_);
lean_dec(v_index_2173_);
v___y_2150_ = v___x_2175_;
goto v___jp_2149_;
}
case 1:
{
lean_object* v_index_2176_; 
v_index_2176_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_index_2176_);
lean_dec_ref_known(v___x_2172_, 1);
v___y_2164_ = v___y_2171_;
v_i_2165_ = v_index_2176_;
goto v___jp_2163_;
}
default: 
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2171_, v___x_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_index_2179_; 
v_index_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_index_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___y_2164_ = v___y_2171_;
v_i_2165_ = v_index_2179_;
goto v___jp_2163_;
}
else
{
lean_dec(v_n_2120_);
v___y_2150_ = v___y_2171_;
goto v___jp_2149_;
}
}
}
}
v___jp_2180_:
{
lean_object* v_size_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_size_2183_ = lean_ctor_get(v___y_2181_, 0);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_add(v_size_2183_, v___x_2184_);
v___x_2186_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2181_, v___x_2185_, v_i_2182_, v_n_2120_, v___x_2162_);
lean_dec(v_i_2182_);
v___y_2150_ = v___x_2186_;
goto v___jp_2149_;
}
v___jp_2187_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2160_, v___x_2161_, v_interestingStructures_2142_);
lean_inc(v_n_2120_);
v___x_2189_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2160_, v___x_2161_, v___x_2188_, v_n_2120_);
switch(lean_obj_tag(v___x_2189_))
{
case 0:
{
lean_object* v_index_2190_; lean_object* v_size_2191_; lean_object* v___x_2192_; 
v_index_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_index_2190_);
lean_dec_ref_known(v___x_2189_, 3);
v_size_2191_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_size_2191_);
v___x_2192_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2188_, v_size_2191_, v_index_2190_, v_n_2120_, v___x_2162_);
lean_dec(v_index_2190_);
v___y_2150_ = v___x_2192_;
goto v___jp_2149_;
}
case 1:
{
lean_object* v_index_2193_; 
v_index_2193_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_index_2193_);
lean_dec_ref_known(v___x_2189_, 1);
v___y_2181_ = v___x_2188_;
v_i_2182_ = v_index_2193_;
goto v___jp_2180_;
}
default: 
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2188_, v___x_2194_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_index_2196_; 
v_index_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_index_2196_);
lean_dec_ref_known(v___x_2195_, 1);
v___y_2181_ = v___x_2188_;
v_i_2182_ = v_index_2196_;
goto v___jp_2180_;
}
else
{
lean_dec(v_n_2120_);
v___y_2150_ = v___x_2188_;
goto v___jp_2149_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v_typeAnalysis_2244_; lean_object* v_caches_2245_; lean_object* v_target_2246_; lean_object* v_hypotheses_2247_; uint8_t v_didChange_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2335_; 
v___x_2243_ = lean_st_ref_take(v_a_2241_);
v_typeAnalysis_2244_ = lean_ctor_get(v___x_2243_, 1);
v_caches_2245_ = lean_ctor_get(v___x_2243_, 0);
v_target_2246_ = lean_ctor_get(v___x_2243_, 2);
v_hypotheses_2247_ = lean_ctor_get(v___x_2243_, 3);
v_didChange_2248_ = lean_ctor_get_uint8(v___x_2243_, sizeof(void*)*4);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2250_ = v___x_2243_;
v_isShared_2251_ = v_isSharedCheck_2335_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_hypotheses_2247_);
lean_inc(v_target_2246_);
lean_inc(v_typeAnalysis_2244_);
lean_inc(v_caches_2245_);
lean_dec(v___x_2243_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2335_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_interestingStructures_2252_; lean_object* v_interestingEnums_2253_; lean_object* v_interestingMatchers_2254_; lean_object* v_uninteresting_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2334_; 
v_interestingStructures_2252_ = lean_ctor_get(v_typeAnalysis_2244_, 0);
v_interestingEnums_2253_ = lean_ctor_get(v_typeAnalysis_2244_, 1);
v_interestingMatchers_2254_ = lean_ctor_get(v_typeAnalysis_2244_, 2);
v_uninteresting_2255_ = lean_ctor_get(v_typeAnalysis_2244_, 3);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_typeAnalysis_2244_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2257_ = v_typeAnalysis_2244_;
v_isShared_2258_ = v_isSharedCheck_2334_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_uninteresting_2255_);
lean_inc(v_interestingMatchers_2254_);
lean_inc(v_interestingEnums_2253_);
lean_inc(v_interestingStructures_2252_);
lean_dec(v_typeAnalysis_2244_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2334_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___y_2260_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___y_2274_; lean_object* v_i_2275_; lean_object* v___y_2281_; lean_object* v___y_2291_; lean_object* v_i_2292_; lean_object* v___x_2307_; 
v___x_2270_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2271_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2272_ = lean_box(0);
lean_inc(v_n_2240_);
v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2270_, v___x_2271_, v_interestingEnums_2253_, v_n_2240_);
switch(lean_obj_tag(v___x_2307_))
{
case 0:
{
lean_dec_ref_known(v___x_2307_, 3);
lean_dec(v_n_2240_);
v___y_2260_ = v_interestingEnums_2253_;
goto v___jp_2259_;
}
case 1:
{
lean_object* v_index_2308_; lean_object* v_size_2309_; lean_object* v_keyArray_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_index_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_index_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v_size_2309_ = lean_ctor_get(v_interestingEnums_2253_, 0);
v_keyArray_2310_ = lean_ctor_get(v_interestingEnums_2253_, 1);
v___x_2311_ = lean_unsigned_to_nat(1u);
v___x_2312_ = lean_nat_add(v_size_2309_, v___x_2311_);
v___x_2313_ = lean_array_get_size(v_keyArray_2310_);
v___x_2314_ = lean_nat_dec_lt(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec(v___x_2312_);
lean_dec(v_index_2308_);
goto v___jp_2297_;
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2315_ = lean_unsigned_to_nat(4u);
v___x_2316_ = lean_nat_mul(v___x_2312_, v___x_2315_);
v___x_2317_ = lean_unsigned_to_nat(3u);
v___x_2318_ = lean_nat_mul(v___x_2313_, v___x_2317_);
v___x_2319_ = lean_nat_dec_le(v___x_2316_, v___x_2318_);
lean_dec(v___x_2318_);
lean_dec(v___x_2316_);
if (v___x_2319_ == 0)
{
lean_dec(v___x_2312_);
lean_dec(v_index_2308_);
goto v___jp_2297_;
}
else
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Std_DHashMap_Raw_setEntry___redArg(v_interestingEnums_2253_, v___x_2312_, v_index_2308_, v_n_2240_, v___x_2272_);
lean_dec(v_index_2308_);
v___y_2260_ = v___x_2320_;
goto v___jp_2259_;
}
}
}
default: 
{
lean_object* v_size_2321_; lean_object* v_keyArray_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_size_2321_ = lean_ctor_get(v_interestingEnums_2253_, 0);
v_keyArray_2322_ = lean_ctor_get(v_interestingEnums_2253_, 1);
v___x_2323_ = lean_unsigned_to_nat(1u);
v___x_2324_ = lean_nat_add(v_size_2321_, v___x_2323_);
v___x_2325_ = lean_array_get_size(v_keyArray_2322_);
v___x_2326_ = lean_nat_dec_lt(v___x_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_dec(v___x_2324_);
v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2270_, v___x_2271_, v_interestingEnums_2253_);
v___y_2281_ = v___x_2327_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2328_ = lean_unsigned_to_nat(4u);
v___x_2329_ = lean_nat_mul(v___x_2324_, v___x_2328_);
lean_dec(v___x_2324_);
v___x_2330_ = lean_unsigned_to_nat(3u);
v___x_2331_ = lean_nat_mul(v___x_2325_, v___x_2330_);
v___x_2332_ = lean_nat_dec_le(v___x_2329_, v___x_2331_);
lean_dec(v___x_2331_);
lean_dec(v___x_2329_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2270_, v___x_2271_, v_interestingEnums_2253_);
v___y_2281_ = v___x_2333_;
goto v___jp_2280_;
}
else
{
v___y_2281_ = v_interestingEnums_2253_;
goto v___jp_2280_;
}
}
}
}
v___jp_2259_:
{
lean_object* v___x_2262_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 1, v___y_2260_);
v___x_2262_ = v___x_2257_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_interestingStructures_2252_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v___y_2260_);
lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_interestingMatchers_2254_);
lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_uninteresting_2255_);
v___x_2262_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2264_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v___x_2262_);
v___x_2264_ = v___x_2250_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_caches_2245_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v_target_2246_);
lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_hypotheses_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2268_, sizeof(void*)*4, v_didChange_2248_);
v___x_2264_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = lean_st_ref_put(v_a_2241_, v___x_2264_);
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
}
v___jp_2273_:
{
lean_object* v_size_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_size_2276_ = lean_ctor_get(v___y_2274_, 0);
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = lean_nat_add(v_size_2276_, v___x_2277_);
v___x_2279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2274_, v___x_2278_, v_i_2275_, v_n_2240_, v___x_2272_);
lean_dec(v_i_2275_);
v___y_2260_ = v___x_2279_;
goto v___jp_2259_;
}
v___jp_2280_:
{
lean_object* v___x_2282_; 
lean_inc(v_n_2240_);
v___x_2282_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2270_, v___x_2271_, v___y_2281_, v_n_2240_);
switch(lean_obj_tag(v___x_2282_))
{
case 0:
{
lean_object* v_index_2283_; lean_object* v_size_2284_; lean_object* v___x_2285_; 
v_index_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_index_2283_);
lean_dec_ref_known(v___x_2282_, 3);
v_size_2284_ = lean_ctor_get(v___y_2281_, 0);
lean_inc(v_size_2284_);
v___x_2285_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2281_, v_size_2284_, v_index_2283_, v_n_2240_, v___x_2272_);
lean_dec(v_index_2283_);
v___y_2260_ = v___x_2285_;
goto v___jp_2259_;
}
case 1:
{
lean_object* v_index_2286_; 
v_index_2286_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_index_2286_);
lean_dec_ref_known(v___x_2282_, 1);
v___y_2274_ = v___y_2281_;
v_i_2275_ = v_index_2286_;
goto v___jp_2273_;
}
default: 
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_unsigned_to_nat(0u);
v___x_2288_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2281_, v___x_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_index_2289_; 
v_index_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_index_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v___y_2274_ = v___y_2281_;
v_i_2275_ = v_index_2289_;
goto v___jp_2273_;
}
else
{
lean_dec(v_n_2240_);
v___y_2260_ = v___y_2281_;
goto v___jp_2259_;
}
}
}
}
v___jp_2290_:
{
lean_object* v_size_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_size_2293_ = lean_ctor_get(v___y_2291_, 0);
v___x_2294_ = lean_unsigned_to_nat(1u);
v___x_2295_ = lean_nat_add(v_size_2293_, v___x_2294_);
v___x_2296_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2291_, v___x_2295_, v_i_2292_, v_n_2240_, v___x_2272_);
lean_dec(v_i_2292_);
v___y_2260_ = v___x_2296_;
goto v___jp_2259_;
}
v___jp_2297_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2270_, v___x_2271_, v_interestingEnums_2253_);
lean_inc(v_n_2240_);
v___x_2299_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2270_, v___x_2271_, v___x_2298_, v_n_2240_);
switch(lean_obj_tag(v___x_2299_))
{
case 0:
{
lean_object* v_index_2300_; lean_object* v_size_2301_; lean_object* v___x_2302_; 
v_index_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_index_2300_);
lean_dec_ref_known(v___x_2299_, 3);
v_size_2301_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_size_2301_);
v___x_2302_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2298_, v_size_2301_, v_index_2300_, v_n_2240_, v___x_2272_);
lean_dec(v_index_2300_);
v___y_2260_ = v___x_2302_;
goto v___jp_2259_;
}
case 1:
{
lean_object* v_index_2303_; 
v_index_2303_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_index_2303_);
lean_dec_ref_known(v___x_2299_, 1);
v___y_2291_ = v___x_2298_;
v_i_2292_ = v_index_2303_;
goto v___jp_2290_;
}
default: 
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2298_, v___x_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_index_2306_; 
v_index_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_index_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___y_2291_ = v___x_2298_;
v_i_2292_ = v_index_2306_;
goto v___jp_2290_;
}
else
{
lean_dec(v_n_2240_);
v___y_2260_ = v___x_2298_;
goto v___jp_2259_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_2336_, v_a_2337_);
lean_dec(v_a_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v_typeAnalysis_2354_; lean_object* v_caches_2355_; lean_object* v_target_2356_; lean_object* v_hypotheses_2357_; uint8_t v_didChange_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2445_; 
v___x_2353_ = lean_st_ref_take(v_a_2342_);
v_typeAnalysis_2354_ = lean_ctor_get(v___x_2353_, 1);
v_caches_2355_ = lean_ctor_get(v___x_2353_, 0);
v_target_2356_ = lean_ctor_get(v___x_2353_, 2);
v_hypotheses_2357_ = lean_ctor_get(v___x_2353_, 3);
v_didChange_2358_ = lean_ctor_get_uint8(v___x_2353_, sizeof(void*)*4);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2360_ = v___x_2353_;
v_isShared_2361_ = v_isSharedCheck_2445_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_hypotheses_2357_);
lean_inc(v_target_2356_);
lean_inc(v_typeAnalysis_2354_);
lean_inc(v_caches_2355_);
lean_dec(v___x_2353_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2445_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_interestingStructures_2362_; lean_object* v_interestingEnums_2363_; lean_object* v_interestingMatchers_2364_; lean_object* v_uninteresting_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2444_; 
v_interestingStructures_2362_ = lean_ctor_get(v_typeAnalysis_2354_, 0);
v_interestingEnums_2363_ = lean_ctor_get(v_typeAnalysis_2354_, 1);
v_interestingMatchers_2364_ = lean_ctor_get(v_typeAnalysis_2354_, 2);
v_uninteresting_2365_ = lean_ctor_get(v_typeAnalysis_2354_, 3);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_typeAnalysis_2354_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2367_ = v_typeAnalysis_2354_;
v_isShared_2368_ = v_isSharedCheck_2444_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_uninteresting_2365_);
lean_inc(v_interestingMatchers_2364_);
lean_inc(v_interestingEnums_2363_);
lean_inc(v_interestingStructures_2362_);
lean_dec(v_typeAnalysis_2354_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2444_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___y_2370_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___y_2384_; lean_object* v_i_2385_; lean_object* v___y_2391_; lean_object* v___y_2401_; lean_object* v_i_2402_; lean_object* v___x_2417_; 
v___x_2380_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2381_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2382_ = lean_box(0);
lean_inc(v_n_2340_);
v___x_2417_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2380_, v___x_2381_, v_interestingEnums_2363_, v_n_2340_);
switch(lean_obj_tag(v___x_2417_))
{
case 0:
{
lean_dec_ref_known(v___x_2417_, 3);
lean_dec(v_n_2340_);
v___y_2370_ = v_interestingEnums_2363_;
goto v___jp_2369_;
}
case 1:
{
lean_object* v_index_2418_; lean_object* v_size_2419_; lean_object* v_keyArray_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_index_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_index_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v_size_2419_ = lean_ctor_get(v_interestingEnums_2363_, 0);
v_keyArray_2420_ = lean_ctor_get(v_interestingEnums_2363_, 1);
v___x_2421_ = lean_unsigned_to_nat(1u);
v___x_2422_ = lean_nat_add(v_size_2419_, v___x_2421_);
v___x_2423_ = lean_array_get_size(v_keyArray_2420_);
v___x_2424_ = lean_nat_dec_lt(v___x_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_dec(v___x_2422_);
lean_dec(v_index_2418_);
goto v___jp_2407_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2425_ = lean_unsigned_to_nat(4u);
v___x_2426_ = lean_nat_mul(v___x_2422_, v___x_2425_);
v___x_2427_ = lean_unsigned_to_nat(3u);
v___x_2428_ = lean_nat_mul(v___x_2423_, v___x_2427_);
v___x_2429_ = lean_nat_dec_le(v___x_2426_, v___x_2428_);
lean_dec(v___x_2428_);
lean_dec(v___x_2426_);
if (v___x_2429_ == 0)
{
lean_dec(v___x_2422_);
lean_dec(v_index_2418_);
goto v___jp_2407_;
}
else
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Std_DHashMap_Raw_setEntry___redArg(v_interestingEnums_2363_, v___x_2422_, v_index_2418_, v_n_2340_, v___x_2382_);
lean_dec(v_index_2418_);
v___y_2370_ = v___x_2430_;
goto v___jp_2369_;
}
}
}
default: 
{
lean_object* v_size_2431_; lean_object* v_keyArray_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v_size_2431_ = lean_ctor_get(v_interestingEnums_2363_, 0);
v_keyArray_2432_ = lean_ctor_get(v_interestingEnums_2363_, 1);
v___x_2433_ = lean_unsigned_to_nat(1u);
v___x_2434_ = lean_nat_add(v_size_2431_, v___x_2433_);
v___x_2435_ = lean_array_get_size(v_keyArray_2432_);
v___x_2436_ = lean_nat_dec_lt(v___x_2434_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
lean_dec(v___x_2434_);
v___x_2437_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2380_, v___x_2381_, v_interestingEnums_2363_);
v___y_2391_ = v___x_2437_;
goto v___jp_2390_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2438_ = lean_unsigned_to_nat(4u);
v___x_2439_ = lean_nat_mul(v___x_2434_, v___x_2438_);
lean_dec(v___x_2434_);
v___x_2440_ = lean_unsigned_to_nat(3u);
v___x_2441_ = lean_nat_mul(v___x_2435_, v___x_2440_);
v___x_2442_ = lean_nat_dec_le(v___x_2439_, v___x_2441_);
lean_dec(v___x_2441_);
lean_dec(v___x_2439_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2380_, v___x_2381_, v_interestingEnums_2363_);
v___y_2391_ = v___x_2443_;
goto v___jp_2390_;
}
else
{
v___y_2391_ = v_interestingEnums_2363_;
goto v___jp_2390_;
}
}
}
}
v___jp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 1, v___y_2370_);
v___x_2372_ = v___x_2367_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_interestingStructures_2362_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___y_2370_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_interestingMatchers_2364_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v_uninteresting_2365_);
v___x_2372_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v___x_2372_);
v___x_2374_ = v___x_2360_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_caches_2355_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2378_, 2, v_target_2356_);
lean_ctor_set(v_reuseFailAlloc_2378_, 3, v_hypotheses_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*4, v_didChange_2358_);
v___x_2374_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_st_ref_put(v_a_2342_, v___x_2374_);
v___x_2376_ = lean_box(0);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
}
}
v___jp_2383_:
{
lean_object* v_size_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_size_2386_ = lean_ctor_get(v___y_2384_, 0);
v___x_2387_ = lean_unsigned_to_nat(1u);
v___x_2388_ = lean_nat_add(v_size_2386_, v___x_2387_);
v___x_2389_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2384_, v___x_2388_, v_i_2385_, v_n_2340_, v___x_2382_);
lean_dec(v_i_2385_);
v___y_2370_ = v___x_2389_;
goto v___jp_2369_;
}
v___jp_2390_:
{
lean_object* v___x_2392_; 
lean_inc(v_n_2340_);
v___x_2392_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2380_, v___x_2381_, v___y_2391_, v_n_2340_);
switch(lean_obj_tag(v___x_2392_))
{
case 0:
{
lean_object* v_index_2393_; lean_object* v_size_2394_; lean_object* v___x_2395_; 
v_index_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_index_2393_);
lean_dec_ref_known(v___x_2392_, 3);
v_size_2394_ = lean_ctor_get(v___y_2391_, 0);
lean_inc(v_size_2394_);
v___x_2395_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2391_, v_size_2394_, v_index_2393_, v_n_2340_, v___x_2382_);
lean_dec(v_index_2393_);
v___y_2370_ = v___x_2395_;
goto v___jp_2369_;
}
case 1:
{
lean_object* v_index_2396_; 
v_index_2396_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_index_2396_);
lean_dec_ref_known(v___x_2392_, 1);
v___y_2384_ = v___y_2391_;
v_i_2385_ = v_index_2396_;
goto v___jp_2383_;
}
default: 
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(0u);
v___x_2398_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2391_, v___x_2397_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_index_2399_; 
v_index_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_index_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___y_2384_ = v___y_2391_;
v_i_2385_ = v_index_2399_;
goto v___jp_2383_;
}
else
{
lean_dec(v_n_2340_);
v___y_2370_ = v___y_2391_;
goto v___jp_2369_;
}
}
}
}
v___jp_2400_:
{
lean_object* v_size_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_size_2403_ = lean_ctor_get(v___y_2401_, 0);
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = lean_nat_add(v_size_2403_, v___x_2404_);
v___x_2406_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2401_, v___x_2405_, v_i_2402_, v_n_2340_, v___x_2382_);
lean_dec(v_i_2402_);
v___y_2370_ = v___x_2406_;
goto v___jp_2369_;
}
v___jp_2407_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2380_, v___x_2381_, v_interestingEnums_2363_);
lean_inc(v_n_2340_);
v___x_2409_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2380_, v___x_2381_, v___x_2408_, v_n_2340_);
switch(lean_obj_tag(v___x_2409_))
{
case 0:
{
lean_object* v_index_2410_; lean_object* v_size_2411_; lean_object* v___x_2412_; 
v_index_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_index_2410_);
lean_dec_ref_known(v___x_2409_, 3);
v_size_2411_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_size_2411_);
v___x_2412_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2408_, v_size_2411_, v_index_2410_, v_n_2340_, v___x_2382_);
lean_dec(v_index_2410_);
v___y_2370_ = v___x_2412_;
goto v___jp_2369_;
}
case 1:
{
lean_object* v_index_2413_; 
v_index_2413_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_index_2413_);
lean_dec_ref_known(v___x_2409_, 1);
v___y_2401_ = v___x_2408_;
v_i_2402_ = v_index_2413_;
goto v___jp_2400_;
}
default: 
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2408_, v___x_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_index_2416_; 
v_index_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_index_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___y_2401_ = v___x_2408_;
v_i_2402_ = v_index_2416_;
goto v___jp_2400_;
}
else
{
lean_dec(v_n_2340_);
v___y_2370_ = v___x_2408_;
goto v___jp_2369_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_2460_, lean_object* v_k_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; lean_object* v_typeAnalysis_2465_; lean_object* v_caches_2466_; lean_object* v_target_2467_; lean_object* v_hypotheses_2468_; uint8_t v_didChange_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2558_; 
v___x_2464_ = lean_st_ref_take(v_a_2462_);
v_typeAnalysis_2465_ = lean_ctor_get(v___x_2464_, 1);
v_caches_2466_ = lean_ctor_get(v___x_2464_, 0);
v_target_2467_ = lean_ctor_get(v___x_2464_, 2);
v_hypotheses_2468_ = lean_ctor_get(v___x_2464_, 3);
v_didChange_2469_ = lean_ctor_get_uint8(v___x_2464_, sizeof(void*)*4);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2471_ = v___x_2464_;
v_isShared_2472_ = v_isSharedCheck_2558_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_hypotheses_2468_);
lean_inc(v_target_2467_);
lean_inc(v_typeAnalysis_2465_);
lean_inc(v_caches_2466_);
lean_dec(v___x_2464_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2558_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_interestingStructures_2473_; lean_object* v_interestingEnums_2474_; lean_object* v_interestingMatchers_2475_; lean_object* v_uninteresting_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2557_; 
v_interestingStructures_2473_ = lean_ctor_get(v_typeAnalysis_2465_, 0);
v_interestingEnums_2474_ = lean_ctor_get(v_typeAnalysis_2465_, 1);
v_interestingMatchers_2475_ = lean_ctor_get(v_typeAnalysis_2465_, 2);
v_uninteresting_2476_ = lean_ctor_get(v_typeAnalysis_2465_, 3);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_typeAnalysis_2465_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2478_ = v_typeAnalysis_2465_;
v_isShared_2479_ = v_isSharedCheck_2557_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_uninteresting_2476_);
lean_inc(v_interestingMatchers_2475_);
lean_inc(v_interestingEnums_2474_);
lean_inc(v_interestingStructures_2473_);
lean_dec(v_typeAnalysis_2465_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2557_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___y_2481_; lean_object* v___y_2492_; lean_object* v_i_2493_; lean_object* v___y_2499_; lean_object* v_i_2500_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___y_2508_; lean_object* v___x_2527_; 
v___x_2505_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2506_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_2460_);
v___x_2527_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2505_, v___x_2506_, v_interestingMatchers_2475_, v_n_2460_);
switch(lean_obj_tag(v___x_2527_))
{
case 0:
{
lean_object* v_index_2528_; lean_object* v_size_2529_; lean_object* v___x_2530_; 
v_index_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_index_2528_);
lean_dec_ref_known(v___x_2527_, 3);
v_size_2529_ = lean_ctor_get(v_interestingMatchers_2475_, 0);
lean_inc(v_size_2529_);
v___x_2530_ = l_Std_DHashMap_Raw_setEntry___redArg(v_interestingMatchers_2475_, v_size_2529_, v_index_2528_, v_n_2460_, v_k_2461_);
lean_dec(v_index_2528_);
v___y_2481_ = v___x_2530_;
goto v___jp_2480_;
}
case 1:
{
lean_object* v_index_2531_; lean_object* v_size_2532_; lean_object* v_keyArray_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v_index_2531_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_index_2531_);
lean_dec_ref_known(v___x_2527_, 1);
v_size_2532_ = lean_ctor_get(v_interestingMatchers_2475_, 0);
v_keyArray_2533_ = lean_ctor_get(v_interestingMatchers_2475_, 1);
v___x_2534_ = lean_unsigned_to_nat(1u);
v___x_2535_ = lean_nat_add(v_size_2532_, v___x_2534_);
v___x_2536_ = lean_array_get_size(v_keyArray_2533_);
v___x_2537_ = lean_nat_dec_lt(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_dec(v___x_2535_);
lean_dec(v_index_2531_);
goto v___jp_2517_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2538_ = lean_unsigned_to_nat(4u);
v___x_2539_ = lean_nat_mul(v___x_2535_, v___x_2538_);
v___x_2540_ = lean_unsigned_to_nat(3u);
v___x_2541_ = lean_nat_mul(v___x_2536_, v___x_2540_);
v___x_2542_ = lean_nat_dec_le(v___x_2539_, v___x_2541_);
lean_dec(v___x_2541_);
lean_dec(v___x_2539_);
if (v___x_2542_ == 0)
{
lean_dec(v___x_2535_);
lean_dec(v_index_2531_);
goto v___jp_2517_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Std_DHashMap_Raw_setEntry___redArg(v_interestingMatchers_2475_, v___x_2535_, v_index_2531_, v_n_2460_, v_k_2461_);
lean_dec(v_index_2531_);
v___y_2481_ = v___x_2543_;
goto v___jp_2480_;
}
}
}
default: 
{
lean_object* v_size_2544_; lean_object* v_keyArray_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_size_2544_ = lean_ctor_get(v_interestingMatchers_2475_, 0);
v_keyArray_2545_ = lean_ctor_get(v_interestingMatchers_2475_, 1);
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_add(v_size_2544_, v___x_2546_);
v___x_2548_ = lean_array_get_size(v_keyArray_2545_);
v___x_2549_ = lean_nat_dec_lt(v___x_2547_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; 
lean_dec(v___x_2547_);
v___x_2550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2505_, v___x_2506_, v_interestingMatchers_2475_);
v___y_2508_ = v___x_2550_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2551_ = lean_unsigned_to_nat(4u);
v___x_2552_ = lean_nat_mul(v___x_2547_, v___x_2551_);
lean_dec(v___x_2547_);
v___x_2553_ = lean_unsigned_to_nat(3u);
v___x_2554_ = lean_nat_mul(v___x_2548_, v___x_2553_);
v___x_2555_ = lean_nat_dec_le(v___x_2552_, v___x_2554_);
lean_dec(v___x_2554_);
lean_dec(v___x_2552_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2505_, v___x_2506_, v_interestingMatchers_2475_);
v___y_2508_ = v___x_2556_;
goto v___jp_2507_;
}
else
{
v___y_2508_ = v_interestingMatchers_2475_;
goto v___jp_2507_;
}
}
}
}
v___jp_2480_:
{
lean_object* v___x_2483_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 2, v___y_2481_);
v___x_2483_ = v___x_2478_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_interestingStructures_2473_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_interestingEnums_2474_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v___y_2481_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_uninteresting_2476_);
v___x_2483_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2485_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 1, v___x_2483_);
v___x_2485_ = v___x_2471_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_caches_2466_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_target_2467_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_hypotheses_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2489_, sizeof(void*)*4, v_didChange_2469_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_st_ref_put(v_a_2462_, v___x_2485_);
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
return v___x_2488_;
}
}
}
v___jp_2491_:
{
lean_object* v_size_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_size_2494_ = lean_ctor_get(v___y_2492_, 0);
v___x_2495_ = lean_unsigned_to_nat(1u);
v___x_2496_ = lean_nat_add(v_size_2494_, v___x_2495_);
v___x_2497_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2492_, v___x_2496_, v_i_2493_, v_n_2460_, v_k_2461_);
lean_dec(v_i_2493_);
v___y_2481_ = v___x_2497_;
goto v___jp_2480_;
}
v___jp_2498_:
{
lean_object* v_size_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_size_2501_ = lean_ctor_get(v___y_2499_, 0);
v___x_2502_ = lean_unsigned_to_nat(1u);
v___x_2503_ = lean_nat_add(v_size_2501_, v___x_2502_);
v___x_2504_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2499_, v___x_2503_, v_i_2500_, v_n_2460_, v_k_2461_);
lean_dec(v_i_2500_);
v___y_2481_ = v___x_2504_;
goto v___jp_2480_;
}
v___jp_2507_:
{
lean_object* v___x_2509_; 
lean_inc(v_n_2460_);
v___x_2509_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2505_, v___x_2506_, v___y_2508_, v_n_2460_);
switch(lean_obj_tag(v___x_2509_))
{
case 0:
{
lean_object* v_index_2510_; lean_object* v_size_2511_; lean_object* v___x_2512_; 
v_index_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_index_2510_);
lean_dec_ref_known(v___x_2509_, 3);
v_size_2511_ = lean_ctor_get(v___y_2508_, 0);
lean_inc(v_size_2511_);
v___x_2512_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2508_, v_size_2511_, v_index_2510_, v_n_2460_, v_k_2461_);
lean_dec(v_index_2510_);
v___y_2481_ = v___x_2512_;
goto v___jp_2480_;
}
case 1:
{
lean_object* v_index_2513_; 
v_index_2513_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_index_2513_);
lean_dec_ref_known(v___x_2509_, 1);
v___y_2492_ = v___y_2508_;
v_i_2493_ = v_index_2513_;
goto v___jp_2491_;
}
default: 
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2508_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_index_2516_; 
v_index_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_index_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___y_2492_ = v___y_2508_;
v_i_2493_ = v_index_2516_;
goto v___jp_2491_;
}
else
{
lean_dec_ref(v_k_2461_);
lean_dec(v_n_2460_);
v___y_2481_ = v___y_2508_;
goto v___jp_2480_;
}
}
}
}
v___jp_2517_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2505_, v___x_2506_, v_interestingMatchers_2475_);
lean_inc(v_n_2460_);
v___x_2519_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2505_, v___x_2506_, v___x_2518_, v_n_2460_);
switch(lean_obj_tag(v___x_2519_))
{
case 0:
{
lean_object* v_index_2520_; lean_object* v_size_2521_; lean_object* v___x_2522_; 
v_index_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_index_2520_);
lean_dec_ref_known(v___x_2519_, 3);
v_size_2521_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_size_2521_);
v___x_2522_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2518_, v_size_2521_, v_index_2520_, v_n_2460_, v_k_2461_);
lean_dec(v_index_2520_);
v___y_2481_ = v___x_2522_;
goto v___jp_2480_;
}
case 1:
{
lean_object* v_index_2523_; 
v_index_2523_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_index_2523_);
lean_dec_ref_known(v___x_2519_, 1);
v___y_2499_ = v___x_2518_;
v_i_2500_ = v_index_2523_;
goto v___jp_2498_;
}
default: 
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_unsigned_to_nat(0u);
v___x_2525_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2518_, v___x_2524_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_index_2526_; 
v_index_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_index_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___y_2499_ = v___x_2518_;
v_i_2500_ = v_index_2526_;
goto v___jp_2498_;
}
else
{
lean_dec_ref(v_k_2461_);
lean_dec(v_n_2460_);
v___y_2481_ = v___x_2518_;
goto v___jp_2480_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_2559_, lean_object* v_k_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_2559_, v_k_2560_, v_a_2561_);
lean_dec(v_a_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_2564_, lean_object* v_k_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v___x_2578_; lean_object* v_typeAnalysis_2579_; lean_object* v_caches_2580_; lean_object* v_target_2581_; lean_object* v_hypotheses_2582_; uint8_t v_didChange_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2672_; 
v___x_2578_ = lean_st_ref_take(v_a_2567_);
v_typeAnalysis_2579_ = lean_ctor_get(v___x_2578_, 1);
v_caches_2580_ = lean_ctor_get(v___x_2578_, 0);
v_target_2581_ = lean_ctor_get(v___x_2578_, 2);
v_hypotheses_2582_ = lean_ctor_get(v___x_2578_, 3);
v_didChange_2583_ = lean_ctor_get_uint8(v___x_2578_, sizeof(void*)*4);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2585_ = v___x_2578_;
v_isShared_2586_ = v_isSharedCheck_2672_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_hypotheses_2582_);
lean_inc(v_target_2581_);
lean_inc(v_typeAnalysis_2579_);
lean_inc(v_caches_2580_);
lean_dec(v___x_2578_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2672_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v_interestingStructures_2587_; lean_object* v_interestingEnums_2588_; lean_object* v_interestingMatchers_2589_; lean_object* v_uninteresting_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2671_; 
v_interestingStructures_2587_ = lean_ctor_get(v_typeAnalysis_2579_, 0);
v_interestingEnums_2588_ = lean_ctor_get(v_typeAnalysis_2579_, 1);
v_interestingMatchers_2589_ = lean_ctor_get(v_typeAnalysis_2579_, 2);
v_uninteresting_2590_ = lean_ctor_get(v_typeAnalysis_2579_, 3);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_typeAnalysis_2579_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2592_ = v_typeAnalysis_2579_;
v_isShared_2593_ = v_isSharedCheck_2671_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_uninteresting_2590_);
lean_inc(v_interestingMatchers_2589_);
lean_inc(v_interestingEnums_2588_);
lean_inc(v_interestingStructures_2587_);
lean_dec(v_typeAnalysis_2579_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2671_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___y_2595_; lean_object* v___y_2606_; lean_object* v_i_2607_; lean_object* v___y_2613_; lean_object* v_i_2614_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___y_2622_; lean_object* v___x_2641_; 
v___x_2619_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2620_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_2564_);
v___x_2641_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2619_, v___x_2620_, v_interestingMatchers_2589_, v_n_2564_);
switch(lean_obj_tag(v___x_2641_))
{
case 0:
{
lean_object* v_index_2642_; lean_object* v_size_2643_; lean_object* v___x_2644_; 
v_index_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_index_2642_);
lean_dec_ref_known(v___x_2641_, 3);
v_size_2643_ = lean_ctor_get(v_interestingMatchers_2589_, 0);
lean_inc(v_size_2643_);
v___x_2644_ = l_Std_DHashMap_Raw_setEntry___redArg(v_interestingMatchers_2589_, v_size_2643_, v_index_2642_, v_n_2564_, v_k_2565_);
lean_dec(v_index_2642_);
v___y_2595_ = v___x_2644_;
goto v___jp_2594_;
}
case 1:
{
lean_object* v_index_2645_; lean_object* v_size_2646_; lean_object* v_keyArray_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v_index_2645_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_index_2645_);
lean_dec_ref_known(v___x_2641_, 1);
v_size_2646_ = lean_ctor_get(v_interestingMatchers_2589_, 0);
v_keyArray_2647_ = lean_ctor_get(v_interestingMatchers_2589_, 1);
v___x_2648_ = lean_unsigned_to_nat(1u);
v___x_2649_ = lean_nat_add(v_size_2646_, v___x_2648_);
v___x_2650_ = lean_array_get_size(v_keyArray_2647_);
v___x_2651_ = lean_nat_dec_lt(v___x_2649_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_dec(v___x_2649_);
lean_dec(v_index_2645_);
goto v___jp_2631_;
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2652_ = lean_unsigned_to_nat(4u);
v___x_2653_ = lean_nat_mul(v___x_2649_, v___x_2652_);
v___x_2654_ = lean_unsigned_to_nat(3u);
v___x_2655_ = lean_nat_mul(v___x_2650_, v___x_2654_);
v___x_2656_ = lean_nat_dec_le(v___x_2653_, v___x_2655_);
lean_dec(v___x_2655_);
lean_dec(v___x_2653_);
if (v___x_2656_ == 0)
{
lean_dec(v___x_2649_);
lean_dec(v_index_2645_);
goto v___jp_2631_;
}
else
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Std_DHashMap_Raw_setEntry___redArg(v_interestingMatchers_2589_, v___x_2649_, v_index_2645_, v_n_2564_, v_k_2565_);
lean_dec(v_index_2645_);
v___y_2595_ = v___x_2657_;
goto v___jp_2594_;
}
}
}
default: 
{
lean_object* v_size_2658_; lean_object* v_keyArray_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v_size_2658_ = lean_ctor_get(v_interestingMatchers_2589_, 0);
v_keyArray_2659_ = lean_ctor_get(v_interestingMatchers_2589_, 1);
v___x_2660_ = lean_unsigned_to_nat(1u);
v___x_2661_ = lean_nat_add(v_size_2658_, v___x_2660_);
v___x_2662_ = lean_array_get_size(v_keyArray_2659_);
v___x_2663_ = lean_nat_dec_lt(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_dec(v___x_2661_);
v___x_2664_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2619_, v___x_2620_, v_interestingMatchers_2589_);
v___y_2622_ = v___x_2664_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2665_ = lean_unsigned_to_nat(4u);
v___x_2666_ = lean_nat_mul(v___x_2661_, v___x_2665_);
lean_dec(v___x_2661_);
v___x_2667_ = lean_unsigned_to_nat(3u);
v___x_2668_ = lean_nat_mul(v___x_2662_, v___x_2667_);
v___x_2669_ = lean_nat_dec_le(v___x_2666_, v___x_2668_);
lean_dec(v___x_2668_);
lean_dec(v___x_2666_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2619_, v___x_2620_, v_interestingMatchers_2589_);
v___y_2622_ = v___x_2670_;
goto v___jp_2621_;
}
else
{
v___y_2622_ = v_interestingMatchers_2589_;
goto v___jp_2621_;
}
}
}
}
v___jp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 2, v___y_2595_);
v___x_2597_ = v___x_2592_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_interestingStructures_2587_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_interestingEnums_2588_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v___y_2595_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_uninteresting_2590_);
v___x_2597_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2599_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 1, v___x_2597_);
v___x_2599_ = v___x_2585_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_caches_2580_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_target_2581_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_hypotheses_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2603_, sizeof(void*)*4, v_didChange_2583_);
v___x_2599_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = lean_st_ref_put(v_a_2567_, v___x_2599_);
v___x_2601_ = lean_box(0);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
}
}
v___jp_2605_:
{
lean_object* v_size_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v_size_2608_ = lean_ctor_get(v___y_2606_, 0);
v___x_2609_ = lean_unsigned_to_nat(1u);
v___x_2610_ = lean_nat_add(v_size_2608_, v___x_2609_);
v___x_2611_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2606_, v___x_2610_, v_i_2607_, v_n_2564_, v_k_2565_);
lean_dec(v_i_2607_);
v___y_2595_ = v___x_2611_;
goto v___jp_2594_;
}
v___jp_2612_:
{
lean_object* v_size_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_size_2615_ = lean_ctor_get(v___y_2613_, 0);
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_nat_add(v_size_2615_, v___x_2616_);
v___x_2618_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2613_, v___x_2617_, v_i_2614_, v_n_2564_, v_k_2565_);
lean_dec(v_i_2614_);
v___y_2595_ = v___x_2618_;
goto v___jp_2594_;
}
v___jp_2621_:
{
lean_object* v___x_2623_; 
lean_inc(v_n_2564_);
v___x_2623_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2619_, v___x_2620_, v___y_2622_, v_n_2564_);
switch(lean_obj_tag(v___x_2623_))
{
case 0:
{
lean_object* v_index_2624_; lean_object* v_size_2625_; lean_object* v___x_2626_; 
v_index_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_index_2624_);
lean_dec_ref_known(v___x_2623_, 3);
v_size_2625_ = lean_ctor_get(v___y_2622_, 0);
lean_inc(v_size_2625_);
v___x_2626_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2622_, v_size_2625_, v_index_2624_, v_n_2564_, v_k_2565_);
lean_dec(v_index_2624_);
v___y_2595_ = v___x_2626_;
goto v___jp_2594_;
}
case 1:
{
lean_object* v_index_2627_; 
v_index_2627_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_index_2627_);
lean_dec_ref_known(v___x_2623_, 1);
v___y_2606_ = v___y_2622_;
v_i_2607_ = v_index_2627_;
goto v___jp_2605_;
}
default: 
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2622_, v___x_2628_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_index_2630_; 
v_index_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_index_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___y_2606_ = v___y_2622_;
v_i_2607_ = v_index_2630_;
goto v___jp_2605_;
}
else
{
lean_dec_ref(v_k_2565_);
lean_dec(v_n_2564_);
v___y_2595_ = v___y_2622_;
goto v___jp_2594_;
}
}
}
}
v___jp_2631_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2619_, v___x_2620_, v_interestingMatchers_2589_);
lean_inc(v_n_2564_);
v___x_2633_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2619_, v___x_2620_, v___x_2632_, v_n_2564_);
switch(lean_obj_tag(v___x_2633_))
{
case 0:
{
lean_object* v_index_2634_; lean_object* v_size_2635_; lean_object* v___x_2636_; 
v_index_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_index_2634_);
lean_dec_ref_known(v___x_2633_, 3);
v_size_2635_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_size_2635_);
v___x_2636_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2632_, v_size_2635_, v_index_2634_, v_n_2564_, v_k_2565_);
lean_dec(v_index_2634_);
v___y_2595_ = v___x_2636_;
goto v___jp_2594_;
}
case 1:
{
lean_object* v_index_2637_; 
v_index_2637_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_index_2637_);
lean_dec_ref_known(v___x_2633_, 1);
v___y_2613_ = v___x_2632_;
v_i_2614_ = v_index_2637_;
goto v___jp_2612_;
}
default: 
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2632_, v___x_2638_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_index_2640_; 
v_index_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_index_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v___y_2613_ = v___x_2632_;
v_i_2614_ = v_index_2640_;
goto v___jp_2612_;
}
else
{
lean_dec_ref(v_k_2565_);
lean_dec(v_n_2564_);
v___y_2595_ = v___x_2632_;
goto v___jp_2594_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_2673_, lean_object* v_k_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_2673_, v_k_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v___x_2691_; lean_object* v_typeAnalysis_2692_; lean_object* v_caches_2693_; lean_object* v_target_2694_; lean_object* v_hypotheses_2695_; uint8_t v_didChange_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2783_; 
v___x_2691_ = lean_st_ref_take(v_a_2689_);
v_typeAnalysis_2692_ = lean_ctor_get(v___x_2691_, 1);
v_caches_2693_ = lean_ctor_get(v___x_2691_, 0);
v_target_2694_ = lean_ctor_get(v___x_2691_, 2);
v_hypotheses_2695_ = lean_ctor_get(v___x_2691_, 3);
v_didChange_2696_ = lean_ctor_get_uint8(v___x_2691_, sizeof(void*)*4);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2698_ = v___x_2691_;
v_isShared_2699_ = v_isSharedCheck_2783_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_hypotheses_2695_);
lean_inc(v_target_2694_);
lean_inc(v_typeAnalysis_2692_);
lean_inc(v_caches_2693_);
lean_dec(v___x_2691_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2783_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v_interestingStructures_2700_; lean_object* v_interestingEnums_2701_; lean_object* v_interestingMatchers_2702_; lean_object* v_uninteresting_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2782_; 
v_interestingStructures_2700_ = lean_ctor_get(v_typeAnalysis_2692_, 0);
v_interestingEnums_2701_ = lean_ctor_get(v_typeAnalysis_2692_, 1);
v_interestingMatchers_2702_ = lean_ctor_get(v_typeAnalysis_2692_, 2);
v_uninteresting_2703_ = lean_ctor_get(v_typeAnalysis_2692_, 3);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_typeAnalysis_2692_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2705_ = v_typeAnalysis_2692_;
v_isShared_2706_ = v_isSharedCheck_2782_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_uninteresting_2703_);
lean_inc(v_interestingMatchers_2702_);
lean_inc(v_interestingEnums_2701_);
lean_inc(v_interestingStructures_2700_);
lean_dec(v_typeAnalysis_2692_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2782_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___y_2708_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___y_2722_; lean_object* v_i_2723_; lean_object* v___y_2729_; lean_object* v___y_2739_; lean_object* v_i_2740_; lean_object* v___x_2755_; 
v___x_2718_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2719_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2720_ = lean_box(0);
lean_inc(v_n_2688_);
v___x_2755_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2718_, v___x_2719_, v_uninteresting_2703_, v_n_2688_);
switch(lean_obj_tag(v___x_2755_))
{
case 0:
{
lean_dec_ref_known(v___x_2755_, 3);
lean_dec(v_n_2688_);
v___y_2708_ = v_uninteresting_2703_;
goto v___jp_2707_;
}
case 1:
{
lean_object* v_index_2756_; lean_object* v_size_2757_; lean_object* v_keyArray_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v_index_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_index_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v_size_2757_ = lean_ctor_get(v_uninteresting_2703_, 0);
v_keyArray_2758_ = lean_ctor_get(v_uninteresting_2703_, 1);
v___x_2759_ = lean_unsigned_to_nat(1u);
v___x_2760_ = lean_nat_add(v_size_2757_, v___x_2759_);
v___x_2761_ = lean_array_get_size(v_keyArray_2758_);
v___x_2762_ = lean_nat_dec_lt(v___x_2760_, v___x_2761_);
if (v___x_2762_ == 0)
{
lean_dec(v___x_2760_);
lean_dec(v_index_2756_);
goto v___jp_2745_;
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2763_ = lean_unsigned_to_nat(4u);
v___x_2764_ = lean_nat_mul(v___x_2760_, v___x_2763_);
v___x_2765_ = lean_unsigned_to_nat(3u);
v___x_2766_ = lean_nat_mul(v___x_2761_, v___x_2765_);
v___x_2767_ = lean_nat_dec_le(v___x_2764_, v___x_2766_);
lean_dec(v___x_2766_);
lean_dec(v___x_2764_);
if (v___x_2767_ == 0)
{
lean_dec(v___x_2760_);
lean_dec(v_index_2756_);
goto v___jp_2745_;
}
else
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Std_DHashMap_Raw_setEntry___redArg(v_uninteresting_2703_, v___x_2760_, v_index_2756_, v_n_2688_, v___x_2720_);
lean_dec(v_index_2756_);
v___y_2708_ = v___x_2768_;
goto v___jp_2707_;
}
}
}
default: 
{
lean_object* v_size_2769_; lean_object* v_keyArray_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v_size_2769_ = lean_ctor_get(v_uninteresting_2703_, 0);
v_keyArray_2770_ = lean_ctor_get(v_uninteresting_2703_, 1);
v___x_2771_ = lean_unsigned_to_nat(1u);
v___x_2772_ = lean_nat_add(v_size_2769_, v___x_2771_);
v___x_2773_ = lean_array_get_size(v_keyArray_2770_);
v___x_2774_ = lean_nat_dec_lt(v___x_2772_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; 
lean_dec(v___x_2772_);
v___x_2775_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2718_, v___x_2719_, v_uninteresting_2703_);
v___y_2729_ = v___x_2775_;
goto v___jp_2728_;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2776_ = lean_unsigned_to_nat(4u);
v___x_2777_ = lean_nat_mul(v___x_2772_, v___x_2776_);
lean_dec(v___x_2772_);
v___x_2778_ = lean_unsigned_to_nat(3u);
v___x_2779_ = lean_nat_mul(v___x_2773_, v___x_2778_);
v___x_2780_ = lean_nat_dec_le(v___x_2777_, v___x_2779_);
lean_dec(v___x_2779_);
lean_dec(v___x_2777_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2718_, v___x_2719_, v_uninteresting_2703_);
v___y_2729_ = v___x_2781_;
goto v___jp_2728_;
}
else
{
v___y_2729_ = v_uninteresting_2703_;
goto v___jp_2728_;
}
}
}
}
v___jp_2707_:
{
lean_object* v___x_2710_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 3, v___y_2708_);
v___x_2710_ = v___x_2705_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_interestingStructures_2700_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_interestingEnums_2701_);
lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_interestingMatchers_2702_);
lean_ctor_set(v_reuseFailAlloc_2717_, 3, v___y_2708_);
v___x_2710_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2712_; 
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v___x_2710_);
v___x_2712_ = v___x_2698_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_caches_2693_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v_target_2694_);
lean_ctor_set(v_reuseFailAlloc_2716_, 3, v_hypotheses_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, sizeof(void*)*4, v_didChange_2696_);
v___x_2712_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_st_ref_put(v_a_2689_, v___x_2712_);
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
}
}
v___jp_2721_:
{
lean_object* v_size_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v_size_2724_ = lean_ctor_get(v___y_2722_, 0);
v___x_2725_ = lean_unsigned_to_nat(1u);
v___x_2726_ = lean_nat_add(v_size_2724_, v___x_2725_);
v___x_2727_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2722_, v___x_2726_, v_i_2723_, v_n_2688_, v___x_2720_);
lean_dec(v_i_2723_);
v___y_2708_ = v___x_2727_;
goto v___jp_2707_;
}
v___jp_2728_:
{
lean_object* v___x_2730_; 
lean_inc(v_n_2688_);
v___x_2730_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2718_, v___x_2719_, v___y_2729_, v_n_2688_);
switch(lean_obj_tag(v___x_2730_))
{
case 0:
{
lean_object* v_index_2731_; lean_object* v_size_2732_; lean_object* v___x_2733_; 
v_index_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_index_2731_);
lean_dec_ref_known(v___x_2730_, 3);
v_size_2732_ = lean_ctor_get(v___y_2729_, 0);
lean_inc(v_size_2732_);
v___x_2733_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2729_, v_size_2732_, v_index_2731_, v_n_2688_, v___x_2720_);
lean_dec(v_index_2731_);
v___y_2708_ = v___x_2733_;
goto v___jp_2707_;
}
case 1:
{
lean_object* v_index_2734_; 
v_index_2734_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_index_2734_);
lean_dec_ref_known(v___x_2730_, 1);
v___y_2722_ = v___y_2729_;
v_i_2723_ = v_index_2734_;
goto v___jp_2721_;
}
default: 
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2729_, v___x_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_index_2737_; 
v_index_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_index_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___y_2722_ = v___y_2729_;
v_i_2723_ = v_index_2737_;
goto v___jp_2721_;
}
else
{
lean_dec(v_n_2688_);
v___y_2708_ = v___y_2729_;
goto v___jp_2707_;
}
}
}
}
v___jp_2738_:
{
lean_object* v_size_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v_size_2741_ = lean_ctor_get(v___y_2739_, 0);
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_nat_add(v_size_2741_, v___x_2742_);
v___x_2744_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2739_, v___x_2743_, v_i_2740_, v_n_2688_, v___x_2720_);
lean_dec(v_i_2740_);
v___y_2708_ = v___x_2744_;
goto v___jp_2707_;
}
v___jp_2745_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2718_, v___x_2719_, v_uninteresting_2703_);
lean_inc(v_n_2688_);
v___x_2747_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2718_, v___x_2719_, v___x_2746_, v_n_2688_);
switch(lean_obj_tag(v___x_2747_))
{
case 0:
{
lean_object* v_index_2748_; lean_object* v_size_2749_; lean_object* v___x_2750_; 
v_index_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_index_2748_);
lean_dec_ref_known(v___x_2747_, 3);
v_size_2749_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_size_2749_);
v___x_2750_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2746_, v_size_2749_, v_index_2748_, v_n_2688_, v___x_2720_);
lean_dec(v_index_2748_);
v___y_2708_ = v___x_2750_;
goto v___jp_2707_;
}
case 1:
{
lean_object* v_index_2751_; 
v_index_2751_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_index_2751_);
lean_dec_ref_known(v___x_2747_, 1);
v___y_2739_ = v___x_2746_;
v_i_2740_ = v_index_2751_;
goto v___jp_2738_;
}
default: 
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2746_, v___x_2752_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_index_2754_; 
v_index_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_index_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v___y_2739_ = v___x_2746_;
v_i_2740_ = v_index_2754_;
goto v___jp_2738_;
}
else
{
lean_dec(v_n_2688_);
v___y_2708_ = v___x_2746_;
goto v___jp_2707_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_2784_, v_a_2785_);
lean_dec(v_a_2785_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; lean_object* v_typeAnalysis_2802_; lean_object* v_caches_2803_; lean_object* v_target_2804_; lean_object* v_hypotheses_2805_; uint8_t v_didChange_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2893_; 
v___x_2801_ = lean_st_ref_take(v_a_2790_);
v_typeAnalysis_2802_ = lean_ctor_get(v___x_2801_, 1);
v_caches_2803_ = lean_ctor_get(v___x_2801_, 0);
v_target_2804_ = lean_ctor_get(v___x_2801_, 2);
v_hypotheses_2805_ = lean_ctor_get(v___x_2801_, 3);
v_didChange_2806_ = lean_ctor_get_uint8(v___x_2801_, sizeof(void*)*4);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2808_ = v___x_2801_;
v_isShared_2809_ = v_isSharedCheck_2893_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_hypotheses_2805_);
lean_inc(v_target_2804_);
lean_inc(v_typeAnalysis_2802_);
lean_inc(v_caches_2803_);
lean_dec(v___x_2801_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2893_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v_interestingStructures_2810_; lean_object* v_interestingEnums_2811_; lean_object* v_interestingMatchers_2812_; lean_object* v_uninteresting_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2892_; 
v_interestingStructures_2810_ = lean_ctor_get(v_typeAnalysis_2802_, 0);
v_interestingEnums_2811_ = lean_ctor_get(v_typeAnalysis_2802_, 1);
v_interestingMatchers_2812_ = lean_ctor_get(v_typeAnalysis_2802_, 2);
v_uninteresting_2813_ = lean_ctor_get(v_typeAnalysis_2802_, 3);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_typeAnalysis_2802_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2815_ = v_typeAnalysis_2802_;
v_isShared_2816_ = v_isSharedCheck_2892_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_uninteresting_2813_);
lean_inc(v_interestingMatchers_2812_);
lean_inc(v_interestingEnums_2811_);
lean_inc(v_interestingStructures_2810_);
lean_dec(v_typeAnalysis_2802_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2892_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___y_2818_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___y_2832_; lean_object* v_i_2833_; lean_object* v___y_2839_; lean_object* v___y_2849_; lean_object* v_i_2850_; lean_object* v___x_2865_; 
v___x_2828_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2829_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2830_ = lean_box(0);
lean_inc(v_n_2788_);
v___x_2865_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2828_, v___x_2829_, v_uninteresting_2813_, v_n_2788_);
switch(lean_obj_tag(v___x_2865_))
{
case 0:
{
lean_dec_ref_known(v___x_2865_, 3);
lean_dec(v_n_2788_);
v___y_2818_ = v_uninteresting_2813_;
goto v___jp_2817_;
}
case 1:
{
lean_object* v_index_2866_; lean_object* v_size_2867_; lean_object* v_keyArray_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_index_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_index_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v_size_2867_ = lean_ctor_get(v_uninteresting_2813_, 0);
v_keyArray_2868_ = lean_ctor_get(v_uninteresting_2813_, 1);
v___x_2869_ = lean_unsigned_to_nat(1u);
v___x_2870_ = lean_nat_add(v_size_2867_, v___x_2869_);
v___x_2871_ = lean_array_get_size(v_keyArray_2868_);
v___x_2872_ = lean_nat_dec_lt(v___x_2870_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_dec(v___x_2870_);
lean_dec(v_index_2866_);
goto v___jp_2855_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2873_ = lean_unsigned_to_nat(4u);
v___x_2874_ = lean_nat_mul(v___x_2870_, v___x_2873_);
v___x_2875_ = lean_unsigned_to_nat(3u);
v___x_2876_ = lean_nat_mul(v___x_2871_, v___x_2875_);
v___x_2877_ = lean_nat_dec_le(v___x_2874_, v___x_2876_);
lean_dec(v___x_2876_);
lean_dec(v___x_2874_);
if (v___x_2877_ == 0)
{
lean_dec(v___x_2870_);
lean_dec(v_index_2866_);
goto v___jp_2855_;
}
else
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Std_DHashMap_Raw_setEntry___redArg(v_uninteresting_2813_, v___x_2870_, v_index_2866_, v_n_2788_, v___x_2830_);
lean_dec(v_index_2866_);
v___y_2818_ = v___x_2878_;
goto v___jp_2817_;
}
}
}
default: 
{
lean_object* v_size_2879_; lean_object* v_keyArray_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v_size_2879_ = lean_ctor_get(v_uninteresting_2813_, 0);
v_keyArray_2880_ = lean_ctor_get(v_uninteresting_2813_, 1);
v___x_2881_ = lean_unsigned_to_nat(1u);
v___x_2882_ = lean_nat_add(v_size_2879_, v___x_2881_);
v___x_2883_ = lean_array_get_size(v_keyArray_2880_);
v___x_2884_ = lean_nat_dec_lt(v___x_2882_, v___x_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; 
lean_dec(v___x_2882_);
v___x_2885_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2828_, v___x_2829_, v_uninteresting_2813_);
v___y_2839_ = v___x_2885_;
goto v___jp_2838_;
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2886_ = lean_unsigned_to_nat(4u);
v___x_2887_ = lean_nat_mul(v___x_2882_, v___x_2886_);
lean_dec(v___x_2882_);
v___x_2888_ = lean_unsigned_to_nat(3u);
v___x_2889_ = lean_nat_mul(v___x_2883_, v___x_2888_);
v___x_2890_ = lean_nat_dec_le(v___x_2887_, v___x_2889_);
lean_dec(v___x_2889_);
lean_dec(v___x_2887_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2828_, v___x_2829_, v_uninteresting_2813_);
v___y_2839_ = v___x_2891_;
goto v___jp_2838_;
}
else
{
v___y_2839_ = v_uninteresting_2813_;
goto v___jp_2838_;
}
}
}
}
v___jp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 3, v___y_2818_);
v___x_2820_ = v___x_2815_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_interestingStructures_2810_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_interestingEnums_2811_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_interestingMatchers_2812_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v___y_2818_);
v___x_2820_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; 
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 1, v___x_2820_);
v___x_2822_ = v___x_2808_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_caches_2803_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_target_2804_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_hypotheses_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, sizeof(void*)*4, v_didChange_2806_);
v___x_2822_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = lean_st_ref_put(v_a_2790_, v___x_2822_);
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
}
}
v___jp_2831_:
{
lean_object* v_size_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_size_2834_ = lean_ctor_get(v___y_2832_, 0);
v___x_2835_ = lean_unsigned_to_nat(1u);
v___x_2836_ = lean_nat_add(v_size_2834_, v___x_2835_);
v___x_2837_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2832_, v___x_2836_, v_i_2833_, v_n_2788_, v___x_2830_);
lean_dec(v_i_2833_);
v___y_2818_ = v___x_2837_;
goto v___jp_2817_;
}
v___jp_2838_:
{
lean_object* v___x_2840_; 
lean_inc(v_n_2788_);
v___x_2840_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2828_, v___x_2829_, v___y_2839_, v_n_2788_);
switch(lean_obj_tag(v___x_2840_))
{
case 0:
{
lean_object* v_index_2841_; lean_object* v_size_2842_; lean_object* v___x_2843_; 
v_index_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_index_2841_);
lean_dec_ref_known(v___x_2840_, 3);
v_size_2842_ = lean_ctor_get(v___y_2839_, 0);
lean_inc(v_size_2842_);
v___x_2843_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2839_, v_size_2842_, v_index_2841_, v_n_2788_, v___x_2830_);
lean_dec(v_index_2841_);
v___y_2818_ = v___x_2843_;
goto v___jp_2817_;
}
case 1:
{
lean_object* v_index_2844_; 
v_index_2844_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_index_2844_);
lean_dec_ref_known(v___x_2840_, 1);
v___y_2832_ = v___y_2839_;
v_i_2833_ = v_index_2844_;
goto v___jp_2831_;
}
default: 
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_unsigned_to_nat(0u);
v___x_2846_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2839_, v___x_2845_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_index_2847_; 
v_index_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_index_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___y_2832_ = v___y_2839_;
v_i_2833_ = v_index_2847_;
goto v___jp_2831_;
}
else
{
lean_dec(v_n_2788_);
v___y_2818_ = v___y_2839_;
goto v___jp_2817_;
}
}
}
}
v___jp_2848_:
{
lean_object* v_size_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_size_2851_ = lean_ctor_get(v___y_2849_, 0);
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_2853_ = lean_nat_add(v_size_2851_, v___x_2852_);
v___x_2854_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2849_, v___x_2853_, v_i_2850_, v_n_2788_, v___x_2830_);
lean_dec(v_i_2850_);
v___y_2818_ = v___x_2854_;
goto v___jp_2817_;
}
v___jp_2855_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_2828_, v___x_2829_, v_uninteresting_2813_);
lean_inc(v_n_2788_);
v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_2828_, v___x_2829_, v___x_2856_, v_n_2788_);
switch(lean_obj_tag(v___x_2857_))
{
case 0:
{
lean_object* v_index_2858_; lean_object* v_size_2859_; lean_object* v___x_2860_; 
v_index_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_index_2858_);
lean_dec_ref_known(v___x_2857_, 3);
v_size_2859_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_size_2859_);
v___x_2860_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2856_, v_size_2859_, v_index_2858_, v_n_2788_, v___x_2830_);
lean_dec(v_index_2858_);
v___y_2818_ = v___x_2860_;
goto v___jp_2817_;
}
case 1:
{
lean_object* v_index_2861_; 
v_index_2861_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_index_2861_);
lean_dec_ref_known(v___x_2857_, 1);
v___y_2849_ = v___x_2856_;
v_i_2850_ = v_index_2861_;
goto v___jp_2848_;
}
default: 
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2856_, v___x_2862_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_index_2864_; 
v_index_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_index_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___y_2849_ = v___x_2856_;
v_i_2850_ = v_index_2864_;
goto v___jp_2848_;
}
else
{
lean_dec(v_n_2788_);
v___y_2818_ = v___x_2856_;
goto v___jp_2817_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
return v_res_2907_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_2908_; lean_object* v___x_2909_; 
v_cellCount_2908_ = lean_unsigned_to_nat(16u);
v___x_2909_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2908_);
return v___x_2909_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_2910_; lean_object* v___x_2911_; 
v_cellCount_2910_ = lean_unsigned_to_nat(16u);
v___x_2911_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2910_);
return v___x_2911_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2912_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_2913_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_2914_ = lean_unsigned_to_nat(0u);
v___x_2915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v___x_2913_);
lean_ctor_set(v___x_2915_, 2, v___x_2912_);
return v___x_2915_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
lean_ctor_set(v___x_2917_, 2, v___x_2916_);
lean_ctor_set(v___x_2917_, 3, v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_ctx_2920_, lean_object* v_target_2921_, lean_object* v_x_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2933_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2934_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3);
v___x_2935_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4));
v___x_2936_ = 0;
v___x_2937_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2937_, 0, v___x_2933_);
lean_ctor_set(v___x_2937_, 1, v___x_2934_);
lean_ctor_set(v___x_2937_, 2, v_target_2921_);
lean_ctor_set(v___x_2937_, 3, v___x_2935_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*4, v___x_2936_);
v___x_2938_ = lean_st_mk_ref(v___x_2937_);
lean_inc(v_a_2931_);
lean_inc_ref(v_a_2930_);
lean_inc(v_a_2929_);
lean_inc_ref(v_a_2928_);
lean_inc(v_a_2927_);
lean_inc_ref(v_a_2926_);
lean_inc(v_a_2925_);
lean_inc_ref(v_a_2924_);
lean_inc(v_a_2923_);
lean_inc(v___x_2938_);
v___x_2939_ = lean_apply_12(v_x_2922_, v_ctx_2920_, v___x_2938_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, lean_box(0));
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2949_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2949_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2949_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2944_ = lean_st_ref_get(v___x_2938_);
lean_dec(v___x_2938_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_a_2940_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2945_);
v___x_2947_ = v___x_2942_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v___x_2938_);
v_a_2950_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2939_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2939_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_ctx_2958_, lean_object* v_target_2959_, lean_object* v_x_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_ctx_2958_, v_target_2959_, v_x_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
lean_dec(v_a_2961_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_2972_, lean_object* v_ctx_2973_, lean_object* v_target_2974_, lean_object* v_x_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2986_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2987_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3);
v___x_2988_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4));
v___x_2989_ = 0;
v___x_2990_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2990_, 0, v___x_2986_);
lean_ctor_set(v___x_2990_, 1, v___x_2987_);
lean_ctor_set(v___x_2990_, 2, v_target_2974_);
lean_ctor_set(v___x_2990_, 3, v___x_2988_);
lean_ctor_set_uint8(v___x_2990_, sizeof(void*)*4, v___x_2989_);
v___x_2991_ = lean_st_mk_ref(v___x_2990_);
lean_inc(v_a_2984_);
lean_inc_ref(v_a_2983_);
lean_inc(v_a_2982_);
lean_inc_ref(v_a_2981_);
lean_inc(v_a_2980_);
lean_inc_ref(v_a_2979_);
lean_inc(v_a_2978_);
lean_inc_ref(v_a_2977_);
lean_inc(v_a_2976_);
lean_inc(v___x_2991_);
v___x_2992_ = lean_apply_12(v_x_2975_, v_ctx_2973_, v___x_2991_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, lean_box(0));
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3002_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3002_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3002_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2997_ = lean_st_ref_get(v___x_2991_);
lean_dec(v___x_2991_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_a_2993_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_2998_);
v___x_3000_ = v___x_2995_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v___x_2991_);
v_a_3003_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2992_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2992_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_3011_, lean_object* v_ctx_3012_, lean_object* v_target_3013_, lean_object* v_x_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_3011_, v_ctx_3012_, v_target_3013_, v_x_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
lean_dec(v_a_3015_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_ctx_3026_, lean_object* v_target_3027_, lean_object* v_x_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3039_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_3040_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3);
v___x_3041_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4));
v___x_3042_ = 0;
v___x_3043_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3039_);
lean_ctor_set(v___x_3043_, 1, v___x_3040_);
lean_ctor_set(v___x_3043_, 2, v_target_3027_);
lean_ctor_set(v___x_3043_, 3, v___x_3041_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*4, v___x_3042_);
v___x_3044_ = lean_st_mk_ref(v___x_3043_);
lean_inc(v_a_3037_);
lean_inc_ref(v_a_3036_);
lean_inc(v_a_3035_);
lean_inc_ref(v_a_3034_);
lean_inc(v_a_3033_);
lean_inc_ref(v_a_3032_);
lean_inc(v_a_3031_);
lean_inc_ref(v_a_3030_);
lean_inc(v_a_3029_);
lean_inc(v___x_3044_);
v___x_3045_ = lean_apply_12(v_x_3028_, v_ctx_3026_, v___x_3044_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, lean_box(0));
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3054_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3054_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3054_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3050_ = lean_st_ref_get(v___x_3044_);
lean_dec(v___x_3044_);
lean_dec(v___x_3050_);
if (v_isShared_3049_ == 0)
{
v___x_3052_ = v___x_3048_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3046_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
else
{
lean_dec(v___x_3044_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_ctx_3055_, lean_object* v_target_3056_, lean_object* v_x_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_ctx_3055_, v_target_3056_, v_x_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_3069_, lean_object* v_ctx_3070_, lean_object* v_target_3071_, lean_object* v_x_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3083_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_3084_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3);
v___x_3085_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4));
v___x_3086_ = 0;
v___x_3087_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3087_, 0, v___x_3083_);
lean_ctor_set(v___x_3087_, 1, v___x_3084_);
lean_ctor_set(v___x_3087_, 2, v_target_3071_);
lean_ctor_set(v___x_3087_, 3, v___x_3085_);
lean_ctor_set_uint8(v___x_3087_, sizeof(void*)*4, v___x_3086_);
v___x_3088_ = lean_st_mk_ref(v___x_3087_);
lean_inc(v_a_3081_);
lean_inc_ref(v_a_3080_);
lean_inc(v_a_3079_);
lean_inc_ref(v_a_3078_);
lean_inc(v_a_3077_);
lean_inc_ref(v_a_3076_);
lean_inc(v_a_3075_);
lean_inc_ref(v_a_3074_);
lean_inc(v_a_3073_);
lean_inc(v___x_3088_);
v___x_3089_ = lean_apply_12(v_x_3072_, v_ctx_3070_, v___x_3088_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, lean_box(0));
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3098_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_st_ref_get(v___x_3088_);
lean_dec(v___x_3088_);
lean_dec(v___x_3094_);
if (v_isShared_3093_ == 0)
{
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3090_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_dec(v___x_3088_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_3099_, lean_object* v_ctx_3100_, lean_object* v_target_3101_, lean_object* v_x_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_3099_, v_ctx_3100_, v_target_3101_, v_x_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
return v_res_3113_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3117_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3118_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3117_, v___x_3116_);
return v___x_3118_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___f_3120_; lean_object* v___x_3121_; 
v___x_3119_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2);
v___f_3120_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_3121_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3120_, v___x_3119_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3);
v___x_3123_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3124_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3123_, v___x_3122_);
return v___x_3124_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; 
v___x_3125_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4);
v___f_3126_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_3127_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3126_, v___x_3125_);
return v___x_3127_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5);
v___x_3129_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3130_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___f_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6);
v___f_3132_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_3133_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3132_, v___x_3131_);
return v___x_3133_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; 
v___x_3134_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7);
v___f_3135_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_3136_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3135_, v___x_3134_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___x_3138_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3139_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3138_, v___x_3137_);
return v___x_3139_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___f_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___f_3141_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_3142_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3141_, v___x_3140_);
return v___x_3142_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17(void){
_start:
{
lean_object* v_cls_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v_cls_3153_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_3154_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16));
v___x_3155_ = l_Lean_Name_append(v___x_3154_, v_cls_3153_);
return v___x_3155_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3158_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3160_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_3161_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3160_, v___x_3159_, v___x_3158_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___f_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; 
v___x_3162_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___f_3163_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3164_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_3165_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3164_, v___f_3163_, v___x_3162_);
return v___x_3165_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3166_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v___x_3167_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3168_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_3169_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3168_, v___x_3167_, v___x_3166_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___f_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; 
v___x_3170_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22);
v___f_3171_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3172_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_3173_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3172_, v___f_3171_, v___x_3170_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3174_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_3175_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3176_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_3177_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3176_, v___x_3175_, v___x_3174_);
return v___x_3177_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___f_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; 
v___x_3178_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24);
v___f_3179_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3180_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_3181_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3180_, v___f_3179_, v___x_3178_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___x_3185_; 
v___x_3182_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25);
v___f_3183_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3184_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_3185_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3184_, v___f_3183_, v___x_3182_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3186_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26);
v___x_3187_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3188_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_3189_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3188_, v___x_3187_, v___x_3186_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___f_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; 
v___x_3190_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27);
v___f_3191_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3192_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_3193_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3192_, v___f_3191_, v___x_3190_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___f_3196_; 
v___x_3194_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3195_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_3196_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3196_, 0, v___x_3195_);
lean_closure_set(v___f_3196_, 1, v___x_3194_);
return v___f_3196_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___f_3197_; lean_object* v___f_3198_; lean_object* v___f_3199_; 
v___f_3197_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3198_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___f_3199_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3199_, 0, v___f_3198_);
lean_closure_set(v___f_3199_, 1, v___f_3197_);
return v___f_3199_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___f_3201_; lean_object* v___f_3202_; 
v___x_3200_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_3201_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_3202_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3202_, 0, v___f_3201_);
lean_closure_set(v___f_3202_, 1, v___x_3200_);
return v___f_3202_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___f_3205_; 
v___f_3203_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3204_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_3205_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3205_, 0, v___f_3204_);
lean_closure_set(v___f_3205_, 1, v___f_3203_);
return v___f_3205_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33(void){
_start:
{
lean_object* v___f_3206_; lean_object* v___f_3207_; lean_object* v___f_3208_; 
v___f_3206_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3207_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___f_3208_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3208_, 0, v___f_3207_);
lean_closure_set(v___f_3208_, 1, v___f_3206_);
return v___f_3208_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___f_3210_; lean_object* v___f_3211_; 
v___x_3209_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_3210_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33);
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3211_, 0, v___f_3210_);
lean_closure_set(v___f_3211_, 1, v___x_3209_);
return v___f_3211_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35(void){
_start:
{
lean_object* v___f_3212_; lean_object* v___f_3213_; lean_object* v___f_3214_; 
v___f_3212_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_3213_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v___f_3214_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3214_, 0, v___f_3213_);
lean_closure_set(v___f_3214_, 1, v___f_3212_);
return v___f_3214_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36));
v___x_3217_ = l_Lean_stringToMessageData(v___x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v___y_3232_; lean_object* v___x_3250_; lean_object* v_toApplicative_3251_; lean_object* v_toFunctor_3252_; lean_object* v_toSeq_3253_; lean_object* v_toSeqLeft_3254_; lean_object* v_toSeqRight_3255_; lean_object* v___f_3256_; lean_object* v___f_3257_; lean_object* v___f_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; lean_object* v___f_3261_; lean_object* v___f_3262_; lean_object* v___f_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v_toApplicative_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3317_; 
v___x_3250_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_3251_ = lean_ctor_get(v___x_3250_, 0);
v_toFunctor_3252_ = lean_ctor_get(v_toApplicative_3251_, 0);
v_toSeq_3253_ = lean_ctor_get(v_toApplicative_3251_, 2);
v_toSeqLeft_3254_ = lean_ctor_get(v_toApplicative_3251_, 3);
v_toSeqRight_3255_ = lean_ctor_get(v_toApplicative_3251_, 4);
v___f_3256_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_3257_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_3252_, 2);
v___f_3258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3258_, 0, v_toFunctor_3252_);
v___f_3259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3259_, 0, v_toFunctor_3252_);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___f_3258_);
lean_ctor_set(v___x_3260_, 1, v___f_3259_);
lean_inc(v_toSeqRight_3255_);
v___f_3261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3261_, 0, v_toSeqRight_3255_);
lean_inc(v_toSeqLeft_3254_);
v___f_3262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3262_, 0, v_toSeqLeft_3254_);
lean_inc(v_toSeq_3253_);
v___f_3263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3263_, 0, v_toSeq_3253_);
v___x_3264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3260_);
lean_ctor_set(v___x_3264_, 1, v___f_3256_);
lean_ctor_set(v___x_3264_, 2, v___f_3263_);
lean_ctor_set(v___x_3264_, 3, v___f_3262_);
lean_ctor_set(v___x_3264_, 4, v___f_3261_);
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v___f_3257_);
v___x_3266_ = l_StateRefT_x27_instMonad___redArg(v___x_3265_);
v_toApplicative_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v___x_3266_, 1);
lean_dec(v_unused_3318_);
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3317_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_toApplicative_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3317_;
goto v_resetjp_3268_;
}
v___jp_3231_:
{
lean_object* v___x_3233_; lean_object* v_caches_3234_; lean_object* v_typeAnalysis_3235_; lean_object* v_target_3236_; lean_object* v_hypotheses_3237_; uint8_t v_didChange_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3249_; 
v___x_3233_ = lean_st_ref_take(v___y_3232_);
v_caches_3234_ = lean_ctor_get(v___x_3233_, 0);
v_typeAnalysis_3235_ = lean_ctor_get(v___x_3233_, 1);
v_target_3236_ = lean_ctor_get(v___x_3233_, 2);
v_hypotheses_3237_ = lean_ctor_get(v___x_3233_, 3);
v_didChange_3238_ = lean_ctor_get_uint8(v___x_3233_, sizeof(void*)*4);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3240_ = v___x_3233_;
v_isShared_3241_ = v_isSharedCheck_3249_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_hypotheses_3237_);
lean_inc(v_target_3236_);
lean_inc(v_typeAnalysis_3235_);
lean_inc(v_caches_3234_);
lean_dec(v___x_3233_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3249_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3242_ = lean_array_push(v_hypotheses_3237_, v_hyp_3218_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 3, v___x_3242_);
v___x_3244_ = v___x_3240_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_caches_3234_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_typeAnalysis_3235_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_target_3236_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v___x_3242_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, sizeof(void*)*4, v_didChange_3238_);
v___x_3244_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = lean_st_ref_put(v___y_3232_, v___x_3244_);
v___x_3246_ = lean_box(0);
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
}
}
v_resetjp_3268_:
{
lean_object* v_toFunctor_3271_; lean_object* v_toSeq_3272_; lean_object* v_toSeqLeft_3273_; lean_object* v_toSeqRight_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3315_; 
v_toFunctor_3271_ = lean_ctor_get(v_toApplicative_3267_, 0);
v_toSeq_3272_ = lean_ctor_get(v_toApplicative_3267_, 2);
v_toSeqLeft_3273_ = lean_ctor_get(v_toApplicative_3267_, 3);
v_toSeqRight_3274_ = lean_ctor_get(v_toApplicative_3267_, 4);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_toApplicative_3267_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v_toApplicative_3267_, 1);
lean_dec(v_unused_3316_);
v___x_3276_ = v_toApplicative_3267_;
v_isShared_3277_ = v_isSharedCheck_3315_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_toSeqRight_3274_);
lean_inc(v_toSeqLeft_3273_);
lean_inc(v_toSeq_3272_);
lean_inc(v_toFunctor_3271_);
lean_dec(v_toApplicative_3267_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3315_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___f_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; lean_object* v___f_3283_; lean_object* v___f_3284_; lean_object* v___f_3285_; lean_object* v___x_3287_; 
v___f_3278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_3279_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_3271_);
v___f_3280_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3280_, 0, v_toFunctor_3271_);
v___f_3281_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3281_, 0, v_toFunctor_3271_);
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___f_3280_);
lean_ctor_set(v___x_3282_, 1, v___f_3281_);
v___f_3283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3283_, 0, v_toSeqRight_3274_);
v___f_3284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3284_, 0, v_toSeqLeft_3273_);
v___f_3285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3285_, 0, v_toSeq_3272_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v___f_3283_);
lean_ctor_set(v___x_3276_, 3, v___f_3284_);
lean_ctor_set(v___x_3276_, 2, v___f_3285_);
lean_ctor_set(v___x_3276_, 1, v___f_3278_);
lean_ctor_set(v___x_3276_, 0, v___x_3282_);
v___x_3287_ = v___x_3276_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___f_3278_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v___f_3285_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v___f_3284_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v___f_3283_);
v___x_3287_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3289_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 1, v___f_3279_);
lean_ctor_set(v___x_3269_, 0, v___x_3287_);
v___x_3289_ = v___x_3269_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3287_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v___f_3279_);
v___x_3289_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v_options_3298_; uint8_t v_hasTrace_3299_; 
v___x_3290_ = l_StateRefT_x27_instMonad___redArg(v___x_3289_);
v___x_3291_ = l_ReaderT_instMonad___redArg(v___x_3290_);
v___x_3292_ = l_StateRefT_x27_instMonad___redArg(v___x_3291_);
v___x_3293_ = l_ReaderT_instMonad___redArg(v___x_3292_);
v___x_3294_ = l_ReaderT_instMonad___redArg(v___x_3293_);
v___x_3295_ = l_StateRefT_x27_instMonad___redArg(v___x_3294_);
v___x_3296_ = l_ReaderT_instMonad___redArg(v___x_3295_);
v___x_3297_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v_options_3298_ = lean_ctor_get(v_a_3228_, 2);
v_hasTrace_3299_ = lean_ctor_get_uint8(v_options_3298_, sizeof(void*)*1);
if (v_hasTrace_3299_ == 0)
{
lean_dec_ref(v___x_3296_);
v___y_3232_ = v_a_3220_;
goto v___jp_3231_;
}
else
{
lean_object* v_inheritedTraceOptions_3300_; lean_object* v_cls_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v_inheritedTraceOptions_3300_ = lean_ctor_get(v_a_3228_, 13);
v_cls_3301_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_3302_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_3303_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3300_, v_options_3298_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_dec_ref(v___x_3296_);
v___y_3232_ = v_a_3220_;
goto v___jp_3231_;
}
else
{
lean_object* v___x_3304_; lean_object* v_toMonadRef_3305_; lean_object* v_type_3306_; lean_object* v___f_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_6452__overap_3311_; lean_object* v___x_3312_; 
v___x_3304_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_3305_ = lean_ctor_get(v___x_3304_, 0);
v_type_3306_ = lean_ctor_get(v_hyp_3218_, 1);
v___f_3307_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_3308_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_3306_);
v___x_3309_ = l_Lean_MessageData_ofExpr(v_type_3306_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
lean_inc_ref(v_toMonadRef_3305_);
v___x_6452__overap_3311_ = l_Lean_addTrace___redArg(v___x_3296_, v___x_3297_, v_toMonadRef_3305_, v___f_3307_, v_cls_3301_, v___x_3310_);
lean_inc(v_a_3229_);
lean_inc_ref(v_a_3228_);
lean_inc(v_a_3227_);
lean_inc_ref(v_a_3226_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc(v_a_3223_);
lean_inc_ref(v_a_3222_);
lean_inc(v_a_3221_);
lean_inc(v_a_3220_);
lean_inc_ref(v_a_3219_);
v___x_3312_ = lean_apply_12(v___x_6452__overap_3311_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, lean_box(0));
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref_known(v___x_3312_, 1);
v___y_3232_ = v_a_3220_;
goto v___jp_3231_;
}
else
{
lean_dec_ref(v_hyp_3218_);
return v___x_3312_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
lean_dec(v_a_3328_);
lean_dec_ref(v_a_3327_);
lean_dec(v_a_3326_);
lean_dec_ref(v_a_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_3333_, lean_object* v___f_3334_, lean_object* v___x_3335_, lean_object* v___f_3336_, lean_object* v___x_3337_, lean_object* v___f_3338_, lean_object* v___f_3339_, lean_object* v___x_3340_, lean_object* v___f_3341_, lean_object* v___x_3342_, lean_object* v___x_3343_, lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_options_3361_; uint8_t v_hasTrace_3362_; 
v_options_3361_ = lean_ctor_get(v___y_3355_, 2);
v_hasTrace_3362_ = lean_ctor_get_uint8(v_options_3361_, sizeof(void*)*1);
if (v_hasTrace_3362_ == 0)
{
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___x_3343_);
lean_dec_ref(v___x_3342_);
lean_dec(v___f_3341_);
lean_dec(v___x_3340_);
lean_dec(v___f_3339_);
lean_dec(v___f_3338_);
lean_dec(v___x_3337_);
lean_dec(v___f_3336_);
lean_dec(v___x_3335_);
lean_dec(v___f_3334_);
lean_dec(v___x_3333_);
goto v___jp_3358_;
}
else
{
lean_object* v_inheritedTraceOptions_3363_; lean_object* v_cls_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v_inheritedTraceOptions_3363_ = lean_ctor_get(v___y_3355_, 13);
v_cls_3364_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_3365_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_3366_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3363_, v_options_3361_, v___x_3365_);
if (v___x_3366_ == 0)
{
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___x_3343_);
lean_dec_ref(v___x_3342_);
lean_dec(v___f_3341_);
lean_dec(v___x_3340_);
lean_dec(v___f_3339_);
lean_dec(v___f_3338_);
lean_dec(v___x_3337_);
lean_dec(v___f_3336_);
lean_dec(v___x_3335_);
lean_dec(v___f_3334_);
lean_dec(v___x_3333_);
goto v___jp_3358_;
}
else
{
lean_object* v___f_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v_toMonadRef_3379_; lean_object* v_type_3380_; lean_object* v___x_3381_; lean_object* v___f_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___f_3385_; lean_object* v___f_3386_; lean_object* v___f_3387_; lean_object* v___f_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_7548__overap_3392_; lean_object* v___x_3393_; 
v___f_3367_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_3368_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_3369_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3370_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3368_, v___x_3333_, v___x_3369_);
v___x_3371_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3367_, v___f_3334_, v___x_3370_);
lean_inc(v___x_3335_);
v___x_3372_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3368_, v___x_3335_, v___x_3371_);
lean_inc(v___f_3336_);
v___x_3373_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3367_, v___f_3336_, v___x_3372_);
lean_inc(v___x_3337_);
v___x_3374_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3368_, v___x_3337_, v___x_3373_);
lean_inc(v___f_3338_);
v___x_3375_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3367_, v___f_3338_, v___x_3374_);
lean_inc(v___f_3339_);
v___x_3376_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3367_, v___f_3339_, v___x_3375_);
lean_inc(v___x_3340_);
v___x_3377_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3368_, v___x_3340_, v___x_3376_);
lean_inc(v___f_3341_);
v___x_3378_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3367_, v___f_3341_, v___x_3377_);
v_toMonadRef_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc_ref(v_toMonadRef_3379_);
lean_dec_ref(v___x_3378_);
v_type_3380_ = lean_ctor_get(v___y_3345_, 1);
lean_inc_ref(v_type_3380_);
lean_dec_ref(v___y_3345_);
v___x_3381_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_3382_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3382_, 0, v___x_3381_);
lean_closure_set(v___f_3382_, 1, v___x_3335_);
v___f_3383_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3383_, 0, v___f_3382_);
lean_closure_set(v___f_3383_, 1, v___f_3336_);
v___f_3384_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3384_, 0, v___f_3383_);
lean_closure_set(v___f_3384_, 1, v___x_3337_);
v___f_3385_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3385_, 0, v___f_3384_);
lean_closure_set(v___f_3385_, 1, v___f_3338_);
v___f_3386_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3386_, 0, v___f_3385_);
lean_closure_set(v___f_3386_, 1, v___f_3339_);
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3387_, 0, v___f_3386_);
lean_closure_set(v___f_3387_, 1, v___x_3340_);
v___f_3388_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3388_, 0, v___f_3387_);
lean_closure_set(v___f_3388_, 1, v___f_3341_);
v___x_3389_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_3390_ = l_Lean_MessageData_ofExpr(v_type_3380_);
v___x_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_7548__overap_3392_ = l_Lean_addTrace___redArg(v___x_3342_, v___x_3343_, v_toMonadRef_3379_, v___f_3388_, v_cls_3364_, v___x_3391_);
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
v___x_3393_ = lean_apply_12(v___x_7548__overap_3392_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, lean_box(0));
return v___x_3393_;
}
}
v___jp_3358_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_3394_ = _args[0];
lean_object* v___f_3395_ = _args[1];
lean_object* v___x_3396_ = _args[2];
lean_object* v___f_3397_ = _args[3];
lean_object* v___x_3398_ = _args[4];
lean_object* v___f_3399_ = _args[5];
lean_object* v___f_3400_ = _args[6];
lean_object* v___x_3401_ = _args[7];
lean_object* v___f_3402_ = _args[8];
lean_object* v___x_3403_ = _args[9];
lean_object* v___x_3404_ = _args[10];
lean_object* v_x_3405_ = _args[11];
lean_object* v___y_3406_ = _args[12];
lean_object* v___y_3407_ = _args[13];
lean_object* v___y_3408_ = _args[14];
lean_object* v___y_3409_ = _args[15];
lean_object* v___y_3410_ = _args[16];
lean_object* v___y_3411_ = _args[17];
lean_object* v___y_3412_ = _args[18];
lean_object* v___y_3413_ = _args[19];
lean_object* v___y_3414_ = _args[20];
lean_object* v___y_3415_ = _args[21];
lean_object* v___y_3416_ = _args[22];
lean_object* v___y_3417_ = _args[23];
lean_object* v___y_3418_ = _args[24];
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_3394_, v___f_3395_, v___x_3396_, v___f_3397_, v___x_3398_, v___f_3399_, v___f_3400_, v___x_3401_, v___f_3402_, v___x_3403_, v___x_3404_, v_x_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v___y_3452_; lean_object* v___x_3453_; lean_object* v_toApplicative_3454_; lean_object* v_toFunctor_3455_; lean_object* v_toSeq_3456_; lean_object* v_toSeqLeft_3457_; lean_object* v_toSeqRight_3458_; lean_object* v___f_3459_; lean_object* v___f_3460_; lean_object* v___f_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; lean_object* v___f_3464_; lean_object* v___f_3465_; lean_object* v___f_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v_toApplicative_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3521_; 
v___x_3453_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_3454_ = lean_ctor_get(v___x_3453_, 0);
v_toFunctor_3455_ = lean_ctor_get(v_toApplicative_3454_, 0);
v_toSeq_3456_ = lean_ctor_get(v_toApplicative_3454_, 2);
v_toSeqLeft_3457_ = lean_ctor_get(v_toApplicative_3454_, 3);
v_toSeqRight_3458_ = lean_ctor_get(v_toApplicative_3454_, 4);
v___f_3459_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_3460_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_3455_, 2);
v___f_3461_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3461_, 0, v_toFunctor_3455_);
v___f_3462_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3462_, 0, v_toFunctor_3455_);
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___f_3461_);
lean_ctor_set(v___x_3463_, 1, v___f_3462_);
lean_inc(v_toSeqRight_3458_);
v___f_3464_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3464_, 0, v_toSeqRight_3458_);
lean_inc(v_toSeqLeft_3457_);
v___f_3465_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3465_, 0, v_toSeqLeft_3457_);
lean_inc(v_toSeq_3456_);
v___f_3466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3466_, 0, v_toSeq_3456_);
v___x_3467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3463_);
lean_ctor_set(v___x_3467_, 1, v___f_3459_);
lean_ctor_set(v___x_3467_, 2, v___f_3466_);
lean_ctor_set(v___x_3467_, 3, v___f_3465_);
lean_ctor_set(v___x_3467_, 4, v___f_3464_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
lean_ctor_set(v___x_3468_, 1, v___f_3460_);
v___x_3469_ = l_StateRefT_x27_instMonad___redArg(v___x_3468_);
v_toApplicative_3470_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3521_ == 0)
{
lean_object* v_unused_3522_; 
v_unused_3522_ = lean_ctor_get(v___x_3469_, 1);
lean_dec(v_unused_3522_);
v___x_3472_ = v___x_3469_;
v_isShared_3473_ = v_isSharedCheck_3521_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_toApplicative_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3521_;
goto v_resetjp_3471_;
}
v___jp_3433_:
{
lean_object* v___x_3434_; lean_object* v_caches_3435_; lean_object* v_typeAnalysis_3436_; lean_object* v_target_3437_; lean_object* v_hypotheses_3438_; uint8_t v_didChange_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3450_; 
v___x_3434_ = lean_st_ref_take(v_a_3422_);
v_caches_3435_ = lean_ctor_get(v___x_3434_, 0);
v_typeAnalysis_3436_ = lean_ctor_get(v___x_3434_, 1);
v_target_3437_ = lean_ctor_get(v___x_3434_, 2);
v_hypotheses_3438_ = lean_ctor_get(v___x_3434_, 3);
v_didChange_3439_ = lean_ctor_get_uint8(v___x_3434_, sizeof(void*)*4);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3441_ = v___x_3434_;
v_isShared_3442_ = v_isSharedCheck_3450_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_hypotheses_3438_);
lean_inc(v_target_3437_);
lean_inc(v_typeAnalysis_3436_);
lean_inc(v_caches_3435_);
lean_dec(v___x_3434_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3450_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = l_Array_append___redArg(v_hypotheses_3438_, v_hyps_3420_);
lean_dec_ref(v_hyps_3420_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 3, v___x_3443_);
v___x_3445_ = v___x_3441_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_caches_3435_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_typeAnalysis_3436_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_target_3437_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v___x_3443_);
lean_ctor_set_uint8(v_reuseFailAlloc_3449_, sizeof(void*)*4, v_didChange_3439_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_st_ref_put(v_a_3422_, v___x_3445_);
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
}
}
v___jp_3451_:
{
if (lean_obj_tag(v___y_3452_) == 0)
{
lean_dec_ref_known(v___y_3452_, 1);
goto v___jp_3433_;
}
else
{
lean_dec_ref(v_hyps_3420_);
return v___y_3452_;
}
}
v_resetjp_3471_:
{
lean_object* v_toFunctor_3474_; lean_object* v_toSeq_3475_; lean_object* v_toSeqLeft_3476_; lean_object* v_toSeqRight_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3519_; 
v_toFunctor_3474_ = lean_ctor_get(v_toApplicative_3470_, 0);
v_toSeq_3475_ = lean_ctor_get(v_toApplicative_3470_, 2);
v_toSeqLeft_3476_ = lean_ctor_get(v_toApplicative_3470_, 3);
v_toSeqRight_3477_ = lean_ctor_get(v_toApplicative_3470_, 4);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_toApplicative_3470_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; 
v_unused_3520_ = lean_ctor_get(v_toApplicative_3470_, 1);
lean_dec(v_unused_3520_);
v___x_3479_ = v_toApplicative_3470_;
v_isShared_3480_ = v_isSharedCheck_3519_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_toSeqRight_3477_);
lean_inc(v_toSeqLeft_3476_);
lean_inc(v_toSeq_3475_);
lean_inc(v_toFunctor_3474_);
lean_dec(v_toApplicative_3470_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3519_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___f_3481_; lean_object* v___f_3482_; lean_object* v___f_3483_; lean_object* v___f_3484_; lean_object* v___x_3485_; lean_object* v___f_3486_; lean_object* v___f_3487_; lean_object* v___f_3488_; lean_object* v___x_3490_; 
v___f_3481_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_3482_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_3474_);
v___f_3483_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3483_, 0, v_toFunctor_3474_);
v___f_3484_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3484_, 0, v_toFunctor_3474_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___f_3483_);
lean_ctor_set(v___x_3485_, 1, v___f_3484_);
v___f_3486_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3486_, 0, v_toSeqRight_3477_);
v___f_3487_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3487_, 0, v_toSeqLeft_3476_);
v___f_3488_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3488_, 0, v_toSeq_3475_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 4, v___f_3486_);
lean_ctor_set(v___x_3479_, 3, v___f_3487_);
lean_ctor_set(v___x_3479_, 2, v___f_3488_);
lean_ctor_set(v___x_3479_, 1, v___f_3481_);
lean_ctor_set(v___x_3479_, 0, v___x_3485_);
v___x_3490_ = v___x_3479_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___f_3481_);
lean_ctor_set(v_reuseFailAlloc_3518_, 2, v___f_3488_);
lean_ctor_set(v_reuseFailAlloc_3518_, 3, v___f_3487_);
lean_ctor_set(v_reuseFailAlloc_3518_, 4, v___f_3486_);
v___x_3490_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3492_; 
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v___f_3482_);
lean_ctor_set(v___x_3472_, 0, v___x_3490_);
v___x_3492_ = v___x_3472_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v___f_3482_);
v___x_3492_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___f_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_3493_ = l_StateRefT_x27_instMonad___redArg(v___x_3492_);
v___x_3494_ = l_ReaderT_instMonad___redArg(v___x_3493_);
v___x_3495_ = l_StateRefT_x27_instMonad___redArg(v___x_3494_);
v___x_3496_ = l_ReaderT_instMonad___redArg(v___x_3495_);
v___x_3497_ = l_ReaderT_instMonad___redArg(v___x_3496_);
v___x_3498_ = l_StateRefT_x27_instMonad___redArg(v___x_3497_);
v___x_3499_ = l_ReaderT_instMonad___redArg(v___x_3498_);
v___f_3500_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_3501_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_3502_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_3503_ = lean_unsigned_to_nat(0u);
v___x_3504_ = lean_array_get_size(v_hyps_3420_);
v___x_3505_ = lean_nat_dec_lt(v___x_3503_, v___x_3504_);
if (v___x_3505_ == 0)
{
lean_dec_ref(v___x_3499_);
goto v___jp_3433_;
}
else
{
lean_object* v___f_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
lean_inc_ref(v___x_3499_);
v___f_3506_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 25, 11);
lean_closure_set(v___f_3506_, 0, v___x_3501_);
lean_closure_set(v___f_3506_, 1, v___f_3500_);
lean_closure_set(v___f_3506_, 2, v___x_3501_);
lean_closure_set(v___f_3506_, 3, v___f_3500_);
lean_closure_set(v___f_3506_, 4, v___x_3501_);
lean_closure_set(v___f_3506_, 5, v___f_3500_);
lean_closure_set(v___f_3506_, 6, v___f_3500_);
lean_closure_set(v___f_3506_, 7, v___x_3501_);
lean_closure_set(v___f_3506_, 8, v___f_3500_);
lean_closure_set(v___f_3506_, 9, v___x_3499_);
lean_closure_set(v___f_3506_, 10, v___x_3502_);
v___x_3507_ = lean_box(0);
v___x_3508_ = lean_nat_dec_le(v___x_3504_, v___x_3504_);
if (v___x_3508_ == 0)
{
if (v___x_3505_ == 0)
{
lean_dec_ref(v___f_3506_);
lean_dec_ref(v___x_3499_);
goto v___jp_3433_;
}
else
{
size_t v___x_3509_; size_t v___x_3510_; lean_object* v___x_7104__overap_3511_; lean_object* v___x_3512_; 
v___x_3509_ = ((size_t)0ULL);
v___x_3510_ = lean_usize_of_nat(v___x_3504_);
lean_inc_ref(v_hyps_3420_);
v___x_7104__overap_3511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3499_, v___f_3506_, v_hyps_3420_, v___x_3509_, v___x_3510_, v___x_3507_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3427_);
lean_inc_ref(v_a_3426_);
lean_inc(v_a_3425_);
lean_inc_ref(v_a_3424_);
lean_inc(v_a_3423_);
lean_inc(v_a_3422_);
lean_inc_ref(v_a_3421_);
v___x_3512_ = lean_apply_12(v___x_7104__overap_3511_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, lean_box(0));
v___y_3452_ = v___x_3512_;
goto v___jp_3451_;
}
}
else
{
size_t v___x_3513_; size_t v___x_3514_; lean_object* v___x_7108__overap_3515_; lean_object* v___x_3516_; 
v___x_3513_ = ((size_t)0ULL);
v___x_3514_ = lean_usize_of_nat(v___x_3504_);
lean_inc_ref(v_hyps_3420_);
v___x_7108__overap_3515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3499_, v___f_3506_, v_hyps_3420_, v___x_3513_, v___x_3514_, v___x_3507_);
lean_inc(v_a_3431_);
lean_inc_ref(v_a_3430_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3427_);
lean_inc_ref(v_a_3426_);
lean_inc(v_a_3425_);
lean_inc_ref(v_a_3424_);
lean_inc(v_a_3423_);
lean_inc(v_a_3422_);
lean_inc_ref(v_a_3421_);
v___x_3516_ = lean_apply_12(v___x_7108__overap_3515_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, lean_box(0));
v___y_3452_ = v___x_3516_;
goto v___jp_3451_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_3537_){
_start:
{
lean_object* v___x_3539_; lean_object* v_hypotheses_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_st_ref_get(v_a_3537_);
v_hypotheses_3540_ = lean_ctor_get(v___x_3539_, 3);
lean_inc_ref(v_hypotheses_3540_);
lean_dec(v___x_3539_);
v___x_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3541_, 0, v_hypotheses_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_3542_);
lean_dec(v_a_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___x_3557_; lean_object* v_hypotheses_3558_; lean_object* v___x_3559_; 
v___x_3557_ = lean_st_ref_get(v_a_3546_);
v_hypotheses_3558_ = lean_ctor_get(v___x_3557_, 3);
lean_inc_ref(v_hypotheses_3558_);
lean_dec(v___x_3557_);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_hypotheses_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; lean_object* v_caches_3587_; lean_object* v_typeAnalysis_3588_; lean_object* v_target_3589_; uint8_t v_didChange_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3600_; 
v___x_3586_ = lean_st_ref_take(v___y_3575_);
v_caches_3587_ = lean_ctor_get(v___x_3586_, 0);
v_typeAnalysis_3588_ = lean_ctor_get(v___x_3586_, 1);
v_target_3589_ = lean_ctor_get(v___x_3586_, 2);
v_didChange_3590_ = lean_ctor_get_uint8(v___x_3586_, sizeof(void*)*4);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; 
v_unused_3601_ = lean_ctor_get(v___x_3586_, 3);
lean_dec(v_unused_3601_);
v___x_3592_ = v___x_3586_;
v_isShared_3593_ = v_isSharedCheck_3600_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_target_3589_);
lean_inc(v_typeAnalysis_3588_);
lean_inc(v_caches_3587_);
lean_dec(v___x_3586_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3600_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 3, v_hyps_3573_);
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_caches_3587_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_typeAnalysis_3588_);
lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_target_3589_);
lean_ctor_set(v_reuseFailAlloc_3599_, 3, v_hyps_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3599_, sizeof(void*)*4, v_didChange_3590_);
v___x_3595_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = lean_st_ref_put(v___y_3575_, v___x_3595_);
v___x_3597_ = lean_box(0);
v___x_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
return v___x_3598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3616_, lean_object* v_hyps_3617_){
_start:
{
lean_object* v___f_3618_; lean_object* v___x_3619_; 
v___f_3618_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3618_, 0, v_hyps_3617_);
v___x_3619_ = lean_apply_2(v_inst_3616_, lean_box(0), v___f_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; lean_object* v_caches_3633_; lean_object* v_typeAnalysis_3634_; lean_object* v_target_3635_; uint8_t v_didChange_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3647_; 
v___x_3632_ = lean_st_ref_take(v___y_3621_);
v_caches_3633_ = lean_ctor_get(v___x_3632_, 0);
v_typeAnalysis_3634_ = lean_ctor_get(v___x_3632_, 1);
v_target_3635_ = lean_ctor_get(v___x_3632_, 2);
v_didChange_3636_ = lean_ctor_get_uint8(v___x_3632_, sizeof(void*)*4);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3647_ == 0)
{
lean_object* v_unused_3648_; 
v_unused_3648_ = lean_ctor_get(v___x_3632_, 3);
lean_dec(v_unused_3648_);
v___x_3638_ = v___x_3632_;
v_isShared_3639_ = v_isSharedCheck_3647_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_target_3635_);
lean_inc(v_typeAnalysis_3634_);
lean_inc(v_caches_3633_);
lean_dec(v___x_3632_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3647_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3640_; lean_object* v___x_3642_; 
v___x_3640_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4));
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 3, v___x_3640_);
v___x_3642_ = v___x_3638_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_caches_3633_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_typeAnalysis_3634_);
lean_ctor_set(v_reuseFailAlloc_3646_, 2, v_target_3635_);
lean_ctor_set(v_reuseFailAlloc_3646_, 3, v___x_3640_);
lean_ctor_set_uint8(v_reuseFailAlloc_3646_, sizeof(void*)*4, v_didChange_3636_);
v___x_3642_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = lean_st_ref_put(v___y_3621_, v___x_3642_);
v___x_3644_ = lean_box(0);
v___x_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3662_, lean_object* v_cls_3663_, lean_object* v_____do__lift_3664_, lean_object* v_____do__lift_3665_){
_start:
{
uint8_t v_hasTrace_3666_; 
v_hasTrace_3666_ = lean_ctor_get_uint8(v_____do__lift_3665_, sizeof(void*)*1);
if (v_hasTrace_3666_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
lean_dec(v_cls_3663_);
v___x_3667_ = lean_box(v_hasTrace_3666_);
v___x_3668_ = lean_apply_2(v_toPure_3662_, lean_box(0), v___x_3667_);
return v___x_3668_;
}
else
{
lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3669_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16));
v___x_3670_ = l_Lean_Name_append(v___x_3669_, v_cls_3663_);
v___x_3671_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3664_, v_____do__lift_3665_, v___x_3670_);
lean_dec(v___x_3670_);
v___x_3672_ = lean_box(v___x_3671_);
v___x_3673_ = lean_apply_2(v_toPure_3662_, lean_box(0), v___x_3672_);
return v___x_3673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3674_, lean_object* v_cls_3675_, lean_object* v_____do__lift_3676_, lean_object* v_____do__lift_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3674_, v_cls_3675_, v_____do__lift_3676_, v_____do__lift_3677_);
lean_dec_ref(v_____do__lift_3677_);
lean_dec_ref(v_____do__lift_3676_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_toPure_3679_, lean_object* v_cls_3680_, lean_object* v_toBind_3681_, lean_object* v_inst_3682_, lean_object* v_____do__lift_3683_){
_start:
{
lean_object* v___f_3684_; lean_object* v___x_3685_; 
v___f_3684_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3684_, 0, v_toPure_3679_);
lean_closure_set(v___f_3684_, 1, v_cls_3680_);
lean_closure_set(v___f_3684_, 2, v_____do__lift_3683_);
v___x_3685_ = lean_apply_4(v_toBind_3681_, lean_box(0), lean_box(0), v_inst_3682_, v___f_3684_);
return v___x_3685_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3688_ = l_Lean_stringToMessageData(v___x_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3689_, lean_object* v_a_3690_, lean_object* v___y_3691_, lean_object* v_inst_3692_, lean_object* v_inst_3693_, lean_object* v_inst_3694_, lean_object* v_inst_3695_, lean_object* v_cls_3696_, uint8_t v_____do__lift_3697_){
_start:
{
if (v_____do__lift_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec(v_cls_3696_);
lean_dec(v_inst_3695_);
lean_dec_ref(v_inst_3694_);
lean_dec_ref(v_inst_3693_);
lean_dec_ref(v_inst_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_a_3690_);
v___x_3698_ = lean_box(0);
v___x_3699_ = lean_apply_2(v_toPure_3689_, lean_box(0), v___x_3698_);
return v___x_3699_;
}
else
{
lean_object* v_type_3700_; lean_object* v_type_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
lean_dec(v_toPure_3689_);
v_type_3700_ = lean_ctor_get(v_a_3690_, 1);
lean_inc_ref(v_type_3700_);
lean_dec_ref(v_a_3690_);
v_type_3701_ = lean_ctor_get(v___y_3691_, 1);
lean_inc_ref(v_type_3701_);
lean_dec_ref(v___y_3691_);
v___x_3702_ = l_Lean_MessageData_ofExpr(v_type_3700_);
v___x_3703_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = l_Lean_MessageData_ofExpr(v_type_3701_);
v___x_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3704_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = l_Lean_addTrace___redArg(v_inst_3692_, v_inst_3693_, v_inst_3694_, v_inst_3695_, v_cls_3696_, v___x_3706_);
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3708_, lean_object* v_a_3709_, lean_object* v___y_3710_, lean_object* v_inst_3711_, lean_object* v_inst_3712_, lean_object* v_inst_3713_, lean_object* v_inst_3714_, lean_object* v_cls_3715_, lean_object* v_____do__lift_3716_){
_start:
{
uint8_t v_____do__lift_3352__boxed_3717_; lean_object* v_res_3718_; 
v_____do__lift_3352__boxed_3717_ = lean_unbox(v_____do__lift_3716_);
v_res_3718_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3708_, v_a_3709_, v___y_3710_, v_inst_3711_, v_inst_3712_, v_inst_3713_, v_inst_3714_, v_cls_3715_, v_____do__lift_3352__boxed_3717_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3719_, lean_object* v_toPure_3720_, lean_object* v_toBind_3721_, lean_object* v_inst_3722_, lean_object* v_a_3723_, lean_object* v_inst_3724_, lean_object* v_inst_3725_, lean_object* v_inst_3726_, lean_object* v_x_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v_getInheritedTraceOptions_3729_; lean_object* v_cls_3730_; lean_object* v___f_3731_; lean_object* v___f_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_getInheritedTraceOptions_3729_ = lean_ctor_get(v_inst_3719_, 2);
lean_inc(v_getInheritedTraceOptions_3729_);
v_cls_3730_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
lean_inc_n(v_toBind_3721_, 2);
lean_inc(v_toPure_3720_);
v___f_3731_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3731_, 0, v_toPure_3720_);
lean_closure_set(v___f_3731_, 1, v_cls_3730_);
lean_closure_set(v___f_3731_, 2, v_toBind_3721_);
lean_closure_set(v___f_3731_, 3, v_inst_3722_);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3732_, 0, v_toPure_3720_);
lean_closure_set(v___f_3732_, 1, v_a_3723_);
lean_closure_set(v___f_3732_, 2, v___y_3728_);
lean_closure_set(v___f_3732_, 3, v_inst_3724_);
lean_closure_set(v___f_3732_, 4, v_inst_3719_);
lean_closure_set(v___f_3732_, 5, v_inst_3725_);
lean_closure_set(v___f_3732_, 6, v_inst_3726_);
lean_closure_set(v___f_3732_, 7, v_cls_3730_);
v___x_3733_ = lean_apply_4(v_toBind_3721_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3729_, v___f_3731_);
v___x_3734_ = lean_apply_4(v_toBind_3721_, lean_box(0), lean_box(0), v___x_3733_, v___f_3732_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3735_, lean_object* v_res_3736_, lean_object* v_____r_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_apply_2(v_toPure_3735_, lean_box(0), v_res_3736_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3739_, lean_object* v_toBind_3740_, lean_object* v___f_3741_, lean_object* v_____r_3742_){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3743_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3744_ = lean_apply_2(v_inst_3739_, lean_box(0), v___x_3743_);
v___x_3745_ = lean_apply_4(v_toBind_3740_, lean_box(0), lean_box(0), v___x_3744_, v___f_3741_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3746_, lean_object* v_____r_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = lean_apply_1(v___f_3746_, v_____r_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3749_, lean_object* v_type_3750_, lean_object* v_type_3751_, lean_object* v_inst_3752_, lean_object* v_inst_3753_, lean_object* v_inst_3754_, lean_object* v_inst_3755_, lean_object* v_cls_3756_, lean_object* v_toBind_3757_, lean_object* v___f_3758_, uint8_t v_____do__lift_3759_){
_start:
{
if (v_____do__lift_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
lean_dec(v___f_3758_);
lean_dec(v_toBind_3757_);
lean_dec(v_cls_3756_);
lean_dec(v_inst_3755_);
lean_dec_ref(v_inst_3754_);
lean_dec_ref(v_inst_3753_);
lean_dec_ref(v_inst_3752_);
lean_dec_ref(v_type_3751_);
lean_dec_ref(v_type_3750_);
v___x_3760_ = lean_box(0);
v___x_3761_ = lean_apply_1(v___f_3749_, v___x_3760_);
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_dec(v___f_3749_);
v___x_3762_ = l_Lean_MessageData_ofExpr(v_type_3750_);
v___x_3763_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l_Lean_MessageData_ofExpr(v_type_3751_);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = l_Lean_addTrace___redArg(v_inst_3752_, v_inst_3753_, v_inst_3754_, v_inst_3755_, v_cls_3756_, v___x_3766_);
v___x_3768_ = lean_apply_4(v_toBind_3757_, lean_box(0), lean_box(0), v___x_3767_, v___f_3758_);
return v___x_3768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3769_, lean_object* v_type_3770_, lean_object* v_type_3771_, lean_object* v_inst_3772_, lean_object* v_inst_3773_, lean_object* v_inst_3774_, lean_object* v_inst_3775_, lean_object* v_cls_3776_, lean_object* v_toBind_3777_, lean_object* v___f_3778_, lean_object* v_____do__lift_3779_){
_start:
{
uint8_t v_____do__lift_3452__boxed_3780_; lean_object* v_res_3781_; 
v_____do__lift_3452__boxed_3780_ = lean_unbox(v_____do__lift_3779_);
v_res_3781_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3769_, v_type_3770_, v_type_3771_, v_inst_3772_, v_inst_3773_, v_inst_3774_, v_inst_3775_, v_cls_3776_, v_toBind_3777_, v___f_3778_, v_____do__lift_3452__boxed_3780_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3782_, lean_object* v_inst_3783_, lean_object* v_toBind_3784_, lean_object* v_inst_3785_, lean_object* v___f_3786_, lean_object* v_a_3787_, lean_object* v_inst_3788_, lean_object* v_inst_3789_, lean_object* v_inst_3790_, lean_object* v_inst_3791_, lean_object* v___f_3792_, lean_object* v_res_3793_){
_start:
{
lean_object* v___x_3794_; lean_object* v_zero_3795_; uint8_t v_isZero_3796_; 
v___x_3794_ = lean_array_get_size(v_res_3793_);
v_zero_3795_ = lean_unsigned_to_nat(0u);
v_isZero_3796_ = lean_nat_dec_eq(v___x_3794_, v_zero_3795_);
if (v_isZero_3796_ == 1)
{
lean_object* v___f_3797_; lean_object* v___f_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
lean_dec(v___f_3792_);
lean_dec(v_inst_3791_);
lean_dec_ref(v_inst_3790_);
lean_dec(v_inst_3789_);
lean_dec_ref(v_inst_3788_);
lean_dec_ref(v_a_3787_);
lean_inc_ref(v_res_3793_);
lean_inc(v_toPure_3782_);
v___f_3797_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3797_, 0, v_toPure_3782_);
lean_closure_set(v___f_3797_, 1, v_res_3793_);
lean_inc(v_toBind_3784_);
v___f_3798_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3798_, 0, v_inst_3783_);
lean_closure_set(v___f_3798_, 1, v_toBind_3784_);
lean_closure_set(v___f_3798_, 2, v___f_3797_);
v___x_3799_ = lean_box(0);
v___x_3800_ = lean_nat_dec_lt(v_zero_3795_, v___x_3794_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec_ref(v_res_3793_);
lean_dec(v___f_3786_);
lean_dec_ref(v_inst_3785_);
v___x_3801_ = lean_apply_2(v_toPure_3782_, lean_box(0), v___x_3799_);
v___x_3802_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3801_, v___f_3798_);
return v___x_3802_;
}
else
{
uint8_t v___x_3803_; 
v___x_3803_ = lean_nat_dec_le(v___x_3794_, v___x_3794_);
if (v___x_3803_ == 0)
{
if (v___x_3800_ == 0)
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
lean_dec_ref(v_res_3793_);
lean_dec(v___f_3786_);
lean_dec_ref(v_inst_3785_);
v___x_3804_ = lean_apply_2(v_toPure_3782_, lean_box(0), v___x_3799_);
v___x_3805_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3804_, v___f_3798_);
return v___x_3805_;
}
else
{
size_t v___x_3806_; size_t v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_dec(v_toPure_3782_);
v___x_3806_ = ((size_t)0ULL);
v___x_3807_ = lean_usize_of_nat(v___x_3794_);
v___x_3808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3785_, v___f_3786_, v_res_3793_, v___x_3806_, v___x_3807_, v___x_3799_);
v___x_3809_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3808_, v___f_3798_);
return v___x_3809_;
}
}
else
{
size_t v___x_3810_; size_t v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
lean_dec(v_toPure_3782_);
v___x_3810_ = ((size_t)0ULL);
v___x_3811_ = lean_usize_of_nat(v___x_3794_);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3785_, v___f_3786_, v_res_3793_, v___x_3810_, v___x_3811_, v___x_3799_);
v___x_3813_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3812_, v___f_3798_);
return v___x_3813_;
}
}
}
else
{
lean_object* v_one_3814_; lean_object* v_n_3815_; uint8_t v_isZero_3816_; 
lean_dec(v___f_3786_);
v_one_3814_ = lean_unsigned_to_nat(1u);
v_n_3815_ = lean_nat_sub(v___x_3794_, v_one_3814_);
v_isZero_3816_ = lean_nat_dec_eq(v_n_3815_, v_zero_3795_);
lean_dec(v_n_3815_);
if (v_isZero_3816_ == 1)
{
lean_object* v_newHyp_3817_; lean_object* v_type_3818_; lean_object* v_type_3819_; uint8_t v___x_3820_; 
lean_dec(v___f_3792_);
v_newHyp_3817_ = lean_array_fget_borrowed(v_res_3793_, v_zero_3795_);
v_type_3818_ = lean_ctor_get(v_newHyp_3817_, 1);
v_type_3819_ = lean_ctor_get(v_a_3787_, 1);
lean_inc_ref(v_type_3819_);
lean_dec_ref(v_a_3787_);
v___x_3820_ = lean_expr_eqv(v_type_3818_, v_type_3819_);
if (v___x_3820_ == 0)
{
lean_object* v_getInheritedTraceOptions_3821_; lean_object* v___f_3822_; lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v_cls_3825_; lean_object* v___f_3826_; lean_object* v___f_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
lean_inc_ref(v_type_3818_);
v_getInheritedTraceOptions_3821_ = lean_ctor_get(v_inst_3788_, 2);
lean_inc(v_getInheritedTraceOptions_3821_);
lean_inc(v_toPure_3782_);
v___f_3822_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3822_, 0, v_toPure_3782_);
lean_closure_set(v___f_3822_, 1, v_res_3793_);
lean_inc_n(v_toBind_3784_, 4);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3823_, 0, v_inst_3783_);
lean_closure_set(v___f_3823_, 1, v_toBind_3784_);
lean_closure_set(v___f_3823_, 2, v___f_3822_);
lean_inc_ref(v___f_3823_);
v___f_3824_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3824_, 0, v___f_3823_);
v_cls_3825_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___f_3826_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3826_, 0, v_toPure_3782_);
lean_closure_set(v___f_3826_, 1, v_cls_3825_);
lean_closure_set(v___f_3826_, 2, v_toBind_3784_);
lean_closure_set(v___f_3826_, 3, v_inst_3789_);
v___f_3827_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3827_, 0, v___f_3823_);
lean_closure_set(v___f_3827_, 1, v_type_3819_);
lean_closure_set(v___f_3827_, 2, v_type_3818_);
lean_closure_set(v___f_3827_, 3, v_inst_3785_);
lean_closure_set(v___f_3827_, 4, v_inst_3788_);
lean_closure_set(v___f_3827_, 5, v_inst_3790_);
lean_closure_set(v___f_3827_, 6, v_inst_3791_);
lean_closure_set(v___f_3827_, 7, v_cls_3825_);
lean_closure_set(v___f_3827_, 8, v_toBind_3784_);
lean_closure_set(v___f_3827_, 9, v___f_3824_);
v___x_3828_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3821_, v___f_3826_);
v___x_3829_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3828_, v___f_3827_);
return v___x_3829_;
}
else
{
lean_object* v___x_3830_; 
lean_dec_ref(v_type_3819_);
lean_dec(v_inst_3791_);
lean_dec_ref(v_inst_3790_);
lean_dec(v_inst_3789_);
lean_dec_ref(v_inst_3788_);
lean_dec_ref(v_inst_3785_);
lean_dec(v_toBind_3784_);
lean_dec(v_inst_3783_);
v___x_3830_ = lean_apply_2(v_toPure_3782_, lean_box(0), v_res_3793_);
return v___x_3830_;
}
}
else
{
lean_object* v___f_3831_; lean_object* v___f_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
lean_dec(v_inst_3791_);
lean_dec_ref(v_inst_3790_);
lean_dec(v_inst_3789_);
lean_dec_ref(v_inst_3788_);
lean_dec_ref(v_a_3787_);
lean_inc_ref(v_res_3793_);
lean_inc(v_toPure_3782_);
v___f_3831_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3831_, 0, v_toPure_3782_);
lean_closure_set(v___f_3831_, 1, v_res_3793_);
lean_inc(v_toBind_3784_);
v___f_3832_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3832_, 0, v_inst_3783_);
lean_closure_set(v___f_3832_, 1, v_toBind_3784_);
lean_closure_set(v___f_3832_, 2, v___f_3831_);
v___x_3833_ = lean_box(0);
v___x_3834_ = lean_nat_dec_lt(v_zero_3795_, v___x_3794_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
lean_dec_ref(v_res_3793_);
lean_dec(v___f_3792_);
lean_dec_ref(v_inst_3785_);
v___x_3835_ = lean_apply_2(v_toPure_3782_, lean_box(0), v___x_3833_);
v___x_3836_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3835_, v___f_3832_);
return v___x_3836_;
}
else
{
uint8_t v___x_3837_; 
v___x_3837_ = lean_nat_dec_le(v___x_3794_, v___x_3794_);
if (v___x_3837_ == 0)
{
if (v___x_3834_ == 0)
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_dec_ref(v_res_3793_);
lean_dec(v___f_3792_);
lean_dec_ref(v_inst_3785_);
v___x_3838_ = lean_apply_2(v_toPure_3782_, lean_box(0), v___x_3833_);
v___x_3839_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3838_, v___f_3832_);
return v___x_3839_;
}
else
{
size_t v___x_3840_; size_t v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec(v_toPure_3782_);
v___x_3840_ = ((size_t)0ULL);
v___x_3841_ = lean_usize_of_nat(v___x_3794_);
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3785_, v___f_3792_, v_res_3793_, v___x_3840_, v___x_3841_, v___x_3833_);
v___x_3843_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3842_, v___f_3832_);
return v___x_3843_;
}
}
else
{
size_t v___x_3844_; size_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
lean_dec(v_toPure_3782_);
v___x_3844_ = ((size_t)0ULL);
v___x_3845_ = lean_usize_of_nat(v___x_3794_);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3785_, v___f_3792_, v_res_3793_, v___x_3844_, v___x_3845_, v___x_3833_);
v___x_3847_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3846_, v___f_3832_);
return v___x_3847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3848_, lean_object* v_toPure_3849_, lean_object* v_____do__lift_3850_){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = l_Array_append___redArg(v_bs_3848_, v_____do__lift_3850_);
v___x_3852_ = lean_apply_2(v_toPure_3849_, lean_box(0), v___x_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3853_, lean_object* v_toPure_3854_, lean_object* v_____do__lift_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3853_, v_toPure_3854_, v_____do__lift_3855_);
lean_dec_ref(v_____do__lift_3855_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3857_, lean_object* v_toPure_3858_, lean_object* v_toBind_3859_, lean_object* v_inst_3860_, lean_object* v_inst_3861_, lean_object* v_inst_3862_, lean_object* v_inst_3863_, lean_object* v_inst_3864_, lean_object* v_f_3865_, lean_object* v_bs_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v___f_3868_; lean_object* v___f_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
lean_inc(v_inst_3863_);
lean_inc_ref(v_inst_3862_);
lean_inc_ref(v_inst_3861_);
lean_inc_ref_n(v_a_3867_, 2);
lean_inc(v_inst_3860_);
lean_inc_n(v_toBind_3859_, 3);
lean_inc_n(v_toPure_3858_, 2);
lean_inc_ref(v_inst_3857_);
v___f_3868_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3868_, 0, v_inst_3857_);
lean_closure_set(v___f_3868_, 1, v_toPure_3858_);
lean_closure_set(v___f_3868_, 2, v_toBind_3859_);
lean_closure_set(v___f_3868_, 3, v_inst_3860_);
lean_closure_set(v___f_3868_, 4, v_a_3867_);
lean_closure_set(v___f_3868_, 5, v_inst_3861_);
lean_closure_set(v___f_3868_, 6, v_inst_3862_);
lean_closure_set(v___f_3868_, 7, v_inst_3863_);
lean_inc_ref(v___f_3868_);
v___f_3869_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3869_, 0, v_toPure_3858_);
lean_closure_set(v___f_3869_, 1, v_inst_3864_);
lean_closure_set(v___f_3869_, 2, v_toBind_3859_);
lean_closure_set(v___f_3869_, 3, v_inst_3861_);
lean_closure_set(v___f_3869_, 4, v___f_3868_);
lean_closure_set(v___f_3869_, 5, v_a_3867_);
lean_closure_set(v___f_3869_, 6, v_inst_3857_);
lean_closure_set(v___f_3869_, 7, v_inst_3860_);
lean_closure_set(v___f_3869_, 8, v_inst_3862_);
lean_closure_set(v___f_3869_, 9, v_inst_3863_);
lean_closure_set(v___f_3869_, 10, v___f_3868_);
v___f_3870_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3870_, 0, v_bs_3866_);
lean_closure_set(v___f_3870_, 1, v_toPure_3858_);
v___x_3871_ = lean_apply_1(v_f_3865_, v_a_3867_);
v___x_3872_ = lean_apply_4(v_toBind_3859_, lean_box(0), lean_box(0), v___x_3871_, v___f_3869_);
v___x_3873_ = lean_apply_4(v_toBind_3859_, lean_box(0), lean_box(0), v___x_3872_, v___f_3870_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3876_, lean_object* v_toPure_3877_, lean_object* v_toBind_3878_, lean_object* v___f_3879_, lean_object* v_inst_3880_, lean_object* v___f_3881_, lean_object* v_____r_3882_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; uint8_t v___x_3886_; 
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3885_ = lean_array_get_size(v_hyps_3876_);
v___x_3886_ = lean_nat_dec_lt(v___x_3883_, v___x_3885_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
lean_dec(v___f_3881_);
lean_dec_ref(v_inst_3880_);
lean_dec_ref(v_hyps_3876_);
v___x_3887_ = lean_apply_2(v_toPure_3877_, lean_box(0), v___x_3884_);
v___x_3888_ = lean_apply_4(v_toBind_3878_, lean_box(0), lean_box(0), v___x_3887_, v___f_3879_);
return v___x_3888_;
}
else
{
uint8_t v___x_3889_; 
v___x_3889_ = lean_nat_dec_le(v___x_3885_, v___x_3885_);
if (v___x_3889_ == 0)
{
if (v___x_3886_ == 0)
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_dec(v___f_3881_);
lean_dec_ref(v_inst_3880_);
lean_dec_ref(v_hyps_3876_);
v___x_3890_ = lean_apply_2(v_toPure_3877_, lean_box(0), v___x_3884_);
v___x_3891_ = lean_apply_4(v_toBind_3878_, lean_box(0), lean_box(0), v___x_3890_, v___f_3879_);
return v___x_3891_;
}
else
{
size_t v___x_3892_; size_t v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec(v_toPure_3877_);
v___x_3892_ = ((size_t)0ULL);
v___x_3893_ = lean_usize_of_nat(v___x_3885_);
v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3880_, v___f_3881_, v_hyps_3876_, v___x_3892_, v___x_3893_, v___x_3884_);
v___x_3895_ = lean_apply_4(v_toBind_3878_, lean_box(0), lean_box(0), v___x_3894_, v___f_3879_);
return v___x_3895_;
}
}
else
{
size_t v___x_3896_; size_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec(v_toPure_3877_);
v___x_3896_ = ((size_t)0ULL);
v___x_3897_ = lean_usize_of_nat(v___x_3885_);
v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3880_, v___f_3881_, v_hyps_3876_, v___x_3896_, v___x_3897_, v___x_3884_);
v___x_3899_ = lean_apply_4(v_toBind_3878_, lean_box(0), lean_box(0), v___x_3898_, v___f_3879_);
return v___x_3899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3900_, lean_object* v_toBind_3901_, lean_object* v___f_3902_, lean_object* v_inst_3903_, lean_object* v___f_3904_, lean_object* v_inst_3905_, lean_object* v___f_3906_, lean_object* v_hyps_3907_){
_start:
{
lean_object* v___f_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_inc(v_toBind_3901_);
v___f_3908_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3908_, 0, v_hyps_3907_);
lean_closure_set(v___f_3908_, 1, v_toPure_3900_);
lean_closure_set(v___f_3908_, 2, v_toBind_3901_);
lean_closure_set(v___f_3908_, 3, v___f_3902_);
lean_closure_set(v___f_3908_, 4, v_inst_3903_);
lean_closure_set(v___f_3908_, 5, v___f_3904_);
v___x_3909_ = lean_apply_2(v_inst_3905_, lean_box(0), v___f_3906_);
v___x_3910_ = lean_apply_4(v_toBind_3901_, lean_box(0), lean_box(0), v___x_3909_, v___f_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3912_, lean_object* v_inst_3913_, lean_object* v_inst_3914_, lean_object* v_inst_3915_, lean_object* v_inst_3916_, lean_object* v_inst_3917_, lean_object* v_f_3918_){
_start:
{
lean_object* v_toApplicative_3919_; lean_object* v_toBind_3920_; lean_object* v_toPure_3921_; lean_object* v___f_3922_; lean_object* v___f_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___f_3926_; lean_object* v___f_3927_; lean_object* v___x_3928_; 
v_toApplicative_3919_ = lean_ctor_get(v_inst_3912_, 0);
v_toBind_3920_ = lean_ctor_get(v_inst_3912_, 1);
lean_inc_n(v_toBind_3920_, 3);
v_toPure_3921_ = lean_ctor_get(v_toApplicative_3919_, 1);
lean_inc_n(v_toPure_3921_, 2);
lean_inc_n(v_inst_3917_, 3);
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3922_, 0, v_inst_3917_);
v___f_3923_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3924_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3925_ = lean_apply_2(v_inst_3917_, lean_box(0), v___x_3924_);
lean_inc_ref(v_inst_3912_);
v___f_3926_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3926_, 0, v_inst_3913_);
lean_closure_set(v___f_3926_, 1, v_toPure_3921_);
lean_closure_set(v___f_3926_, 2, v_toBind_3920_);
lean_closure_set(v___f_3926_, 3, v_inst_3914_);
lean_closure_set(v___f_3926_, 4, v_inst_3912_);
lean_closure_set(v___f_3926_, 5, v_inst_3916_);
lean_closure_set(v___f_3926_, 6, v_inst_3915_);
lean_closure_set(v___f_3926_, 7, v_inst_3917_);
lean_closure_set(v___f_3926_, 8, v_f_3918_);
v___f_3927_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3927_, 0, v_toPure_3921_);
lean_closure_set(v___f_3927_, 1, v_toBind_3920_);
lean_closure_set(v___f_3927_, 2, v___f_3922_);
lean_closure_set(v___f_3927_, 3, v_inst_3912_);
lean_closure_set(v___f_3927_, 4, v___f_3926_);
lean_closure_set(v___f_3927_, 5, v_inst_3917_);
lean_closure_set(v___f_3927_, 6, v___f_3923_);
v___x_3928_ = lean_apply_4(v_toBind_3920_, lean_box(0), lean_box(0), v___x_3925_, v___f_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3929_, lean_object* v_inst_3930_, lean_object* v_inst_3931_, lean_object* v_inst_3932_, lean_object* v_inst_3933_, lean_object* v_inst_3934_, lean_object* v_inst_3935_, lean_object* v_f_3936_){
_start:
{
lean_object* v_toApplicative_3937_; lean_object* v_toBind_3938_; lean_object* v_toPure_3939_; lean_object* v___f_3940_; lean_object* v___f_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___f_3944_; lean_object* v___f_3945_; lean_object* v___x_3946_; 
v_toApplicative_3937_ = lean_ctor_get(v_inst_3930_, 0);
v_toBind_3938_ = lean_ctor_get(v_inst_3930_, 1);
lean_inc_n(v_toBind_3938_, 3);
v_toPure_3939_ = lean_ctor_get(v_toApplicative_3937_, 1);
lean_inc_n(v_toPure_3939_, 2);
lean_inc_n(v_inst_3935_, 3);
v___f_3940_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3940_, 0, v_inst_3935_);
v___f_3941_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3942_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3943_ = lean_apply_2(v_inst_3935_, lean_box(0), v___x_3942_);
lean_inc_ref(v_inst_3930_);
v___f_3944_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3944_, 0, v_inst_3931_);
lean_closure_set(v___f_3944_, 1, v_toPure_3939_);
lean_closure_set(v___f_3944_, 2, v_toBind_3938_);
lean_closure_set(v___f_3944_, 3, v_inst_3932_);
lean_closure_set(v___f_3944_, 4, v_inst_3930_);
lean_closure_set(v___f_3944_, 5, v_inst_3934_);
lean_closure_set(v___f_3944_, 6, v_inst_3933_);
lean_closure_set(v___f_3944_, 7, v_inst_3935_);
lean_closure_set(v___f_3944_, 8, v_f_3936_);
v___f_3945_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3945_, 0, v_toPure_3939_);
lean_closure_set(v___f_3945_, 1, v_toBind_3938_);
lean_closure_set(v___f_3945_, 2, v___f_3940_);
lean_closure_set(v___f_3945_, 3, v_inst_3930_);
lean_closure_set(v___f_3945_, 4, v___f_3944_);
lean_closure_set(v___f_3945_, 5, v_inst_3935_);
lean_closure_set(v___f_3945_, 6, v___f_3941_);
v___x_3946_ = lean_apply_4(v_toBind_3938_, lean_box(0), lean_box(0), v___x_3943_, v___f_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3947_, lean_object* v_____do__lift_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_apply_2(v_toPure_3947_, lean_box(0), v_____do__lift_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_toPure_3950_, lean_object* v_____r_3951_){
_start:
{
uint8_t v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = 0;
v___x_3953_ = lean_box(v___x_3952_);
v___x_3954_ = lean_apply_2(v_toPure_3950_, lean_box(0), v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_snd_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v___x_3968_; lean_object* v_caches_3969_; lean_object* v_typeAnalysis_3970_; lean_object* v_target_3971_; uint8_t v_didChange_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3982_; 
v___x_3968_ = lean_st_ref_take(v___y_3957_);
v_caches_3969_ = lean_ctor_get(v___x_3968_, 0);
v_typeAnalysis_3970_ = lean_ctor_get(v___x_3968_, 1);
v_target_3971_ = lean_ctor_get(v___x_3968_, 2);
v_didChange_3972_ = lean_ctor_get_uint8(v___x_3968_, sizeof(void*)*4);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; 
v_unused_3983_ = lean_ctor_get(v___x_3968_, 3);
lean_dec(v_unused_3983_);
v___x_3974_ = v___x_3968_;
v_isShared_3975_ = v_isSharedCheck_3982_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_target_3971_);
lean_inc(v_typeAnalysis_3970_);
lean_inc(v_caches_3969_);
lean_dec(v___x_3968_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3982_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 3, v_snd_3955_);
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_caches_3969_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_typeAnalysis_3970_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_target_3971_);
lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_snd_3955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3981_, sizeof(void*)*4, v_didChange_3972_);
v___x_3977_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = lean_st_ref_put(v___y_3957_, v___x_3977_);
v___x_3979_ = lean_box(0);
v___x_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object* v_snd_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(v_snd_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_inst_3998_, lean_object* v_toBind_3999_, lean_object* v___f_4000_, lean_object* v_toPure_4001_, lean_object* v_____s_4002_){
_start:
{
lean_object* v_fst_4003_; 
v_fst_4003_ = lean_ctor_get(v_____s_4002_, 0);
if (lean_obj_tag(v_fst_4003_) == 0)
{
lean_object* v_snd_4004_; lean_object* v___f_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_dec(v_toPure_4001_);
v_snd_4004_ = lean_ctor_get(v_____s_4002_, 1);
lean_inc(v_snd_4004_);
lean_dec_ref(v_____s_4002_);
v___f_4005_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed), 13, 1);
lean_closure_set(v___f_4005_, 0, v_snd_4004_);
v___x_4006_ = lean_apply_2(v_inst_3998_, lean_box(0), v___f_4005_);
v___x_4007_ = lean_apply_4(v_toBind_3999_, lean_box(0), lean_box(0), v___x_4006_, v___f_4000_);
return v___x_4007_;
}
else
{
lean_object* v_val_4008_; lean_object* v___x_4009_; 
lean_inc_ref(v_fst_4003_);
lean_dec_ref(v_____s_4002_);
lean_dec(v___f_4000_);
lean_dec(v_toBind_3999_);
lean_dec(v_inst_3998_);
v_val_4008_ = lean_ctor_get(v_fst_4003_, 0);
lean_inc(v_val_4008_);
lean_dec_ref_known(v_fst_4003_, 1);
v___x_4009_ = lean_apply_2(v_toPure_4001_, lean_box(0), v_val_4008_);
return v___x_4009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_4010_, lean_object* v_next_4011_, lean_object* v_G_4012_, lean_object* v_____do__lift_4013_){
_start:
{
if (lean_obj_tag(v_____do__lift_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; 
lean_dec(v_G_4012_);
v_a_4014_ = lean_ctor_get(v_____do__lift_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref_known(v_____do__lift_4013_, 1);
v___x_4015_ = lean_apply_2(v_toPure_4010_, lean_box(0), v_a_4014_);
return v___x_4015_;
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec(v_toPure_4010_);
v_a_4016_ = lean_ctor_get(v_____do__lift_4013_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v_____do__lift_4013_, 1);
v___x_4017_ = lean_unsigned_to_nat(1u);
v___x_4018_ = lean_nat_add(v_next_4011_, v___x_4017_);
v___x_4019_ = lean_apply_4(v_G_4012_, v___x_4018_, v_a_4016_, lean_box(0), lean_box(0));
return v___x_4019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_4020_, lean_object* v_next_4021_, lean_object* v_G_4022_, lean_object* v_____do__lift_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_4020_, v_next_4021_, v_G_4022_, v_____do__lift_4023_);
lean_dec(v_next_4021_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(lean_object* v_snd_4025_, lean_object* v_newHyp_4026_, lean_object* v___x_4027_, lean_object* v_toPure_4028_, lean_object* v_____r_4029_){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4030_ = lean_array_push(v_snd_4025_, v_newHyp_4026_);
v___x_4031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4027_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
v___x_4033_ = lean_apply_2(v_toPure_4028_, lean_box(0), v___x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v_toPure_4034_, lean_object* v___x_4035_, lean_object* v_____do__lift_4036_, lean_object* v_____do__lift_4037_){
_start:
{
uint8_t v_hasTrace_4038_; 
v_hasTrace_4038_ = lean_ctor_get_uint8(v_____do__lift_4037_, sizeof(void*)*1);
if (v_hasTrace_4038_ == 0)
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
lean_dec(v___x_4035_);
v___x_4039_ = lean_box(v_hasTrace_4038_);
v___x_4040_ = lean_apply_2(v_toPure_4034_, lean_box(0), v___x_4039_);
return v___x_4040_;
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4041_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16));
v___x_4042_ = l_Lean_Name_append(v___x_4041_, v___x_4035_);
v___x_4043_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_4036_, v_____do__lift_4037_, v___x_4042_);
lean_dec(v___x_4042_);
v___x_4044_ = lean_box(v___x_4043_);
v___x_4045_ = lean_apply_2(v_toPure_4034_, lean_box(0), v___x_4044_);
return v___x_4045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed(lean_object* v_toPure_4046_, lean_object* v___x_4047_, lean_object* v_____do__lift_4048_, lean_object* v_____do__lift_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(v_toPure_4046_, v___x_4047_, v_____do__lift_4048_, v_____do__lift_4049_);
lean_dec_ref(v_____do__lift_4049_);
lean_dec_ref(v_____do__lift_4048_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_toPure_4051_, lean_object* v___x_4052_, lean_object* v_toBind_4053_, lean_object* v_inst_4054_, lean_object* v_____do__lift_4055_){
_start:
{
lean_object* v___f_4056_; lean_object* v___x_4057_; 
v___f_4056_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed), 4, 3);
lean_closure_set(v___f_4056_, 0, v_toPure_4051_);
lean_closure_set(v___f_4056_, 1, v___x_4052_);
lean_closure_set(v___f_4056_, 2, v_____do__lift_4055_);
v___x_4057_ = lean_apply_4(v_toBind_4053_, lean_box(0), lean_box(0), v_inst_4054_, v___f_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v___f_4058_, lean_object* v_inst_4059_, lean_object* v___x_4060_, lean_object* v_type_4061_, lean_object* v_inst_4062_, lean_object* v_inst_4063_, lean_object* v_inst_4064_, lean_object* v___x_4065_, lean_object* v_toBind_4066_, lean_object* v___f_4067_, uint8_t v_____do__lift_4068_){
_start:
{
if (v_____do__lift_4068_ == 0)
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
lean_dec(v___f_4067_);
lean_dec(v_toBind_4066_);
lean_dec(v___x_4065_);
lean_dec(v_inst_4064_);
lean_dec_ref(v_inst_4063_);
lean_dec_ref(v_inst_4062_);
lean_dec_ref(v_type_4061_);
lean_dec_ref(v___x_4060_);
lean_dec_ref(v_inst_4059_);
v___x_4069_ = lean_box(0);
v___x_4070_ = lean_apply_1(v___f_4058_, v___x_4069_);
return v___x_4070_;
}
else
{
lean_object* v_toMonadRef_4071_; lean_object* v_type_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec(v___f_4058_);
v_toMonadRef_4071_ = lean_ctor_get(v_inst_4059_, 1);
lean_inc_ref(v_toMonadRef_4071_);
lean_dec_ref(v_inst_4059_);
v_type_4072_ = lean_ctor_get(v___x_4060_, 1);
lean_inc_ref(v_type_4072_);
lean_dec_ref(v___x_4060_);
v___x_4073_ = l_Lean_MessageData_ofExpr(v_type_4072_);
v___x_4074_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4073_);
lean_ctor_set(v___x_4075_, 1, v___x_4074_);
v___x_4076_ = l_Lean_MessageData_ofExpr(v_type_4061_);
v___x_4077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4075_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = l_Lean_addTrace___redArg(v_inst_4062_, v_inst_4063_, v_toMonadRef_4071_, v_inst_4064_, v___x_4065_, v___x_4077_);
v___x_4079_ = lean_apply_4(v_toBind_4066_, lean_box(0), lean_box(0), v___x_4078_, v___f_4067_);
return v___x_4079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed(lean_object* v___f_4080_, lean_object* v_inst_4081_, lean_object* v___x_4082_, lean_object* v_type_4083_, lean_object* v_inst_4084_, lean_object* v_inst_4085_, lean_object* v_inst_4086_, lean_object* v___x_4087_, lean_object* v_toBind_4088_, lean_object* v___f_4089_, lean_object* v_____do__lift_4090_){
_start:
{
uint8_t v_____do__lift_2106__boxed_4091_; lean_object* v_res_4092_; 
v_____do__lift_2106__boxed_4091_ = lean_unbox(v_____do__lift_4090_);
v_res_4092_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(v___f_4080_, v_inst_4081_, v___x_4082_, v_type_4083_, v_inst_4084_, v_inst_4085_, v_inst_4086_, v___x_4087_, v_toBind_4088_, v___f_4089_, v_____do__lift_2106__boxed_4091_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(uint8_t v___x_4093_, lean_object* v_snd_4094_, lean_object* v_toPure_4095_, lean_object* v_____r_4096_){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4097_ = lean_box(v___x_4093_);
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
lean_ctor_set(v___x_4099_, 1, v_snd_4094_);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
v___x_4101_ = lean_apply_2(v_toPure_4095_, lean_box(0), v___x_4100_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___x_4102_, lean_object* v_snd_4103_, lean_object* v_toPure_4104_, lean_object* v_____r_4105_){
_start:
{
uint8_t v___x_2144__boxed_4106_; lean_object* v_res_4107_; 
v___x_2144__boxed_4106_ = lean_unbox(v___x_4102_);
v_res_4107_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___x_2144__boxed_4106_, v_snd_4103_, v_toPure_4104_, v_____r_4105_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v___x_4108_, lean_object* v_snd_4109_, lean_object* v___x_4110_, lean_object* v_toPure_4111_, lean_object* v_inst_4112_, lean_object* v_toBind_4113_, lean_object* v_inst_4114_, lean_object* v_inst_4115_, lean_object* v_inst_4116_, lean_object* v_inst_4117_, lean_object* v_inst_4118_, lean_object* v_newHyp_4119_){
_start:
{
lean_object* v_type_4120_; lean_object* v_value_4121_; uint8_t v___x_4122_; 
v_type_4120_ = lean_ctor_get(v_newHyp_4119_, 1);
v_value_4121_ = lean_ctor_get(v_newHyp_4119_, 2);
lean_inc_ref(v_type_4120_);
v___x_4122_ = l_Lean_Expr_isFalse(v_type_4120_);
if (v___x_4122_ == 0)
{
lean_object* v_type_4123_; lean_object* v___f_4124_; lean_object* v___f_4125_; lean_object* v___f_4126_; lean_object* v___f_4127_; uint8_t v___x_4135_; 
v_type_4123_ = lean_ctor_get(v___x_4108_, 1);
lean_inc(v_toPure_4111_);
lean_inc(v___x_4110_);
lean_inc_ref(v_newHyp_4119_);
lean_inc(v_snd_4109_);
v___f_4124_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_4124_, 0, v_snd_4109_);
lean_closure_set(v___f_4124_, 1, v_newHyp_4119_);
lean_closure_set(v___f_4124_, 2, v___x_4110_);
lean_closure_set(v___f_4124_, 3, v_toPure_4111_);
v___f_4125_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_4125_, 0, v___f_4124_);
lean_inc(v_toBind_4113_);
v___f_4126_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_4126_, 0, v_inst_4112_);
lean_closure_set(v___f_4126_, 1, v_toBind_4113_);
lean_closure_set(v___f_4126_, 2, v___f_4125_);
lean_inc_ref(v___f_4126_);
v___f_4127_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_4127_, 0, v___f_4126_);
v___x_4135_ = lean_expr_eqv(v_type_4123_, v_type_4120_);
if (v___x_4135_ == 0)
{
lean_inc_ref(v_type_4120_);
lean_dec_ref(v_newHyp_4119_);
lean_dec(v___x_4110_);
lean_dec(v_snd_4109_);
goto v___jp_4128_;
}
else
{
if (v___x_4122_ == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
lean_dec_ref(v___f_4127_);
lean_dec_ref(v___f_4126_);
lean_dec(v_inst_4118_);
lean_dec_ref(v_inst_4117_);
lean_dec_ref(v_inst_4116_);
lean_dec(v_inst_4115_);
lean_dec_ref(v_inst_4114_);
lean_dec(v_toBind_4113_);
lean_dec_ref(v___x_4108_);
v___x_4136_ = lean_box(0);
v___x_4137_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_4109_, v_newHyp_4119_, v___x_4110_, v_toPure_4111_, v___x_4136_);
return v___x_4137_;
}
else
{
lean_inc_ref(v_type_4120_);
lean_dec_ref(v_newHyp_4119_);
lean_dec(v___x_4110_);
lean_dec(v_snd_4109_);
goto v___jp_4128_;
}
}
v___jp_4128_:
{
lean_object* v_getInheritedTraceOptions_4129_; lean_object* v___x_4130_; lean_object* v___f_4131_; lean_object* v___f_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_getInheritedTraceOptions_4129_ = lean_ctor_get(v_inst_4114_, 2);
lean_inc(v_getInheritedTraceOptions_4129_);
v___x_4130_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
lean_inc_n(v_toBind_4113_, 3);
v___f_4131_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_4131_, 0, v_toPure_4111_);
lean_closure_set(v___f_4131_, 1, v___x_4130_);
lean_closure_set(v___f_4131_, 2, v_toBind_4113_);
lean_closure_set(v___f_4131_, 3, v_inst_4115_);
v___f_4132_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_4132_, 0, v___f_4126_);
lean_closure_set(v___f_4132_, 1, v_inst_4116_);
lean_closure_set(v___f_4132_, 2, v___x_4108_);
lean_closure_set(v___f_4132_, 3, v_type_4120_);
lean_closure_set(v___f_4132_, 4, v_inst_4117_);
lean_closure_set(v___f_4132_, 5, v_inst_4114_);
lean_closure_set(v___f_4132_, 6, v_inst_4118_);
lean_closure_set(v___f_4132_, 7, v___x_4130_);
lean_closure_set(v___f_4132_, 8, v_toBind_4113_);
lean_closure_set(v___f_4132_, 9, v___f_4127_);
v___x_4133_ = lean_apply_4(v_toBind_4113_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_4129_, v___f_4131_);
v___x_4134_ = lean_apply_4(v_toBind_4113_, lean_box(0), lean_box(0), v___x_4133_, v___f_4132_);
return v___x_4134_;
}
}
else
{
lean_object* v___x_4138_; lean_object* v___f_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_inc_ref(v_value_4121_);
lean_dec_ref(v_newHyp_4119_);
lean_dec(v_inst_4118_);
lean_dec_ref(v_inst_4117_);
lean_dec_ref(v_inst_4116_);
lean_dec(v_inst_4115_);
lean_dec_ref(v_inst_4114_);
lean_dec(v___x_4110_);
lean_dec_ref(v___x_4108_);
v___x_4138_ = lean_box(v___x_4122_);
v___f_4139_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_4139_, 0, v___x_4138_);
lean_closure_set(v___f_4139_, 1, v_snd_4109_);
lean_closure_set(v___f_4139_, 2, v_toPure_4111_);
v___x_4140_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_4140_, 0, v_value_4121_);
v___x_4141_ = lean_apply_2(v_inst_4112_, lean_box(0), v___x_4140_);
v___x_4142_ = lean_apply_4(v_toBind_4113_, lean_box(0), lean_box(0), v___x_4141_, v___f_4139_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_4143_, lean_object* v_toPure_4144_, lean_object* v_hyps_4145_, lean_object* v___x_4146_, lean_object* v_inst_4147_, lean_object* v_toBind_4148_, lean_object* v_inst_4149_, lean_object* v_inst_4150_, lean_object* v_inst_4151_, lean_object* v_inst_4152_, lean_object* v_inst_4153_, lean_object* v_f_4154_, lean_object* v___f_4155_, lean_object* v_next_4156_, lean_object* v_acc_4157_, lean_object* v_h_4158_, lean_object* v_G_4159_){
_start:
{
uint8_t v___x_4160_; 
v___x_4160_ = lean_nat_dec_lt(v_next_4156_, v___x_4143_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4161_; 
lean_dec(v_G_4159_);
lean_dec(v_next_4156_);
lean_dec(v___f_4155_);
lean_dec(v_f_4154_);
lean_dec(v_inst_4153_);
lean_dec_ref(v_inst_4152_);
lean_dec_ref(v_inst_4151_);
lean_dec(v_inst_4150_);
lean_dec_ref(v_inst_4149_);
lean_dec(v_toBind_4148_);
lean_dec(v_inst_4147_);
lean_dec(v___x_4146_);
v___x_4161_ = lean_apply_2(v_toPure_4144_, lean_box(0), v_acc_4157_);
return v___x_4161_;
}
else
{
lean_object* v_snd_4162_; lean_object* v___f_4163_; lean_object* v___x_4164_; lean_object* v___f_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v_snd_4162_ = lean_ctor_get(v_acc_4157_, 1);
lean_inc(v_snd_4162_);
lean_dec_ref(v_acc_4157_);
lean_inc(v_next_4156_);
lean_inc(v_toPure_4144_);
v___f_4163_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_4163_, 0, v_toPure_4144_);
lean_closure_set(v___f_4163_, 1, v_next_4156_);
lean_closure_set(v___f_4163_, 2, v_G_4159_);
v___x_4164_ = lean_array_fget_borrowed(v_hyps_4145_, v_next_4156_);
lean_inc_n(v_toBind_4148_, 3);
lean_inc_n(v___x_4164_, 2);
v___f_4165_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10), 12, 11);
lean_closure_set(v___f_4165_, 0, v___x_4164_);
lean_closure_set(v___f_4165_, 1, v_snd_4162_);
lean_closure_set(v___f_4165_, 2, v___x_4146_);
lean_closure_set(v___f_4165_, 3, v_toPure_4144_);
lean_closure_set(v___f_4165_, 4, v_inst_4147_);
lean_closure_set(v___f_4165_, 5, v_toBind_4148_);
lean_closure_set(v___f_4165_, 6, v_inst_4149_);
lean_closure_set(v___f_4165_, 7, v_inst_4150_);
lean_closure_set(v___f_4165_, 8, v_inst_4151_);
lean_closure_set(v___f_4165_, 9, v_inst_4152_);
lean_closure_set(v___f_4165_, 10, v_inst_4153_);
v___x_4166_ = lean_apply_2(v_f_4154_, v_next_4156_, v___x_4164_);
v___x_4167_ = lean_apply_4(v_toBind_4148_, lean_box(0), lean_box(0), v___x_4166_, v___f_4165_);
v___x_4168_ = lean_apply_4(v_toBind_4148_, lean_box(0), lean_box(0), v___x_4167_, v___f_4155_);
v___x_4169_ = lean_apply_4(v_toBind_4148_, lean_box(0), lean_box(0), v___x_4168_, v___f_4163_);
return v___x_4169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_4170_ = _args[0];
lean_object* v_toPure_4171_ = _args[1];
lean_object* v_hyps_4172_ = _args[2];
lean_object* v___x_4173_ = _args[3];
lean_object* v_inst_4174_ = _args[4];
lean_object* v_toBind_4175_ = _args[5];
lean_object* v_inst_4176_ = _args[6];
lean_object* v_inst_4177_ = _args[7];
lean_object* v_inst_4178_ = _args[8];
lean_object* v_inst_4179_ = _args[9];
lean_object* v_inst_4180_ = _args[10];
lean_object* v_f_4181_ = _args[11];
lean_object* v___f_4182_ = _args[12];
lean_object* v_next_4183_ = _args[13];
lean_object* v_acc_4184_ = _args[14];
lean_object* v_h_4185_ = _args[15];
lean_object* v_G_4186_ = _args[16];
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_4170_, v_toPure_4171_, v_hyps_4172_, v___x_4173_, v_inst_4174_, v_toBind_4175_, v_inst_4176_, v_inst_4177_, v_inst_4178_, v_inst_4179_, v_inst_4180_, v_f_4181_, v___f_4182_, v_next_4183_, v_acc_4184_, v_h_4185_, v_G_4186_);
lean_dec_ref(v_hyps_4172_);
lean_dec(v___x_4170_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_4188_, lean_object* v_inst_4189_, lean_object* v_toBind_4190_, lean_object* v_inst_4191_, lean_object* v_inst_4192_, lean_object* v_inst_4193_, lean_object* v_inst_4194_, lean_object* v_inst_4195_, lean_object* v_f_4196_, lean_object* v___f_4197_, lean_object* v___f_4198_, lean_object* v_hyps_4199_){
_start:
{
lean_object* v___x_4200_; lean_object* v_newHyps_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___f_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4200_ = lean_array_get_size(v_hyps_4199_);
v_newHyps_4201_ = lean_mk_empty_array_with_capacity(v___x_4200_);
v___x_4202_ = lean_unsigned_to_nat(0u);
v___x_4203_ = lean_box(0);
lean_inc(v_toBind_4190_);
v___f_4204_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_4204_, 0, v___x_4200_);
lean_closure_set(v___f_4204_, 1, v_toPure_4188_);
lean_closure_set(v___f_4204_, 2, v_hyps_4199_);
lean_closure_set(v___f_4204_, 3, v___x_4203_);
lean_closure_set(v___f_4204_, 4, v_inst_4189_);
lean_closure_set(v___f_4204_, 5, v_toBind_4190_);
lean_closure_set(v___f_4204_, 6, v_inst_4191_);
lean_closure_set(v___f_4204_, 7, v_inst_4192_);
lean_closure_set(v___f_4204_, 8, v_inst_4193_);
lean_closure_set(v___f_4204_, 9, v_inst_4194_);
lean_closure_set(v___f_4204_, 10, v_inst_4195_);
lean_closure_set(v___f_4204_, 11, v_f_4196_);
lean_closure_set(v___f_4204_, 12, v___f_4197_);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4203_);
lean_ctor_set(v___x_4205_, 1, v_newHyps_4201_);
v___x_4206_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4204_, v___x_4202_, v___x_4205_, lean_box(0));
v___x_4207_ = lean_apply_4(v_toBind_4190_, lean_box(0), lean_box(0), v___x_4206_, v___f_4198_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_4208_, lean_object* v_inst_4209_, lean_object* v_inst_4210_, lean_object* v_inst_4211_, lean_object* v_inst_4212_, lean_object* v_inst_4213_, lean_object* v_f_4214_){
_start:
{
lean_object* v_toApplicative_4215_; lean_object* v_toBind_4216_; lean_object* v_toPure_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___f_4220_; lean_object* v___f_4221_; lean_object* v___f_4222_; lean_object* v___f_4223_; lean_object* v___x_4224_; 
v_toApplicative_4215_ = lean_ctor_get(v_inst_4208_, 0);
v_toBind_4216_ = lean_ctor_get(v_inst_4208_, 1);
lean_inc_n(v_toBind_4216_, 3);
v_toPure_4217_ = lean_ctor_get(v_toApplicative_4215_, 1);
lean_inc_n(v_toPure_4217_, 4);
v___x_4218_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_4209_, 2);
v___x_4219_ = lean_apply_2(v_inst_4209_, lean_box(0), v___x_4218_);
v___f_4220_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4220_, 0, v_toPure_4217_);
v___f_4221_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4221_, 0, v_toPure_4217_);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_4222_, 0, v_inst_4209_);
lean_closure_set(v___f_4222_, 1, v_toBind_4216_);
lean_closure_set(v___f_4222_, 2, v___f_4221_);
lean_closure_set(v___f_4222_, 3, v_toPure_4217_);
v___f_4223_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_4223_, 0, v_toPure_4217_);
lean_closure_set(v___f_4223_, 1, v_inst_4209_);
lean_closure_set(v___f_4223_, 2, v_toBind_4216_);
lean_closure_set(v___f_4223_, 3, v_inst_4211_);
lean_closure_set(v___f_4223_, 4, v_inst_4212_);
lean_closure_set(v___f_4223_, 5, v_inst_4210_);
lean_closure_set(v___f_4223_, 6, v_inst_4208_);
lean_closure_set(v___f_4223_, 7, v_inst_4213_);
lean_closure_set(v___f_4223_, 8, v_f_4214_);
lean_closure_set(v___f_4223_, 9, v___f_4220_);
lean_closure_set(v___f_4223_, 10, v___f_4222_);
v___x_4224_ = lean_apply_4(v_toBind_4216_, lean_box(0), lean_box(0), v___x_4219_, v___f_4223_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_4225_, lean_object* v_inst_4226_, lean_object* v_inst_4227_, lean_object* v_inst_4228_, lean_object* v_inst_4229_, lean_object* v_inst_4230_, lean_object* v_inst_4231_, lean_object* v_inst_4232_, lean_object* v_inst_4233_, lean_object* v_f_4234_){
_start:
{
lean_object* v_toApplicative_4235_; lean_object* v_toBind_4236_; lean_object* v_toPure_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___f_4240_; lean_object* v___f_4241_; lean_object* v___f_4242_; lean_object* v___f_4243_; lean_object* v___x_4244_; 
v_toApplicative_4235_ = lean_ctor_get(v_inst_4226_, 0);
v_toBind_4236_ = lean_ctor_get(v_inst_4226_, 1);
lean_inc_n(v_toBind_4236_, 3);
v_toPure_4237_ = lean_ctor_get(v_toApplicative_4235_, 1);
lean_inc_n(v_toPure_4237_, 4);
v___x_4238_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_4227_, 2);
v___x_4239_ = lean_apply_2(v_inst_4227_, lean_box(0), v___x_4238_);
v___f_4240_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4240_, 0, v_toPure_4237_);
v___f_4241_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4241_, 0, v_toPure_4237_);
v___f_4242_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_4242_, 0, v_inst_4227_);
lean_closure_set(v___f_4242_, 1, v_toBind_4236_);
lean_closure_set(v___f_4242_, 2, v___f_4241_);
lean_closure_set(v___f_4242_, 3, v_toPure_4237_);
v___f_4243_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_4243_, 0, v_toPure_4237_);
lean_closure_set(v___f_4243_, 1, v_inst_4227_);
lean_closure_set(v___f_4243_, 2, v_toBind_4236_);
lean_closure_set(v___f_4243_, 3, v_inst_4230_);
lean_closure_set(v___f_4243_, 4, v_inst_4231_);
lean_closure_set(v___f_4243_, 5, v_inst_4228_);
lean_closure_set(v___f_4243_, 6, v_inst_4226_);
lean_closure_set(v___f_4243_, 7, v_inst_4232_);
lean_closure_set(v___f_4243_, 8, v_f_4234_);
lean_closure_set(v___f_4243_, 9, v___f_4240_);
lean_closure_set(v___f_4243_, 10, v___f_4242_);
v___x_4244_ = lean_apply_4(v_toBind_4236_, lean_box(0), lean_box(0), v___x_4239_, v___f_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_4245_, lean_object* v_inst_4246_, lean_object* v_inst_4247_, lean_object* v_inst_4248_, lean_object* v_inst_4249_, lean_object* v_inst_4250_, lean_object* v_inst_4251_, lean_object* v_inst_4252_, lean_object* v_inst_4253_, lean_object* v_f_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_4245_, v_inst_4246_, v_inst_4247_, v_inst_4248_, v_inst_4249_, v_inst_4250_, v_inst_4251_, v_inst_4252_, v_inst_4253_, v_f_4254_);
lean_dec_ref(v_inst_4253_);
lean_dec_ref(v_inst_4249_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_4256_, lean_object* v_snd_4257_, lean_object* v___x_4258_, lean_object* v_toPure_4259_, lean_object* v_inst_4260_, lean_object* v_toBind_4261_, lean_object* v_inst_4262_, lean_object* v_inst_4263_, lean_object* v_inst_4264_, lean_object* v_inst_4265_, lean_object* v_inst_4266_, lean_object* v_newHyp_4267_){
_start:
{
lean_object* v_type_4268_; lean_object* v_value_4269_; uint8_t v___x_4270_; 
v_type_4268_ = lean_ctor_get(v_newHyp_4267_, 1);
v_value_4269_ = lean_ctor_get(v_newHyp_4267_, 2);
lean_inc_ref(v_type_4268_);
v___x_4270_ = l_Lean_Expr_isFalse(v_type_4268_);
if (v___x_4270_ == 0)
{
lean_object* v_type_4271_; lean_object* v___f_4272_; lean_object* v___f_4273_; lean_object* v___f_4274_; lean_object* v___f_4275_; uint8_t v___x_4283_; 
v_type_4271_ = lean_ctor_get(v___x_4256_, 1);
lean_inc(v_toPure_4259_);
lean_inc(v___x_4258_);
lean_inc_ref(v_newHyp_4267_);
lean_inc(v_snd_4257_);
v___f_4272_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_4272_, 0, v_snd_4257_);
lean_closure_set(v___f_4272_, 1, v_newHyp_4267_);
lean_closure_set(v___f_4272_, 2, v___x_4258_);
lean_closure_set(v___f_4272_, 3, v_toPure_4259_);
v___f_4273_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_4273_, 0, v___f_4272_);
lean_inc(v_toBind_4261_);
v___f_4274_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_4274_, 0, v_inst_4260_);
lean_closure_set(v___f_4274_, 1, v_toBind_4261_);
lean_closure_set(v___f_4274_, 2, v___f_4273_);
lean_inc_ref(v___f_4274_);
v___f_4275_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_4275_, 0, v___f_4274_);
v___x_4283_ = lean_expr_eqv(v_type_4271_, v_type_4268_);
if (v___x_4283_ == 0)
{
lean_inc_ref(v_type_4268_);
lean_dec_ref(v_newHyp_4267_);
lean_dec(v___x_4258_);
lean_dec(v_snd_4257_);
goto v___jp_4276_;
}
else
{
if (v___x_4270_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
lean_dec_ref(v___f_4275_);
lean_dec_ref(v___f_4274_);
lean_dec(v_inst_4266_);
lean_dec(v_inst_4265_);
lean_dec_ref(v_inst_4264_);
lean_dec_ref(v_inst_4263_);
lean_dec_ref(v_inst_4262_);
lean_dec(v_toBind_4261_);
lean_dec_ref(v___x_4256_);
v___x_4284_ = lean_box(0);
v___x_4285_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_4257_, v_newHyp_4267_, v___x_4258_, v_toPure_4259_, v___x_4284_);
return v___x_4285_;
}
else
{
lean_inc_ref(v_type_4268_);
lean_dec_ref(v_newHyp_4267_);
lean_dec(v___x_4258_);
lean_dec(v_snd_4257_);
goto v___jp_4276_;
}
}
v___jp_4276_:
{
lean_object* v_getInheritedTraceOptions_4277_; lean_object* v___x_4278_; lean_object* v___f_4279_; lean_object* v___f_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v_getInheritedTraceOptions_4277_ = lean_ctor_get(v_inst_4262_, 2);
lean_inc(v_getInheritedTraceOptions_4277_);
v___x_4278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
lean_inc_n(v_toBind_4261_, 3);
v___f_4279_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_4279_, 0, v___f_4274_);
lean_closure_set(v___f_4279_, 1, v_inst_4263_);
lean_closure_set(v___f_4279_, 2, v___x_4256_);
lean_closure_set(v___f_4279_, 3, v_type_4268_);
lean_closure_set(v___f_4279_, 4, v_inst_4264_);
lean_closure_set(v___f_4279_, 5, v_inst_4262_);
lean_closure_set(v___f_4279_, 6, v_inst_4265_);
lean_closure_set(v___f_4279_, 7, v___x_4278_);
lean_closure_set(v___f_4279_, 8, v_toBind_4261_);
lean_closure_set(v___f_4279_, 9, v___f_4275_);
v___f_4280_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_4280_, 0, v_toPure_4259_);
lean_closure_set(v___f_4280_, 1, v___x_4278_);
lean_closure_set(v___f_4280_, 2, v_toBind_4261_);
lean_closure_set(v___f_4280_, 3, v_inst_4266_);
v___x_4281_ = lean_apply_4(v_toBind_4261_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_4277_, v___f_4280_);
v___x_4282_ = lean_apply_4(v_toBind_4261_, lean_box(0), lean_box(0), v___x_4281_, v___f_4279_);
return v___x_4282_;
}
}
else
{
lean_object* v___x_4286_; lean_object* v___f_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
lean_inc_ref(v_value_4269_);
lean_dec_ref(v_newHyp_4267_);
lean_dec(v_inst_4266_);
lean_dec(v_inst_4265_);
lean_dec_ref(v_inst_4264_);
lean_dec_ref(v_inst_4263_);
lean_dec_ref(v_inst_4262_);
lean_dec(v___x_4258_);
lean_dec_ref(v___x_4256_);
v___x_4286_ = lean_box(v___x_4270_);
v___f_4287_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_4287_, 0, v___x_4286_);
lean_closure_set(v___f_4287_, 1, v_snd_4257_);
lean_closure_set(v___f_4287_, 2, v_toPure_4259_);
v___x_4288_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_4288_, 0, v_value_4269_);
v___x_4289_ = lean_apply_2(v_inst_4260_, lean_box(0), v___x_4288_);
v___x_4290_ = lean_apply_4(v_toBind_4261_, lean_box(0), lean_box(0), v___x_4289_, v___f_4287_);
return v___x_4290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_4291_, lean_object* v_toPure_4292_, lean_object* v_hyps_4293_, lean_object* v___x_4294_, lean_object* v_inst_4295_, lean_object* v_toBind_4296_, lean_object* v_inst_4297_, lean_object* v_inst_4298_, lean_object* v_inst_4299_, lean_object* v_inst_4300_, lean_object* v_inst_4301_, lean_object* v_f_4302_, lean_object* v___f_4303_, lean_object* v_next_4304_, lean_object* v_acc_4305_, lean_object* v_h_4306_, lean_object* v_G_4307_){
_start:
{
uint8_t v___x_4308_; 
v___x_4308_ = lean_nat_dec_lt(v_next_4304_, v___x_4291_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; 
lean_dec(v_G_4307_);
lean_dec(v_next_4304_);
lean_dec(v___f_4303_);
lean_dec(v_f_4302_);
lean_dec(v_inst_4301_);
lean_dec(v_inst_4300_);
lean_dec_ref(v_inst_4299_);
lean_dec_ref(v_inst_4298_);
lean_dec_ref(v_inst_4297_);
lean_dec(v_toBind_4296_);
lean_dec(v_inst_4295_);
lean_dec(v___x_4294_);
v___x_4309_ = lean_apply_2(v_toPure_4292_, lean_box(0), v_acc_4305_);
return v___x_4309_;
}
else
{
lean_object* v_snd_4310_; lean_object* v___f_4311_; lean_object* v___x_4312_; lean_object* v___f_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_snd_4310_ = lean_ctor_get(v_acc_4305_, 1);
lean_inc(v_snd_4310_);
lean_dec_ref(v_acc_4305_);
lean_inc(v_next_4304_);
lean_inc(v_toPure_4292_);
v___f_4311_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_4311_, 0, v_toPure_4292_);
lean_closure_set(v___f_4311_, 1, v_next_4304_);
lean_closure_set(v___f_4311_, 2, v_G_4307_);
v___x_4312_ = lean_array_fget_borrowed(v_hyps_4293_, v_next_4304_);
lean_dec(v_next_4304_);
lean_inc_n(v_toBind_4296_, 3);
lean_inc_n(v___x_4312_, 2);
v___f_4313_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_4313_, 0, v___x_4312_);
lean_closure_set(v___f_4313_, 1, v_snd_4310_);
lean_closure_set(v___f_4313_, 2, v___x_4294_);
lean_closure_set(v___f_4313_, 3, v_toPure_4292_);
lean_closure_set(v___f_4313_, 4, v_inst_4295_);
lean_closure_set(v___f_4313_, 5, v_toBind_4296_);
lean_closure_set(v___f_4313_, 6, v_inst_4297_);
lean_closure_set(v___f_4313_, 7, v_inst_4298_);
lean_closure_set(v___f_4313_, 8, v_inst_4299_);
lean_closure_set(v___f_4313_, 9, v_inst_4300_);
lean_closure_set(v___f_4313_, 10, v_inst_4301_);
v___x_4314_ = lean_apply_1(v_f_4302_, v___x_4312_);
v___x_4315_ = lean_apply_4(v_toBind_4296_, lean_box(0), lean_box(0), v___x_4314_, v___f_4313_);
v___x_4316_ = lean_apply_4(v_toBind_4296_, lean_box(0), lean_box(0), v___x_4315_, v___f_4303_);
v___x_4317_ = lean_apply_4(v_toBind_4296_, lean_box(0), lean_box(0), v___x_4316_, v___f_4311_);
return v___x_4317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_4318_ = _args[0];
lean_object* v_toPure_4319_ = _args[1];
lean_object* v_hyps_4320_ = _args[2];
lean_object* v___x_4321_ = _args[3];
lean_object* v_inst_4322_ = _args[4];
lean_object* v_toBind_4323_ = _args[5];
lean_object* v_inst_4324_ = _args[6];
lean_object* v_inst_4325_ = _args[7];
lean_object* v_inst_4326_ = _args[8];
lean_object* v_inst_4327_ = _args[9];
lean_object* v_inst_4328_ = _args[10];
lean_object* v_f_4329_ = _args[11];
lean_object* v___f_4330_ = _args[12];
lean_object* v_next_4331_ = _args[13];
lean_object* v_acc_4332_ = _args[14];
lean_object* v_h_4333_ = _args[15];
lean_object* v_G_4334_ = _args[16];
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_4318_, v_toPure_4319_, v_hyps_4320_, v___x_4321_, v_inst_4322_, v_toBind_4323_, v_inst_4324_, v_inst_4325_, v_inst_4326_, v_inst_4327_, v_inst_4328_, v_f_4329_, v___f_4330_, v_next_4331_, v_acc_4332_, v_h_4333_, v_G_4334_);
lean_dec_ref(v_hyps_4320_);
lean_dec(v___x_4318_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_4336_, lean_object* v_inst_4337_, lean_object* v_toBind_4338_, lean_object* v_inst_4339_, lean_object* v_inst_4340_, lean_object* v_inst_4341_, lean_object* v_inst_4342_, lean_object* v_inst_4343_, lean_object* v_f_4344_, lean_object* v___f_4345_, lean_object* v___f_4346_, lean_object* v_hyps_4347_){
_start:
{
lean_object* v___x_4348_; lean_object* v_newHyps_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___f_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4348_ = lean_array_get_size(v_hyps_4347_);
v_newHyps_4349_ = lean_mk_empty_array_with_capacity(v___x_4348_);
v___x_4350_ = lean_unsigned_to_nat(0u);
v___x_4351_ = lean_box(0);
lean_inc(v_toBind_4338_);
v___f_4352_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_4352_, 0, v___x_4348_);
lean_closure_set(v___f_4352_, 1, v_toPure_4336_);
lean_closure_set(v___f_4352_, 2, v_hyps_4347_);
lean_closure_set(v___f_4352_, 3, v___x_4351_);
lean_closure_set(v___f_4352_, 4, v_inst_4337_);
lean_closure_set(v___f_4352_, 5, v_toBind_4338_);
lean_closure_set(v___f_4352_, 6, v_inst_4339_);
lean_closure_set(v___f_4352_, 7, v_inst_4340_);
lean_closure_set(v___f_4352_, 8, v_inst_4341_);
lean_closure_set(v___f_4352_, 9, v_inst_4342_);
lean_closure_set(v___f_4352_, 10, v_inst_4343_);
lean_closure_set(v___f_4352_, 11, v_f_4344_);
lean_closure_set(v___f_4352_, 12, v___f_4345_);
v___x_4353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4351_);
lean_ctor_set(v___x_4353_, 1, v_newHyps_4349_);
v___x_4354_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4352_, v___x_4350_, v___x_4353_, lean_box(0));
v___x_4355_ = lean_apply_4(v_toBind_4338_, lean_box(0), lean_box(0), v___x_4354_, v___f_4346_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_4356_, lean_object* v_inst_4357_, lean_object* v_inst_4358_, lean_object* v_inst_4359_, lean_object* v_inst_4360_, lean_object* v_inst_4361_, lean_object* v_f_4362_){
_start:
{
lean_object* v_toApplicative_4363_; lean_object* v_toBind_4364_; lean_object* v_toPure_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___f_4368_; lean_object* v___f_4369_; lean_object* v___f_4370_; lean_object* v___f_4371_; lean_object* v___x_4372_; 
v_toApplicative_4363_ = lean_ctor_get(v_inst_4356_, 0);
v_toBind_4364_ = lean_ctor_get(v_inst_4356_, 1);
lean_inc_n(v_toBind_4364_, 3);
v_toPure_4365_ = lean_ctor_get(v_toApplicative_4363_, 1);
lean_inc_n(v_toPure_4365_, 4);
v___x_4366_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_4357_, 2);
v___x_4367_ = lean_apply_2(v_inst_4357_, lean_box(0), v___x_4366_);
v___f_4368_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4368_, 0, v_toPure_4365_);
v___f_4369_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_4369_, 0, v_inst_4357_);
lean_closure_set(v___f_4369_, 1, v_toBind_4364_);
lean_closure_set(v___f_4369_, 2, v___f_4368_);
lean_closure_set(v___f_4369_, 3, v_toPure_4365_);
v___f_4370_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4370_, 0, v_toPure_4365_);
v___f_4371_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_4371_, 0, v_toPure_4365_);
lean_closure_set(v___f_4371_, 1, v_inst_4357_);
lean_closure_set(v___f_4371_, 2, v_toBind_4364_);
lean_closure_set(v___f_4371_, 3, v_inst_4359_);
lean_closure_set(v___f_4371_, 4, v_inst_4358_);
lean_closure_set(v___f_4371_, 5, v_inst_4356_);
lean_closure_set(v___f_4371_, 6, v_inst_4361_);
lean_closure_set(v___f_4371_, 7, v_inst_4360_);
lean_closure_set(v___f_4371_, 8, v_f_4362_);
lean_closure_set(v___f_4371_, 9, v___f_4370_);
lean_closure_set(v___f_4371_, 10, v___f_4369_);
v___x_4372_ = lean_apply_4(v_toBind_4364_, lean_box(0), lean_box(0), v___x_4367_, v___f_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_4373_, lean_object* v_inst_4374_, lean_object* v_inst_4375_, lean_object* v_inst_4376_, lean_object* v_inst_4377_, lean_object* v_inst_4378_, lean_object* v_inst_4379_, lean_object* v_inst_4380_, lean_object* v_inst_4381_, lean_object* v_f_4382_){
_start:
{
lean_object* v_toApplicative_4383_; lean_object* v_toBind_4384_; lean_object* v_toPure_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___f_4388_; lean_object* v___f_4389_; lean_object* v___f_4390_; lean_object* v___f_4391_; lean_object* v___x_4392_; 
v_toApplicative_4383_ = lean_ctor_get(v_inst_4374_, 0);
v_toBind_4384_ = lean_ctor_get(v_inst_4374_, 1);
lean_inc_n(v_toBind_4384_, 3);
v_toPure_4385_ = lean_ctor_get(v_toApplicative_4383_, 1);
lean_inc_n(v_toPure_4385_, 4);
v___x_4386_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_4375_, 2);
v___x_4387_ = lean_apply_2(v_inst_4375_, lean_box(0), v___x_4386_);
v___f_4388_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4388_, 0, v_toPure_4385_);
v___f_4389_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_4389_, 0, v_inst_4375_);
lean_closure_set(v___f_4389_, 1, v_toBind_4384_);
lean_closure_set(v___f_4389_, 2, v___f_4388_);
lean_closure_set(v___f_4389_, 3, v_toPure_4385_);
v___f_4390_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4390_, 0, v_toPure_4385_);
v___f_4391_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_4391_, 0, v_toPure_4385_);
lean_closure_set(v___f_4391_, 1, v_inst_4375_);
lean_closure_set(v___f_4391_, 2, v_toBind_4384_);
lean_closure_set(v___f_4391_, 3, v_inst_4378_);
lean_closure_set(v___f_4391_, 4, v_inst_4376_);
lean_closure_set(v___f_4391_, 5, v_inst_4374_);
lean_closure_set(v___f_4391_, 6, v_inst_4380_);
lean_closure_set(v___f_4391_, 7, v_inst_4379_);
lean_closure_set(v___f_4391_, 8, v_f_4382_);
lean_closure_set(v___f_4391_, 9, v___f_4390_);
lean_closure_set(v___f_4391_, 10, v___f_4389_);
v___x_4392_ = lean_apply_4(v_toBind_4384_, lean_box(0), lean_box(0), v___x_4387_, v___f_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_4393_, lean_object* v_inst_4394_, lean_object* v_inst_4395_, lean_object* v_inst_4396_, lean_object* v_inst_4397_, lean_object* v_inst_4398_, lean_object* v_inst_4399_, lean_object* v_inst_4400_, lean_object* v_inst_4401_, lean_object* v_f_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_4393_, v_inst_4394_, v_inst_4395_, v_inst_4396_, v_inst_4397_, v_inst_4398_, v_inst_4399_, v_inst_4400_, v_inst_4401_, v_f_4402_);
lean_dec_ref(v_inst_4401_);
lean_dec_ref(v_inst_4397_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_4404_, lean_object* v_x_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = lean_apply_1(v_f_4404_, v___y_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_4408_, lean_object* v_inst_4409_, lean_object* v___f_4410_, lean_object* v_hyps_4411_){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; uint8_t v___x_4415_; 
v___x_4412_ = lean_unsigned_to_nat(0u);
v___x_4413_ = lean_array_get_size(v_hyps_4411_);
v___x_4414_ = lean_box(0);
v___x_4415_ = lean_nat_dec_lt(v___x_4412_, v___x_4413_);
if (v___x_4415_ == 0)
{
lean_object* v_toPure_4416_; lean_object* v___x_4417_; 
lean_dec_ref(v_hyps_4411_);
lean_dec(v___f_4410_);
lean_dec_ref(v_inst_4409_);
v_toPure_4416_ = lean_ctor_get(v_toApplicative_4408_, 1);
lean_inc(v_toPure_4416_);
lean_dec_ref(v_toApplicative_4408_);
v___x_4417_ = lean_apply_2(v_toPure_4416_, lean_box(0), v___x_4414_);
return v___x_4417_;
}
else
{
uint8_t v___x_4418_; 
v___x_4418_ = lean_nat_dec_le(v___x_4413_, v___x_4413_);
if (v___x_4418_ == 0)
{
if (v___x_4415_ == 0)
{
lean_object* v_toPure_4419_; lean_object* v___x_4420_; 
lean_dec_ref(v_hyps_4411_);
lean_dec(v___f_4410_);
lean_dec_ref(v_inst_4409_);
v_toPure_4419_ = lean_ctor_get(v_toApplicative_4408_, 1);
lean_inc(v_toPure_4419_);
lean_dec_ref(v_toApplicative_4408_);
v___x_4420_ = lean_apply_2(v_toPure_4419_, lean_box(0), v___x_4414_);
return v___x_4420_;
}
else
{
size_t v___x_4421_; size_t v___x_4422_; lean_object* v___x_4423_; 
lean_dec_ref(v_toApplicative_4408_);
v___x_4421_ = ((size_t)0ULL);
v___x_4422_ = lean_usize_of_nat(v___x_4413_);
v___x_4423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4409_, v___f_4410_, v_hyps_4411_, v___x_4421_, v___x_4422_, v___x_4414_);
return v___x_4423_;
}
}
else
{
size_t v___x_4424_; size_t v___x_4425_; lean_object* v___x_4426_; 
lean_dec_ref(v_toApplicative_4408_);
v___x_4424_ = ((size_t)0ULL);
v___x_4425_ = lean_usize_of_nat(v___x_4413_);
v___x_4426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4409_, v___f_4410_, v_hyps_4411_, v___x_4424_, v___x_4425_, v___x_4414_);
return v___x_4426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_4427_, lean_object* v_inst_4428_, lean_object* v_f_4429_){
_start:
{
lean_object* v_toApplicative_4430_; lean_object* v_toBind_4431_; lean_object* v___f_4432_; lean_object* v___f_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_toApplicative_4430_ = lean_ctor_get(v_inst_4427_, 0);
lean_inc_ref(v_toApplicative_4430_);
v_toBind_4431_ = lean_ctor_get(v_inst_4427_, 1);
lean_inc(v_toBind_4431_);
v___f_4432_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4432_, 0, v_f_4429_);
v___f_4433_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4433_, 0, v_toApplicative_4430_);
lean_closure_set(v___f_4433_, 1, v_inst_4427_);
lean_closure_set(v___f_4433_, 2, v___f_4432_);
v___x_4434_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_4435_ = lean_apply_2(v_inst_4428_, lean_box(0), v___x_4434_);
v___x_4436_ = lean_apply_4(v_toBind_4431_, lean_box(0), lean_box(0), v___x_4435_, v___f_4433_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_4437_, lean_object* v_inst_4438_, lean_object* v_inst_4439_, lean_object* v_inst_4440_, lean_object* v_f_4441_){
_start:
{
lean_object* v_toApplicative_4442_; lean_object* v_toBind_4443_; lean_object* v___f_4444_; lean_object* v___f_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v_toApplicative_4442_ = lean_ctor_get(v_inst_4438_, 0);
lean_inc_ref(v_toApplicative_4442_);
v_toBind_4443_ = lean_ctor_get(v_inst_4438_, 1);
lean_inc(v_toBind_4443_);
v___f_4444_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4444_, 0, v_f_4441_);
v___f_4445_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_4445_, 0, v_toApplicative_4442_);
lean_closure_set(v___f_4445_, 1, v_inst_4438_);
lean_closure_set(v___f_4445_, 2, v___f_4444_);
v___x_4446_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_4447_ = lean_apply_2(v_inst_4439_, lean_box(0), v___x_4446_);
v___x_4448_ = lean_apply_4(v_toBind_4443_, lean_box(0), lean_box(0), v___x_4447_, v___f_4445_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_4449_, lean_object* v_inst_4450_, lean_object* v_inst_4451_, lean_object* v_inst_4452_, lean_object* v_f_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_4449_, v_inst_4450_, v_inst_4451_, v_inst_4452_, v_f_4453_);
lean_dec_ref(v_inst_4452_);
return v_res_4454_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4455_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_4458_, lean_object* v_methods_4459_, lean_object* v_config_4460_, lean_object* v_hyp_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_){
_start:
{
lean_object* v___x_4470_; lean_object* v_caches_4471_; lean_object* v___x_4472_; lean_object* v_typeAnalysis_4473_; lean_object* v_target_4474_; lean_object* v_hypotheses_4475_; uint8_t v_didChange_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4522_; 
v___x_4470_ = lean_st_ref_get(v_a_4462_);
v_caches_4471_ = lean_ctor_get(v___x_4470_, 0);
lean_inc_ref(v_caches_4471_);
lean_dec(v___x_4470_);
v___x_4472_ = lean_st_ref_take(v_a_4462_);
v_typeAnalysis_4473_ = lean_ctor_get(v___x_4472_, 1);
v_target_4474_ = lean_ctor_get(v___x_4472_, 2);
v_hypotheses_4475_ = lean_ctor_get(v___x_4472_, 3);
v_didChange_4476_ = lean_ctor_get_uint8(v___x_4472_, sizeof(void*)*4);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4522_ == 0)
{
lean_object* v_unused_4523_; 
v_unused_4523_ = lean_ctor_get(v___x_4472_, 0);
lean_dec(v_unused_4523_);
v___x_4478_ = v___x_4472_;
v_isShared_4479_ = v_isSharedCheck_4522_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_hypotheses_4475_);
lean_inc(v_target_4474_);
lean_inc(v_typeAnalysis_4473_);
lean_dec(v___x_4472_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4522_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4480_ = lean_unsigned_to_nat(0u);
v___x_4481_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_4458_, v_caches_4471_);
v___x_4482_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_4483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4480_);
lean_ctor_set(v___x_4483_, 1, v___x_4481_);
lean_ctor_set(v___x_4483_, 2, v___x_4482_);
lean_ctor_set(v___x_4483_, 3, v___x_4482_);
v___x_4484_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_4458_, v___x_4482_, v_caches_4471_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 0, v___x_4484_);
v___x_4486_ = v___x_4478_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v_typeAnalysis_4473_);
lean_ctor_set(v_reuseFailAlloc_4521_, 2, v_target_4474_);
lean_ctor_set(v_reuseFailAlloc_4521_, 3, v_hypotheses_4475_);
lean_ctor_set_uint8(v_reuseFailAlloc_4521_, sizeof(void*)*4, v_didChange_4476_);
v___x_4486_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v_type_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4487_ = lean_st_ref_put(v_a_4462_, v___x_4486_);
v_type_4488_ = lean_ctor_get(v_hyp_4461_, 1);
lean_inc_ref(v_type_4488_);
v___x_4489_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_4489_, 0, v_type_4488_);
v___x_4490_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_4489_, v_methods_4459_, v_config_4460_, v___x_4483_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; lean_object* v_fst_4492_; lean_object* v_snd_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v_caches_4496_; lean_object* v_persistentCache_4497_; lean_object* v_typeAnalysis_4498_; lean_object* v_target_4499_; lean_object* v_hypotheses_4500_; uint8_t v_didChange_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4511_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4490_, 1);
v_fst_4492_ = lean_ctor_get(v_a_4491_, 0);
lean_inc(v_fst_4492_);
v_snd_4493_ = lean_ctor_get(v_a_4491_, 1);
lean_inc(v_snd_4493_);
lean_dec(v_a_4491_);
v___x_4494_ = lean_st_ref_get(v_a_4462_);
v___x_4495_ = lean_st_ref_take(v_a_4462_);
v_caches_4496_ = lean_ctor_get(v___x_4494_, 0);
lean_inc_ref(v_caches_4496_);
lean_dec(v___x_4494_);
v_persistentCache_4497_ = lean_ctor_get(v_snd_4493_, 1);
lean_inc_ref(v_persistentCache_4497_);
lean_dec(v_snd_4493_);
v_typeAnalysis_4498_ = lean_ctor_get(v___x_4495_, 1);
v_target_4499_ = lean_ctor_get(v___x_4495_, 2);
v_hypotheses_4500_ = lean_ctor_get(v___x_4495_, 3);
v_didChange_4501_ = lean_ctor_get_uint8(v___x_4495_, sizeof(void*)*4);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4511_ == 0)
{
lean_object* v_unused_4512_; 
v_unused_4512_ = lean_ctor_get(v___x_4495_, 0);
lean_dec(v_unused_4512_);
v___x_4503_ = v___x_4495_;
v_isShared_4504_ = v_isSharedCheck_4511_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_hypotheses_4500_);
lean_inc(v_target_4499_);
lean_inc(v_typeAnalysis_4498_);
lean_dec(v___x_4495_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4511_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; lean_object* v___x_4507_; 
v___x_4505_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_4458_, v_persistentCache_4497_, v_caches_4496_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4505_);
v___x_4507_ = v___x_4503_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4505_);
lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_typeAnalysis_4498_);
lean_ctor_set(v_reuseFailAlloc_4510_, 2, v_target_4499_);
lean_ctor_set(v_reuseFailAlloc_4510_, 3, v_hypotheses_4500_);
lean_ctor_set_uint8(v_reuseFailAlloc_4510_, sizeof(void*)*4, v_didChange_4501_);
v___x_4507_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4508_ = lean_st_ref_put(v_a_4462_, v___x_4507_);
v___x_4509_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_4461_, v_fst_4492_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
return v___x_4509_;
}
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec_ref(v_hyp_4461_);
v_a_4513_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4490_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4490_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_4524_, lean_object* v_methods_4525_, lean_object* v_config_4526_, lean_object* v_hyp_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
uint8_t v_cacheId_boxed_4536_; lean_object* v_res_4537_; 
v_cacheId_boxed_4536_ = lean_unbox(v_cacheId_4524_);
v_res_4537_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_4536_, v_methods_4525_, v_config_4526_, v_hyp_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_4538_, lean_object* v_methods_4539_, lean_object* v_config_4540_, lean_object* v_hyp_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4538_, v_methods_4539_, v_config_4540_, v_hyp_4541_, v_a_4543_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4555_, lean_object* v_methods_4556_, lean_object* v_config_4557_, lean_object* v_hyp_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
uint8_t v_cacheId_boxed_4571_; lean_object* v_res_4572_; 
v_cacheId_boxed_4571_ = lean_unbox(v_cacheId_4555_);
v_res_4572_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4571_, v_methods_4556_, v_config_4557_, v_hyp_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec(v_a_4560_);
lean_dec_ref(v_a_4559_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4573_, lean_object* v_methods_4574_, lean_object* v_config_4575_, lean_object* v_hyp_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v___x_4585_; lean_object* v_caches_4586_; lean_object* v___x_4587_; lean_object* v_typeAnalysis_4588_; lean_object* v_target_4589_; lean_object* v_hypotheses_4590_; uint8_t v_didChange_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4637_; 
v___x_4585_ = lean_st_ref_get(v_a_4577_);
v_caches_4586_ = lean_ctor_get(v___x_4585_, 0);
lean_inc_ref(v_caches_4586_);
lean_dec(v___x_4585_);
v___x_4587_ = lean_st_ref_take(v_a_4577_);
v_typeAnalysis_4588_ = lean_ctor_get(v___x_4587_, 1);
v_target_4589_ = lean_ctor_get(v___x_4587_, 2);
v_hypotheses_4590_ = lean_ctor_get(v___x_4587_, 3);
v_didChange_4591_ = lean_ctor_get_uint8(v___x_4587_, sizeof(void*)*4);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; 
v_unused_4638_ = lean_ctor_get(v___x_4587_, 0);
lean_dec(v_unused_4638_);
v___x_4593_ = v___x_4587_;
v_isShared_4594_ = v_isSharedCheck_4637_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_hypotheses_4590_);
lean_inc(v_target_4589_);
lean_inc(v_typeAnalysis_4588_);
lean_dec(v___x_4587_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4637_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4599_; 
v___x_4595_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4573_, v_caches_4586_);
v___x_4596_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4597_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4573_, v___x_4596_, v_caches_4586_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4597_);
v___x_4599_ = v___x_4593_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4597_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_typeAnalysis_4588_);
lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_target_4589_);
lean_ctor_set(v_reuseFailAlloc_4636_, 3, v_hypotheses_4590_);
lean_ctor_set_uint8(v_reuseFailAlloc_4636_, sizeof(void*)*4, v_didChange_4591_);
v___x_4599_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
lean_object* v___x_4600_; lean_object* v_type_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4600_ = lean_st_ref_put(v_a_4577_, v___x_4599_);
v_type_4601_ = lean_ctor_get(v_hyp_4576_, 1);
v___x_4602_ = lean_unsigned_to_nat(0u);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
lean_ctor_set(v___x_4603_, 1, v___x_4595_);
lean_inc_ref(v_type_4601_);
v___x_4604_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4604_, 0, v_type_4601_);
v___x_4605_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4604_, v_methods_4574_, v_config_4575_, v___x_4603_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v_fst_4607_; lean_object* v_snd_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v_caches_4611_; lean_object* v_cache_4612_; lean_object* v_typeAnalysis_4613_; lean_object* v_target_4614_; lean_object* v_hypotheses_4615_; uint8_t v_didChange_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4626_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref_known(v___x_4605_, 1);
v_fst_4607_ = lean_ctor_get(v_a_4606_, 0);
lean_inc(v_fst_4607_);
v_snd_4608_ = lean_ctor_get(v_a_4606_, 1);
lean_inc(v_snd_4608_);
lean_dec(v_a_4606_);
v___x_4609_ = lean_st_ref_get(v_a_4577_);
v___x_4610_ = lean_st_ref_take(v_a_4577_);
v_caches_4611_ = lean_ctor_get(v___x_4609_, 0);
lean_inc_ref(v_caches_4611_);
lean_dec(v___x_4609_);
v_cache_4612_ = lean_ctor_get(v_snd_4608_, 1);
lean_inc_ref(v_cache_4612_);
lean_dec(v_snd_4608_);
v_typeAnalysis_4613_ = lean_ctor_get(v___x_4610_, 1);
v_target_4614_ = lean_ctor_get(v___x_4610_, 2);
v_hypotheses_4615_ = lean_ctor_get(v___x_4610_, 3);
v_didChange_4616_ = lean_ctor_get_uint8(v___x_4610_, sizeof(void*)*4);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v___x_4610_, 0);
lean_dec(v_unused_4627_);
v___x_4618_ = v___x_4610_;
v_isShared_4619_ = v_isSharedCheck_4626_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_hypotheses_4615_);
lean_inc(v_target_4614_);
lean_inc(v_typeAnalysis_4613_);
lean_dec(v___x_4610_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4626_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4620_; lean_object* v___x_4622_; 
v___x_4620_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4573_, v_cache_4612_, v_caches_4611_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4620_);
v___x_4622_ = v___x_4618_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4620_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_typeAnalysis_4613_);
lean_ctor_set(v_reuseFailAlloc_4625_, 2, v_target_4614_);
lean_ctor_set(v_reuseFailAlloc_4625_, 3, v_hypotheses_4615_);
lean_ctor_set_uint8(v_reuseFailAlloc_4625_, sizeof(void*)*4, v_didChange_4616_);
v___x_4622_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = lean_st_ref_put(v_a_4577_, v___x_4622_);
v___x_4624_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4576_, v_fst_4607_);
lean_dec(v_fst_4607_);
return v___x_4624_;
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec_ref(v_hyp_4576_);
v_a_4628_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4605_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4605_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4639_, lean_object* v_methods_4640_, lean_object* v_config_4641_, lean_object* v_hyp_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
uint8_t v_cacheId_boxed_4651_; lean_object* v_res_4652_; 
v_cacheId_boxed_4651_ = lean_unbox(v_cacheId_4639_);
v_res_4652_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4651_, v_methods_4640_, v_config_4641_, v_hyp_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4653_, lean_object* v_methods_4654_, lean_object* v_config_4655_, lean_object* v_hyp_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v___x_4669_; 
v___x_4669_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4653_, v_methods_4654_, v_config_4655_, v_hyp_4656_, v_a_4658_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4670_, lean_object* v_methods_4671_, lean_object* v_config_4672_, lean_object* v_hyp_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
uint8_t v_cacheId_boxed_4686_; lean_object* v_res_4687_; 
v_cacheId_boxed_4686_ = lean_unbox(v_cacheId_4670_);
v_res_4687_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4686_, v_methods_4671_, v_config_4672_, v_hyp_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec(v_a_4675_);
lean_dec_ref(v_a_4674_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4688_, lean_object* v_a_4689_, lean_object* v___x_4690_, lean_object* v_____r_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4704_ = lean_array_push(v_snd_4688_, v_a_4689_);
v___x_4705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4690_);
lean_ctor_set(v___x_4705_, 1, v___x_4704_);
v___x_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
v___x_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4708_, lean_object* v_a_4709_, lean_object* v___x_4710_, lean_object* v_____r_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4708_, v_a_4709_, v___x_4710_, v_____r_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4725_, lean_object* v___f_4726_, lean_object* v_____r_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_){
_start:
{
lean_object* v___x_4740_; lean_object* v_caches_4741_; lean_object* v_typeAnalysis_4742_; lean_object* v_target_4743_; lean_object* v_hypotheses_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4754_; 
v___x_4740_ = lean_st_ref_take(v___y_4729_);
v_caches_4741_ = lean_ctor_get(v___x_4740_, 0);
v_typeAnalysis_4742_ = lean_ctor_get(v___x_4740_, 1);
v_target_4743_ = lean_ctor_get(v___x_4740_, 2);
v_hypotheses_4744_ = lean_ctor_get(v___x_4740_, 3);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4746_ = v___x_4740_;
v_isShared_4747_ = v_isSharedCheck_4754_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_hypotheses_4744_);
lean_inc(v_target_4743_);
lean_inc(v_typeAnalysis_4742_);
lean_inc(v_caches_4741_);
lean_dec(v___x_4740_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4754_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_caches_4741_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_typeAnalysis_4742_);
lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_target_4743_);
lean_ctor_set(v_reuseFailAlloc_4753_, 3, v_hypotheses_4744_);
v___x_4749_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*4, v___x_4725_);
v___x_4750_ = lean_st_ref_put(v___y_4729_, v___x_4749_);
v___x_4751_ = lean_box(0);
lean_inc(v___y_4738_);
lean_inc_ref(v___y_4737_);
lean_inc(v___y_4736_);
lean_inc_ref(v___y_4735_);
lean_inc(v___y_4734_);
lean_inc_ref(v___y_4733_);
lean_inc(v___y_4732_);
lean_inc_ref(v___y_4731_);
lean_inc(v___y_4730_);
lean_inc(v___y_4729_);
lean_inc_ref(v___y_4728_);
v___x_4752_ = lean_apply_13(v___f_4726_, v___x_4751_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, lean_box(0));
return v___x_4752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4755_, lean_object* v___f_4756_, lean_object* v_____r_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
uint8_t v___x_22146__boxed_4770_; lean_object* v_res_4771_; 
v___x_22146__boxed_4770_ = lean_unbox(v___x_4755_);
v_res_4771_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22146__boxed_4770_, v___f_4756_, v_____r_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4772_, lean_object* v_hypotheses_4773_, uint8_t v_cacheId_4774_, lean_object* v_methods_4775_, lean_object* v_config_4776_, lean_object* v___x_4777_, lean_object* v___x_4778_, lean_object* v___x_4779_, lean_object* v_toMonadRef_4780_, lean_object* v___f_4781_, lean_object* v_next_4782_, lean_object* v_acc_4783_, lean_object* v_h_4784_, lean_object* v_G_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
lean_object* v___y_4799_; uint8_t v___x_4821_; 
v___x_4821_ = lean_nat_dec_lt(v_next_4782_, v___x_4772_);
if (v___x_4821_ == 0)
{
lean_object* v___x_4822_; 
lean_dec_ref(v_G_4785_);
lean_dec(v___f_4781_);
lean_dec_ref(v_toMonadRef_4780_);
lean_dec_ref(v___x_4779_);
lean_dec_ref(v___x_4778_);
lean_dec(v___x_4777_);
lean_dec_ref(v_config_4776_);
lean_dec_ref(v_methods_4775_);
v___x_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4822_, 0, v_acc_4783_);
return v___x_4822_;
}
else
{
lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4823_ = lean_array_fget_borrowed(v_hypotheses_4773_, v_next_4782_);
lean_inc(v___x_4823_);
v___x_4824_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4774_, v_methods_4775_, v_config_4776_, v___x_4823_, v___y_4787_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v_snd_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4888_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4824_, 1);
v_snd_4826_ = lean_ctor_get(v_acc_4783_, 1);
v_isSharedCheck_4888_ = !lean_is_exclusive(v_acc_4783_);
if (v_isSharedCheck_4888_ == 0)
{
lean_object* v_unused_4889_; 
v_unused_4889_ = lean_ctor_get(v_acc_4783_, 0);
lean_dec(v_unused_4889_);
v___x_4828_ = v_acc_4783_;
v_isShared_4829_ = v_isSharedCheck_4888_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_snd_4826_);
lean_dec(v_acc_4783_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4888_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v_type_4830_; lean_object* v_value_4831_; uint8_t v___x_4832_; 
v_type_4830_ = lean_ctor_get(v_a_4825_, 1);
v_value_4831_ = lean_ctor_get(v_a_4825_, 2);
lean_inc_ref(v_type_4830_);
v___x_4832_ = l_Lean_Expr_isFalse(v_type_4830_);
if (v___x_4832_ == 0)
{
lean_object* v_type_4833_; lean_object* v___f_4834_; uint8_t v___x_4863_; 
lean_del_object(v___x_4828_);
v_type_4833_ = lean_ctor_get(v___x_4823_, 1);
lean_inc(v___x_4777_);
lean_inc(v_a_4825_);
lean_inc(v_snd_4826_);
v___f_4834_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4834_, 0, v_snd_4826_);
lean_closure_set(v___f_4834_, 1, v_a_4825_);
lean_closure_set(v___f_4834_, 2, v___x_4777_);
v___x_4863_ = lean_expr_eqv(v_type_4833_, v_type_4830_);
if (v___x_4863_ == 0)
{
lean_inc_ref(v_type_4830_);
lean_dec(v_snd_4826_);
lean_dec(v_a_4825_);
lean_dec(v___x_4777_);
goto v___jp_4838_;
}
else
{
if (v___x_4832_ == 0)
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
lean_dec_ref(v___f_4834_);
lean_dec(v___f_4781_);
lean_dec_ref(v_toMonadRef_4780_);
lean_dec_ref(v___x_4779_);
lean_dec_ref(v___x_4778_);
v___x_4864_ = lean_box(0);
v___x_4865_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4826_, v_a_4825_, v___x_4777_, v___x_4864_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_);
v___y_4799_ = v___x_4865_;
goto v___jp_4798_;
}
else
{
lean_inc_ref(v_type_4830_);
lean_dec(v_snd_4826_);
lean_dec(v_a_4825_);
lean_dec(v___x_4777_);
goto v___jp_4838_;
}
}
v___jp_4835_:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4836_ = lean_box(0);
v___x_4837_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4821_, v___f_4834_, v___x_4836_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_);
v___y_4799_ = v___x_4837_;
goto v___jp_4798_;
}
v___jp_4838_:
{
lean_object* v_options_4839_; uint8_t v_hasTrace_4840_; 
v_options_4839_ = lean_ctor_get(v___y_4795_, 2);
v_hasTrace_4840_ = lean_ctor_get_uint8(v_options_4839_, sizeof(void*)*1);
if (v_hasTrace_4840_ == 0)
{
lean_dec_ref(v_type_4830_);
lean_dec(v___f_4781_);
lean_dec_ref(v_toMonadRef_4780_);
lean_dec_ref(v___x_4779_);
lean_dec_ref(v___x_4778_);
goto v___jp_4835_;
}
else
{
lean_object* v_inheritedTraceOptions_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; uint8_t v___x_4844_; 
v_inheritedTraceOptions_4841_ = lean_ctor_get(v___y_4795_, 13);
v___x_4842_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_4843_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_4844_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4841_, v_options_4839_, v___x_4843_);
if (v___x_4844_ == 0)
{
lean_dec_ref(v_type_4830_);
lean_dec(v___f_4781_);
lean_dec_ref(v_toMonadRef_4780_);
lean_dec_ref(v___x_4779_);
lean_dec_ref(v___x_4778_);
goto v___jp_4835_;
}
else
{
lean_object* v_type_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_22071__overap_4851_; lean_object* v___x_4852_; 
v_type_4845_ = lean_ctor_get(v___x_4823_, 1);
lean_inc_ref(v_type_4845_);
v___x_4846_ = l_Lean_MessageData_ofExpr(v_type_4845_);
v___x_4847_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4846_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
v___x_4849_ = l_Lean_MessageData_ofExpr(v_type_4830_);
v___x_4850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4848_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v___x_22071__overap_4851_ = l_Lean_addTrace___redArg(v___x_4778_, v___x_4779_, v_toMonadRef_4780_, v___f_4781_, v___x_4842_, v___x_4850_);
lean_inc(v___y_4796_);
lean_inc_ref(v___y_4795_);
lean_inc(v___y_4794_);
lean_inc_ref(v___y_4793_);
lean_inc(v___y_4792_);
lean_inc_ref(v___y_4791_);
lean_inc(v___y_4790_);
lean_inc_ref(v___y_4789_);
lean_inc(v___y_4788_);
lean_inc(v___y_4787_);
lean_inc_ref(v___y_4786_);
v___x_4852_ = lean_apply_12(v___x_22071__overap_4851_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, lean_box(0));
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4854_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref_known(v___x_4852_, 1);
v___x_4854_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4821_, v___f_4834_, v_a_4853_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_);
v___y_4799_ = v___x_4854_;
goto v___jp_4798_;
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4862_; 
lean_dec_ref(v___f_4834_);
lean_dec_ref(v_G_4785_);
v_a_4855_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4857_ = v___x_4852_;
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4852_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4860_; 
if (v_isShared_4858_ == 0)
{
v___x_4860_ = v___x_4857_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4855_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4866_; 
lean_inc_ref(v_value_4831_);
lean_dec(v_a_4825_);
lean_dec_ref(v_G_4785_);
lean_dec(v___f_4781_);
lean_dec_ref(v_toMonadRef_4780_);
lean_dec_ref(v___x_4779_);
lean_dec_ref(v___x_4778_);
lean_dec(v___x_4777_);
v___x_4866_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4831_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4878_; 
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4878_ == 0)
{
lean_object* v_unused_4879_; 
v_unused_4879_ = lean_ctor_get(v___x_4866_, 0);
lean_dec(v_unused_4879_);
v___x_4868_ = v___x_4866_;
v_isShared_4869_ = v_isSharedCheck_4878_;
goto v_resetjp_4867_;
}
else
{
lean_dec(v___x_4866_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4878_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4870_ = lean_box(v___x_4832_);
v___x_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4870_);
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 0, v___x_4871_);
v___x_4873_ = v___x_4828_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4871_);
lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_snd_4826_);
v___x_4873_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
lean_object* v___x_4875_; 
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v___x_4873_);
v___x_4875_ = v___x_4868_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
lean_del_object(v___x_4828_);
lean_dec(v_snd_4826_);
v_a_4880_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4866_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4866_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
}
else
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4897_; 
lean_dec_ref(v_G_4785_);
lean_dec_ref(v_acc_4783_);
lean_dec(v___f_4781_);
lean_dec_ref(v_toMonadRef_4780_);
lean_dec_ref(v___x_4779_);
lean_dec_ref(v___x_4778_);
lean_dec(v___x_4777_);
v_a_4890_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4892_ = v___x_4824_;
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___x_4824_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4895_; 
if (v_isShared_4893_ == 0)
{
v___x_4895_ = v___x_4892_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_a_4890_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
}
v___jp_4798_:
{
if (lean_obj_tag(v___y_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4812_; 
v_a_4800_ = lean_ctor_get(v___y_4799_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___y_4799_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4802_ = v___y_4799_;
v_isShared_4803_ = v_isSharedCheck_4812_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___y_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4812_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
if (lean_obj_tag(v_a_4800_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4806_; 
lean_dec_ref(v_G_4785_);
v_a_4804_ = lean_ctor_get(v_a_4800_, 0);
lean_inc(v_a_4804_);
lean_dec_ref_known(v_a_4800_, 1);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_a_4804_);
v___x_4806_ = v___x_4802_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; 
lean_del_object(v___x_4802_);
v_a_4808_ = lean_ctor_get(v_a_4800_, 0);
lean_inc(v_a_4808_);
lean_dec_ref_known(v_a_4800_, 1);
v___x_4809_ = lean_unsigned_to_nat(1u);
v___x_4810_ = lean_nat_add(v_next_4782_, v___x_4809_);
lean_inc(v___y_4796_);
lean_inc_ref(v___y_4795_);
lean_inc(v___y_4794_);
lean_inc_ref(v___y_4793_);
lean_inc(v___y_4792_);
lean_inc_ref(v___y_4791_);
lean_inc(v___y_4790_);
lean_inc_ref(v___y_4789_);
lean_inc(v___y_4788_);
lean_inc(v___y_4787_);
lean_inc_ref(v___y_4786_);
v___x_4811_ = lean_apply_16(v_G_4785_, v___x_4810_, v_a_4808_, lean_box(0), lean_box(0), v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, lean_box(0));
return v___x_4811_;
}
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_dec_ref(v_G_4785_);
v_a_4813_ = lean_ctor_get(v___y_4799_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___y_4799_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___y_4799_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___y_4799_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4898_ = _args[0];
lean_object* v_hypotheses_4899_ = _args[1];
lean_object* v_cacheId_4900_ = _args[2];
lean_object* v_methods_4901_ = _args[3];
lean_object* v_config_4902_ = _args[4];
lean_object* v___x_4903_ = _args[5];
lean_object* v___x_4904_ = _args[6];
lean_object* v___x_4905_ = _args[7];
lean_object* v_toMonadRef_4906_ = _args[8];
lean_object* v___f_4907_ = _args[9];
lean_object* v_next_4908_ = _args[10];
lean_object* v_acc_4909_ = _args[11];
lean_object* v_h_4910_ = _args[12];
lean_object* v_G_4911_ = _args[13];
lean_object* v___y_4912_ = _args[14];
lean_object* v___y_4913_ = _args[15];
lean_object* v___y_4914_ = _args[16];
lean_object* v___y_4915_ = _args[17];
lean_object* v___y_4916_ = _args[18];
lean_object* v___y_4917_ = _args[19];
lean_object* v___y_4918_ = _args[20];
lean_object* v___y_4919_ = _args[21];
lean_object* v___y_4920_ = _args[22];
lean_object* v___y_4921_ = _args[23];
lean_object* v___y_4922_ = _args[24];
lean_object* v___y_4923_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4924_; lean_object* v_res_4925_; 
v_cacheId_boxed_4924_ = lean_unbox(v_cacheId_4900_);
v_res_4925_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4898_, v_hypotheses_4899_, v_cacheId_boxed_4924_, v_methods_4901_, v_config_4902_, v___x_4903_, v___x_4904_, v___x_4905_, v_toMonadRef_4906_, v___f_4907_, v_next_4908_, v_acc_4909_, v_h_4910_, v_G_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
lean_dec(v___y_4920_);
lean_dec_ref(v___y_4919_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
lean_dec(v___y_4916_);
lean_dec_ref(v___y_4915_);
lean_dec(v___y_4914_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v_next_4908_);
lean_dec_ref(v_hypotheses_4899_);
lean_dec(v___x_4898_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4926_, lean_object* v_methods_4927_, lean_object* v_config_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_){
_start:
{
lean_object* v___x_4941_; lean_object* v_toApplicative_4942_; lean_object* v_toFunctor_4943_; lean_object* v_toSeq_4944_; lean_object* v_toSeqLeft_4945_; lean_object* v_toSeqRight_4946_; lean_object* v___f_4947_; lean_object* v___f_4948_; lean_object* v___f_4949_; lean_object* v___f_4950_; lean_object* v___x_4951_; lean_object* v___f_4952_; lean_object* v___f_4953_; lean_object* v___f_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v_toApplicative_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_5045_; 
v___x_4941_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4942_ = lean_ctor_get(v___x_4941_, 0);
v_toFunctor_4943_ = lean_ctor_get(v_toApplicative_4942_, 0);
v_toSeq_4944_ = lean_ctor_get(v_toApplicative_4942_, 2);
v_toSeqLeft_4945_ = lean_ctor_get(v_toApplicative_4942_, 3);
v_toSeqRight_4946_ = lean_ctor_get(v_toApplicative_4942_, 4);
v___f_4947_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4948_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4943_, 2);
v___f_4949_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4949_, 0, v_toFunctor_4943_);
v___f_4950_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4950_, 0, v_toFunctor_4943_);
v___x_4951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___f_4949_);
lean_ctor_set(v___x_4951_, 1, v___f_4950_);
lean_inc(v_toSeqRight_4946_);
v___f_4952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4952_, 0, v_toSeqRight_4946_);
lean_inc(v_toSeqLeft_4945_);
v___f_4953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4953_, 0, v_toSeqLeft_4945_);
lean_inc(v_toSeq_4944_);
v___f_4954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4954_, 0, v_toSeq_4944_);
v___x_4955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4951_);
lean_ctor_set(v___x_4955_, 1, v___f_4947_);
lean_ctor_set(v___x_4955_, 2, v___f_4954_);
lean_ctor_set(v___x_4955_, 3, v___f_4953_);
lean_ctor_set(v___x_4955_, 4, v___f_4952_);
v___x_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
lean_ctor_set(v___x_4956_, 1, v___f_4948_);
v___x_4957_ = l_StateRefT_x27_instMonad___redArg(v___x_4956_);
v_toApplicative_4958_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_5045_ == 0)
{
lean_object* v_unused_5046_; 
v_unused_5046_ = lean_ctor_get(v___x_4957_, 1);
lean_dec(v_unused_5046_);
v___x_4960_ = v___x_4957_;
v_isShared_4961_ = v_isSharedCheck_5045_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_toApplicative_4958_);
lean_dec(v___x_4957_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_5045_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v_toFunctor_4962_; lean_object* v_toSeq_4963_; lean_object* v_toSeqLeft_4964_; lean_object* v_toSeqRight_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_5043_; 
v_toFunctor_4962_ = lean_ctor_get(v_toApplicative_4958_, 0);
v_toSeq_4963_ = lean_ctor_get(v_toApplicative_4958_, 2);
v_toSeqLeft_4964_ = lean_ctor_get(v_toApplicative_4958_, 3);
v_toSeqRight_4965_ = lean_ctor_get(v_toApplicative_4958_, 4);
v_isSharedCheck_5043_ = !lean_is_exclusive(v_toApplicative_4958_);
if (v_isSharedCheck_5043_ == 0)
{
lean_object* v_unused_5044_; 
v_unused_5044_ = lean_ctor_get(v_toApplicative_4958_, 1);
lean_dec(v_unused_5044_);
v___x_4967_ = v_toApplicative_4958_;
v_isShared_4968_ = v_isSharedCheck_5043_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_toSeqRight_4965_);
lean_inc(v_toSeqLeft_4964_);
lean_inc(v_toSeq_4963_);
lean_inc(v_toFunctor_4962_);
lean_dec(v_toApplicative_4958_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_5043_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___f_4969_; lean_object* v___f_4970_; lean_object* v___f_4971_; lean_object* v___f_4972_; lean_object* v___x_4973_; lean_object* v___f_4974_; lean_object* v___f_4975_; lean_object* v___f_4976_; lean_object* v___x_4978_; 
v___f_4969_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4970_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4962_);
v___f_4971_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4971_, 0, v_toFunctor_4962_);
v___f_4972_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4972_, 0, v_toFunctor_4962_);
v___x_4973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___f_4971_);
lean_ctor_set(v___x_4973_, 1, v___f_4972_);
v___f_4974_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4974_, 0, v_toSeqRight_4965_);
v___f_4975_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4975_, 0, v_toSeqLeft_4964_);
v___f_4976_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4976_, 0, v_toSeq_4963_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 4, v___f_4974_);
lean_ctor_set(v___x_4967_, 3, v___f_4975_);
lean_ctor_set(v___x_4967_, 2, v___f_4976_);
lean_ctor_set(v___x_4967_, 1, v___f_4969_);
lean_ctor_set(v___x_4967_, 0, v___x_4973_);
v___x_4978_ = v___x_4967_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_4973_);
lean_ctor_set(v_reuseFailAlloc_5042_, 1, v___f_4969_);
lean_ctor_set(v_reuseFailAlloc_5042_, 2, v___f_4976_);
lean_ctor_set(v_reuseFailAlloc_5042_, 3, v___f_4975_);
lean_ctor_set(v_reuseFailAlloc_5042_, 4, v___f_4974_);
v___x_4978_ = v_reuseFailAlloc_5042_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
lean_object* v___x_4980_; 
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 1, v___f_4970_);
lean_ctor_set(v___x_4960_, 0, v___x_4978_);
v___x_4980_ = v___x_4960_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v___x_4978_);
lean_ctor_set(v_reuseFailAlloc_5041_, 1, v___f_4970_);
v___x_4980_ = v_reuseFailAlloc_5041_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v_toMonadRef_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v_hypotheses_4992_; lean_object* v___f_4993_; lean_object* v___x_4994_; lean_object* v_newHyps_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___f_4999_; lean_object* v___x_5000_; lean_object* v___x_21853__overap_5001_; lean_object* v___x_5002_; 
v___x_4981_ = l_StateRefT_x27_instMonad___redArg(v___x_4980_);
v___x_4982_ = l_ReaderT_instMonad___redArg(v___x_4981_);
v___x_4983_ = l_StateRefT_x27_instMonad___redArg(v___x_4982_);
v___x_4984_ = l_ReaderT_instMonad___redArg(v___x_4983_);
v___x_4985_ = l_ReaderT_instMonad___redArg(v___x_4984_);
v___x_4986_ = l_StateRefT_x27_instMonad___redArg(v___x_4985_);
v___x_4987_ = l_ReaderT_instMonad___redArg(v___x_4986_);
v___x_4988_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_4989_ = lean_ctor_get(v___x_4988_, 0);
v___x_4990_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4991_ = lean_st_ref_get(v_a_4930_);
v_hypotheses_4992_ = lean_ctor_get(v___x_4991_, 3);
lean_inc_ref(v_hypotheses_4992_);
lean_dec(v___x_4991_);
v___f_4993_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4994_ = lean_array_get_size(v_hypotheses_4992_);
v_newHyps_4995_ = lean_mk_empty_array_with_capacity(v___x_4994_);
v___x_4996_ = lean_unsigned_to_nat(0u);
v___x_4997_ = lean_box(0);
v___x_4998_ = lean_box(v_cacheId_4926_);
lean_inc_ref(v_toMonadRef_4989_);
v___f_4999_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4999_, 0, v___x_4994_);
lean_closure_set(v___f_4999_, 1, v_hypotheses_4992_);
lean_closure_set(v___f_4999_, 2, v___x_4998_);
lean_closure_set(v___f_4999_, 3, v_methods_4927_);
lean_closure_set(v___f_4999_, 4, v_config_4928_);
lean_closure_set(v___f_4999_, 5, v___x_4997_);
lean_closure_set(v___f_4999_, 6, v___x_4987_);
lean_closure_set(v___f_4999_, 7, v___x_4990_);
lean_closure_set(v___f_4999_, 8, v_toMonadRef_4989_);
lean_closure_set(v___f_4999_, 9, v___f_4993_);
v___x_5000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4997_);
lean_ctor_set(v___x_5000_, 1, v_newHyps_4995_);
v___x_21853__overap_5001_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4999_, v___x_4996_, v___x_5000_, lean_box(0));
lean_inc(v_a_4939_);
lean_inc_ref(v_a_4938_);
lean_inc(v_a_4937_);
lean_inc_ref(v_a_4936_);
lean_inc(v_a_4935_);
lean_inc_ref(v_a_4934_);
lean_inc(v_a_4933_);
lean_inc_ref(v_a_4932_);
lean_inc(v_a_4931_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
v___x_5002_ = lean_apply_12(v___x_21853__overap_5001_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, lean_box(0));
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5032_; 
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5005_ = v___x_5002_;
v_isShared_5006_ = v_isSharedCheck_5032_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_5002_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5032_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v_fst_5007_; 
v_fst_5007_ = lean_ctor_get(v_a_5003_, 0);
if (lean_obj_tag(v_fst_5007_) == 0)
{
lean_object* v_snd_5008_; lean_object* v___x_5009_; lean_object* v_caches_5010_; lean_object* v_typeAnalysis_5011_; lean_object* v_target_5012_; uint8_t v_didChange_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5026_; 
v_snd_5008_ = lean_ctor_get(v_a_5003_, 1);
lean_inc(v_snd_5008_);
lean_dec(v_a_5003_);
v___x_5009_ = lean_st_ref_take(v_a_4930_);
v_caches_5010_ = lean_ctor_get(v___x_5009_, 0);
v_typeAnalysis_5011_ = lean_ctor_get(v___x_5009_, 1);
v_target_5012_ = lean_ctor_get(v___x_5009_, 2);
v_didChange_5013_ = lean_ctor_get_uint8(v___x_5009_, sizeof(void*)*4);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5026_ == 0)
{
lean_object* v_unused_5027_; 
v_unused_5027_ = lean_ctor_get(v___x_5009_, 3);
lean_dec(v_unused_5027_);
v___x_5015_ = v___x_5009_;
v_isShared_5016_ = v_isSharedCheck_5026_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_target_5012_);
lean_inc(v_typeAnalysis_5011_);
lean_inc(v_caches_5010_);
lean_dec(v___x_5009_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5026_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 3, v_snd_5008_);
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_caches_5010_);
lean_ctor_set(v_reuseFailAlloc_5025_, 1, v_typeAnalysis_5011_);
lean_ctor_set(v_reuseFailAlloc_5025_, 2, v_target_5012_);
lean_ctor_set(v_reuseFailAlloc_5025_, 3, v_snd_5008_);
lean_ctor_set_uint8(v_reuseFailAlloc_5025_, sizeof(void*)*4, v_didChange_5013_);
v___x_5018_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
lean_object* v___x_5019_; uint8_t v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5023_; 
v___x_5019_ = lean_st_ref_put(v_a_4930_, v___x_5018_);
v___x_5020_ = 0;
v___x_5021_ = lean_box(v___x_5020_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v___x_5021_);
v___x_5023_ = v___x_5005_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5021_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
else
{
lean_object* v_val_5028_; lean_object* v___x_5030_; 
lean_inc_ref(v_fst_5007_);
lean_dec(v_a_5003_);
v_val_5028_ = lean_ctor_get(v_fst_5007_, 0);
lean_inc(v_val_5028_);
lean_dec_ref_known(v_fst_5007_, 1);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v_val_5028_);
v___x_5030_ = v___x_5005_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_val_5028_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
v_a_5033_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5002_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5002_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_5047_, lean_object* v_methods_5048_, lean_object* v_config_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
uint8_t v_cacheId_boxed_5062_; lean_object* v_res_5063_; 
v_cacheId_boxed_5062_ = lean_unbox(v_cacheId_5047_);
v_res_5063_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_5062_, v_methods_5048_, v_config_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
lean_dec(v_a_5054_);
lean_dec_ref(v_a_5053_);
lean_dec(v_a_5052_);
lean_dec(v_a_5051_);
lean_dec_ref(v_a_5050_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_5064_, lean_object* v_hypotheses_5065_, uint8_t v_cacheId_5066_, lean_object* v_methods_5067_, lean_object* v_config_5068_, lean_object* v___x_5069_, lean_object* v___x_5070_, lean_object* v___x_5071_, lean_object* v_toMonadRef_5072_, lean_object* v___f_5073_, lean_object* v_next_5074_, lean_object* v_acc_5075_, lean_object* v_h_5076_, lean_object* v_G_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v___y_5091_; uint8_t v___x_5113_; 
v___x_5113_ = lean_nat_dec_lt(v_next_5074_, v___x_5064_);
if (v___x_5113_ == 0)
{
lean_object* v___x_5114_; 
lean_dec_ref(v_G_5077_);
lean_dec(v___f_5073_);
lean_dec_ref(v_toMonadRef_5072_);
lean_dec_ref(v___x_5071_);
lean_dec_ref(v___x_5070_);
lean_dec(v___x_5069_);
lean_dec_ref(v_config_5068_);
lean_dec_ref(v_methods_5067_);
v___x_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5114_, 0, v_acc_5075_);
return v___x_5114_;
}
else
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5115_ = lean_array_fget_borrowed(v_hypotheses_5065_, v_next_5074_);
lean_inc(v___x_5115_);
v___x_5116_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_5066_, v_methods_5067_, v_config_5068_, v___x_5115_, v___y_5079_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v_a_5117_; lean_object* v_snd_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5180_; 
v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5117_);
lean_dec_ref_known(v___x_5116_, 1);
v_snd_5118_ = lean_ctor_get(v_acc_5075_, 1);
v_isSharedCheck_5180_ = !lean_is_exclusive(v_acc_5075_);
if (v_isSharedCheck_5180_ == 0)
{
lean_object* v_unused_5181_; 
v_unused_5181_ = lean_ctor_get(v_acc_5075_, 0);
lean_dec(v_unused_5181_);
v___x_5120_ = v_acc_5075_;
v_isShared_5121_ = v_isSharedCheck_5180_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_snd_5118_);
lean_dec(v_acc_5075_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5180_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v_type_5122_; lean_object* v_value_5123_; uint8_t v___x_5124_; 
v_type_5122_ = lean_ctor_get(v_a_5117_, 1);
v_value_5123_ = lean_ctor_get(v_a_5117_, 2);
lean_inc_ref(v_type_5122_);
v___x_5124_ = l_Lean_Expr_isFalse(v_type_5122_);
if (v___x_5124_ == 0)
{
lean_object* v_type_5125_; lean_object* v___f_5126_; uint8_t v___x_5155_; 
lean_del_object(v___x_5120_);
v_type_5125_ = lean_ctor_get(v___x_5115_, 1);
lean_inc(v___x_5069_);
lean_inc(v_a_5117_);
lean_inc(v_snd_5118_);
v___f_5126_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_5126_, 0, v_snd_5118_);
lean_closure_set(v___f_5126_, 1, v_a_5117_);
lean_closure_set(v___f_5126_, 2, v___x_5069_);
v___x_5155_ = lean_expr_eqv(v_type_5125_, v_type_5122_);
if (v___x_5155_ == 0)
{
lean_inc_ref(v_type_5122_);
lean_dec(v_snd_5118_);
lean_dec(v_a_5117_);
lean_dec(v___x_5069_);
goto v___jp_5130_;
}
else
{
if (v___x_5124_ == 0)
{
lean_object* v___x_5156_; lean_object* v___x_5157_; 
lean_dec_ref(v___f_5126_);
lean_dec(v___f_5073_);
lean_dec_ref(v_toMonadRef_5072_);
lean_dec_ref(v___x_5071_);
lean_dec_ref(v___x_5070_);
v___x_5156_ = lean_box(0);
v___x_5157_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_5118_, v_a_5117_, v___x_5069_, v___x_5156_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
v___y_5091_ = v___x_5157_;
goto v___jp_5090_;
}
else
{
lean_inc_ref(v_type_5122_);
lean_dec(v_snd_5118_);
lean_dec(v_a_5117_);
lean_dec(v___x_5069_);
goto v___jp_5130_;
}
}
v___jp_5127_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5128_ = lean_box(0);
v___x_5129_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_5113_, v___f_5126_, v___x_5128_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
v___y_5091_ = v___x_5129_;
goto v___jp_5090_;
}
v___jp_5130_:
{
lean_object* v_options_5131_; uint8_t v_hasTrace_5132_; 
v_options_5131_ = lean_ctor_get(v___y_5087_, 2);
v_hasTrace_5132_ = lean_ctor_get_uint8(v_options_5131_, sizeof(void*)*1);
if (v_hasTrace_5132_ == 0)
{
lean_dec_ref(v_type_5122_);
lean_dec(v___f_5073_);
lean_dec_ref(v_toMonadRef_5072_);
lean_dec_ref(v___x_5071_);
lean_dec_ref(v___x_5070_);
goto v___jp_5127_;
}
else
{
lean_object* v_inheritedTraceOptions_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; uint8_t v___x_5136_; 
v_inheritedTraceOptions_5133_ = lean_ctor_get(v___y_5087_, 13);
v___x_5134_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_5135_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_5136_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5133_, v_options_5131_, v___x_5135_);
if (v___x_5136_ == 0)
{
lean_dec_ref(v_type_5122_);
lean_dec(v___f_5073_);
lean_dec_ref(v_toMonadRef_5072_);
lean_dec_ref(v___x_5071_);
lean_dec_ref(v___x_5070_);
goto v___jp_5127_;
}
else
{
lean_object* v_type_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_22071__overap_5143_; lean_object* v___x_5144_; 
v_type_5137_ = lean_ctor_get(v___x_5115_, 1);
lean_inc_ref(v_type_5137_);
v___x_5138_ = l_Lean_MessageData_ofExpr(v_type_5137_);
v___x_5139_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_5140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5140_, 0, v___x_5138_);
lean_ctor_set(v___x_5140_, 1, v___x_5139_);
v___x_5141_ = l_Lean_MessageData_ofExpr(v_type_5122_);
v___x_5142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5142_, 0, v___x_5140_);
lean_ctor_set(v___x_5142_, 1, v___x_5141_);
v___x_22071__overap_5143_ = l_Lean_addTrace___redArg(v___x_5070_, v___x_5071_, v_toMonadRef_5072_, v___f_5073_, v___x_5134_, v___x_5142_);
lean_inc(v___y_5088_);
lean_inc_ref(v___y_5087_);
lean_inc(v___y_5086_);
lean_inc_ref(v___y_5085_);
lean_inc(v___y_5084_);
lean_inc_ref(v___y_5083_);
lean_inc(v___y_5082_);
lean_inc_ref(v___y_5081_);
lean_inc(v___y_5080_);
lean_inc(v___y_5079_);
lean_inc_ref(v___y_5078_);
v___x_5144_ = lean_apply_12(v___x_22071__overap_5143_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, lean_box(0));
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v___x_5146_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5144_, 1);
v___x_5146_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_5113_, v___f_5126_, v_a_5145_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
v___y_5091_ = v___x_5146_;
goto v___jp_5090_;
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_dec_ref(v___f_5126_);
lean_dec_ref(v_G_5077_);
v_a_5147_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5144_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5144_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5158_; 
lean_inc_ref(v_value_5123_);
lean_dec(v_a_5117_);
lean_dec_ref(v_G_5077_);
lean_dec(v___f_5073_);
lean_dec_ref(v_toMonadRef_5072_);
lean_dec_ref(v___x_5071_);
lean_dec_ref(v___x_5070_);
lean_dec(v___x_5069_);
v___x_5158_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5123_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_object* v___x_5160_; uint8_t v_isShared_5161_; uint8_t v_isSharedCheck_5170_; 
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5170_ == 0)
{
lean_object* v_unused_5171_; 
v_unused_5171_ = lean_ctor_get(v___x_5158_, 0);
lean_dec(v_unused_5171_);
v___x_5160_ = v___x_5158_;
v_isShared_5161_ = v_isSharedCheck_5170_;
goto v_resetjp_5159_;
}
else
{
lean_dec(v___x_5158_);
v___x_5160_ = lean_box(0);
v_isShared_5161_ = v_isSharedCheck_5170_;
goto v_resetjp_5159_;
}
v_resetjp_5159_:
{
lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5165_; 
v___x_5162_ = lean_box(v___x_5124_);
v___x_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5162_);
if (v_isShared_5121_ == 0)
{
lean_ctor_set(v___x_5120_, 0, v___x_5163_);
v___x_5165_ = v___x_5120_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5163_);
lean_ctor_set(v_reuseFailAlloc_5169_, 1, v_snd_5118_);
v___x_5165_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
lean_object* v___x_5167_; 
if (v_isShared_5161_ == 0)
{
lean_ctor_set(v___x_5160_, 0, v___x_5165_);
v___x_5167_ = v___x_5160_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v___x_5165_);
v___x_5167_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
return v___x_5167_;
}
}
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_del_object(v___x_5120_);
lean_dec(v_snd_5118_);
v_a_5172_ = lean_ctor_get(v___x_5158_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5158_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5158_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec_ref(v_G_5077_);
lean_dec_ref(v_acc_5075_);
lean_dec(v___f_5073_);
lean_dec_ref(v_toMonadRef_5072_);
lean_dec_ref(v___x_5071_);
lean_dec_ref(v___x_5070_);
lean_dec(v___x_5069_);
v_a_5182_ = lean_ctor_get(v___x_5116_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5116_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5116_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
v___jp_5090_:
{
if (lean_obj_tag(v___y_5091_) == 0)
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5104_; 
v_a_5092_ = lean_ctor_get(v___y_5091_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___y_5091_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5094_ = v___y_5091_;
v_isShared_5095_ = v_isSharedCheck_5104_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___y_5091_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5104_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
if (lean_obj_tag(v_a_5092_) == 0)
{
lean_object* v_a_5096_; lean_object* v___x_5098_; 
lean_dec_ref(v_G_5077_);
v_a_5096_ = lean_ctor_get(v_a_5092_, 0);
lean_inc(v_a_5096_);
lean_dec_ref_known(v_a_5092_, 1);
if (v_isShared_5095_ == 0)
{
lean_ctor_set(v___x_5094_, 0, v_a_5096_);
v___x_5098_ = v___x_5094_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5096_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
lean_del_object(v___x_5094_);
v_a_5100_ = lean_ctor_get(v_a_5092_, 0);
lean_inc(v_a_5100_);
lean_dec_ref_known(v_a_5092_, 1);
v___x_5101_ = lean_unsigned_to_nat(1u);
v___x_5102_ = lean_nat_add(v_next_5074_, v___x_5101_);
lean_inc(v___y_5088_);
lean_inc_ref(v___y_5087_);
lean_inc(v___y_5086_);
lean_inc_ref(v___y_5085_);
lean_inc(v___y_5084_);
lean_inc_ref(v___y_5083_);
lean_inc(v___y_5082_);
lean_inc_ref(v___y_5081_);
lean_inc(v___y_5080_);
lean_inc(v___y_5079_);
lean_inc_ref(v___y_5078_);
v___x_5103_ = lean_apply_16(v_G_5077_, v___x_5102_, v_a_5100_, lean_box(0), lean_box(0), v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, lean_box(0));
return v___x_5103_;
}
}
}
else
{
lean_object* v_a_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5112_; 
lean_dec_ref(v_G_5077_);
v_a_5105_ = lean_ctor_get(v___y_5091_, 0);
v_isSharedCheck_5112_ = !lean_is_exclusive(v___y_5091_);
if (v_isSharedCheck_5112_ == 0)
{
v___x_5107_ = v___y_5091_;
v_isShared_5108_ = v_isSharedCheck_5112_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_a_5105_);
lean_dec(v___y_5091_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5112_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v___x_5110_; 
if (v_isShared_5108_ == 0)
{
v___x_5110_ = v___x_5107_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v_a_5105_);
v___x_5110_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
return v___x_5110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_5190_ = _args[0];
lean_object* v_hypotheses_5191_ = _args[1];
lean_object* v_cacheId_5192_ = _args[2];
lean_object* v_methods_5193_ = _args[3];
lean_object* v_config_5194_ = _args[4];
lean_object* v___x_5195_ = _args[5];
lean_object* v___x_5196_ = _args[6];
lean_object* v___x_5197_ = _args[7];
lean_object* v_toMonadRef_5198_ = _args[8];
lean_object* v___f_5199_ = _args[9];
lean_object* v_next_5200_ = _args[10];
lean_object* v_acc_5201_ = _args[11];
lean_object* v_h_5202_ = _args[12];
lean_object* v_G_5203_ = _args[13];
lean_object* v___y_5204_ = _args[14];
lean_object* v___y_5205_ = _args[15];
lean_object* v___y_5206_ = _args[16];
lean_object* v___y_5207_ = _args[17];
lean_object* v___y_5208_ = _args[18];
lean_object* v___y_5209_ = _args[19];
lean_object* v___y_5210_ = _args[20];
lean_object* v___y_5211_ = _args[21];
lean_object* v___y_5212_ = _args[22];
lean_object* v___y_5213_ = _args[23];
lean_object* v___y_5214_ = _args[24];
lean_object* v___y_5215_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_5216_; lean_object* v_res_5217_; 
v_cacheId_boxed_5216_ = lean_unbox(v_cacheId_5192_);
v_res_5217_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_5190_, v_hypotheses_5191_, v_cacheId_boxed_5216_, v_methods_5193_, v_config_5194_, v___x_5195_, v___x_5196_, v___x_5197_, v_toMonadRef_5198_, v___f_5199_, v_next_5200_, v_acc_5201_, v_h_5202_, v_G_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
lean_dec(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec(v_next_5200_);
lean_dec_ref(v_hypotheses_5191_);
lean_dec(v___x_5190_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_5218_, lean_object* v_methods_5219_, lean_object* v_config_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_){
_start:
{
lean_object* v___x_5233_; lean_object* v_toApplicative_5234_; lean_object* v_toFunctor_5235_; lean_object* v_toSeq_5236_; lean_object* v_toSeqLeft_5237_; lean_object* v_toSeqRight_5238_; lean_object* v___f_5239_; lean_object* v___f_5240_; lean_object* v___f_5241_; lean_object* v___f_5242_; lean_object* v___x_5243_; lean_object* v___f_5244_; lean_object* v___f_5245_; lean_object* v___f_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v_toApplicative_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5337_; 
v___x_5233_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5234_ = lean_ctor_get(v___x_5233_, 0);
v_toFunctor_5235_ = lean_ctor_get(v_toApplicative_5234_, 0);
v_toSeq_5236_ = lean_ctor_get(v_toApplicative_5234_, 2);
v_toSeqLeft_5237_ = lean_ctor_get(v_toApplicative_5234_, 3);
v_toSeqRight_5238_ = lean_ctor_get(v_toApplicative_5234_, 4);
v___f_5239_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5240_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5235_, 2);
v___f_5241_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5241_, 0, v_toFunctor_5235_);
v___f_5242_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5242_, 0, v_toFunctor_5235_);
v___x_5243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___f_5241_);
lean_ctor_set(v___x_5243_, 1, v___f_5242_);
lean_inc(v_toSeqRight_5238_);
v___f_5244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5244_, 0, v_toSeqRight_5238_);
lean_inc(v_toSeqLeft_5237_);
v___f_5245_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5245_, 0, v_toSeqLeft_5237_);
lean_inc(v_toSeq_5236_);
v___f_5246_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5246_, 0, v_toSeq_5236_);
v___x_5247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5243_);
lean_ctor_set(v___x_5247_, 1, v___f_5239_);
lean_ctor_set(v___x_5247_, 2, v___f_5246_);
lean_ctor_set(v___x_5247_, 3, v___f_5245_);
lean_ctor_set(v___x_5247_, 4, v___f_5244_);
v___x_5248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5247_);
lean_ctor_set(v___x_5248_, 1, v___f_5240_);
v___x_5249_ = l_StateRefT_x27_instMonad___redArg(v___x_5248_);
v_toApplicative_5250_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5337_ == 0)
{
lean_object* v_unused_5338_; 
v_unused_5338_ = lean_ctor_get(v___x_5249_, 1);
lean_dec(v_unused_5338_);
v___x_5252_ = v___x_5249_;
v_isShared_5253_ = v_isSharedCheck_5337_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_toApplicative_5250_);
lean_dec(v___x_5249_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5337_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v_toFunctor_5254_; lean_object* v_toSeq_5255_; lean_object* v_toSeqLeft_5256_; lean_object* v_toSeqRight_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5335_; 
v_toFunctor_5254_ = lean_ctor_get(v_toApplicative_5250_, 0);
v_toSeq_5255_ = lean_ctor_get(v_toApplicative_5250_, 2);
v_toSeqLeft_5256_ = lean_ctor_get(v_toApplicative_5250_, 3);
v_toSeqRight_5257_ = lean_ctor_get(v_toApplicative_5250_, 4);
v_isSharedCheck_5335_ = !lean_is_exclusive(v_toApplicative_5250_);
if (v_isSharedCheck_5335_ == 0)
{
lean_object* v_unused_5336_; 
v_unused_5336_ = lean_ctor_get(v_toApplicative_5250_, 1);
lean_dec(v_unused_5336_);
v___x_5259_ = v_toApplicative_5250_;
v_isShared_5260_ = v_isSharedCheck_5335_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_toSeqRight_5257_);
lean_inc(v_toSeqLeft_5256_);
lean_inc(v_toSeq_5255_);
lean_inc(v_toFunctor_5254_);
lean_dec(v_toApplicative_5250_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5335_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___f_5261_; lean_object* v___f_5262_; lean_object* v___f_5263_; lean_object* v___f_5264_; lean_object* v___x_5265_; lean_object* v___f_5266_; lean_object* v___f_5267_; lean_object* v___f_5268_; lean_object* v___x_5270_; 
v___f_5261_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5262_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5254_);
v___f_5263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5263_, 0, v_toFunctor_5254_);
v___f_5264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5264_, 0, v_toFunctor_5254_);
v___x_5265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5265_, 0, v___f_5263_);
lean_ctor_set(v___x_5265_, 1, v___f_5264_);
v___f_5266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5266_, 0, v_toSeqRight_5257_);
v___f_5267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5267_, 0, v_toSeqLeft_5256_);
v___f_5268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5268_, 0, v_toSeq_5255_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 4, v___f_5266_);
lean_ctor_set(v___x_5259_, 3, v___f_5267_);
lean_ctor_set(v___x_5259_, 2, v___f_5268_);
lean_ctor_set(v___x_5259_, 1, v___f_5261_);
lean_ctor_set(v___x_5259_, 0, v___x_5265_);
v___x_5270_ = v___x_5259_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5265_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v___f_5261_);
lean_ctor_set(v_reuseFailAlloc_5334_, 2, v___f_5268_);
lean_ctor_set(v_reuseFailAlloc_5334_, 3, v___f_5267_);
lean_ctor_set(v_reuseFailAlloc_5334_, 4, v___f_5266_);
v___x_5270_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
lean_object* v___x_5272_; 
if (v_isShared_5253_ == 0)
{
lean_ctor_set(v___x_5252_, 1, v___f_5262_);
lean_ctor_set(v___x_5252_, 0, v___x_5270_);
v___x_5272_ = v___x_5252_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5270_);
lean_ctor_set(v_reuseFailAlloc_5333_, 1, v___f_5262_);
v___x_5272_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v_toMonadRef_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v_hypotheses_5284_; lean_object* v___f_5285_; lean_object* v___x_5286_; lean_object* v_newHyps_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___f_5291_; lean_object* v___x_5292_; lean_object* v___x_21853__overap_5293_; lean_object* v___x_5294_; 
v___x_5273_ = l_StateRefT_x27_instMonad___redArg(v___x_5272_);
v___x_5274_ = l_ReaderT_instMonad___redArg(v___x_5273_);
v___x_5275_ = l_StateRefT_x27_instMonad___redArg(v___x_5274_);
v___x_5276_ = l_ReaderT_instMonad___redArg(v___x_5275_);
v___x_5277_ = l_ReaderT_instMonad___redArg(v___x_5276_);
v___x_5278_ = l_StateRefT_x27_instMonad___redArg(v___x_5277_);
v___x_5279_ = l_ReaderT_instMonad___redArg(v___x_5278_);
v___x_5280_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_5281_ = lean_ctor_get(v___x_5280_, 0);
v___x_5282_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5283_ = lean_st_ref_get(v_a_5222_);
v_hypotheses_5284_ = lean_ctor_get(v___x_5283_, 3);
lean_inc_ref(v_hypotheses_5284_);
lean_dec(v___x_5283_);
v___f_5285_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_5286_ = lean_array_get_size(v_hypotheses_5284_);
v_newHyps_5287_ = lean_mk_empty_array_with_capacity(v___x_5286_);
v___x_5288_ = lean_unsigned_to_nat(0u);
v___x_5289_ = lean_box(0);
v___x_5290_ = lean_box(v_cacheId_5218_);
lean_inc_ref(v_toMonadRef_5281_);
v___f_5291_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_5291_, 0, v___x_5286_);
lean_closure_set(v___f_5291_, 1, v_hypotheses_5284_);
lean_closure_set(v___f_5291_, 2, v___x_5290_);
lean_closure_set(v___f_5291_, 3, v_methods_5219_);
lean_closure_set(v___f_5291_, 4, v_config_5220_);
lean_closure_set(v___f_5291_, 5, v___x_5289_);
lean_closure_set(v___f_5291_, 6, v___x_5279_);
lean_closure_set(v___f_5291_, 7, v___x_5282_);
lean_closure_set(v___f_5291_, 8, v_toMonadRef_5281_);
lean_closure_set(v___f_5291_, 9, v___f_5285_);
v___x_5292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5289_);
lean_ctor_set(v___x_5292_, 1, v_newHyps_5287_);
v___x_21853__overap_5293_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_5291_, v___x_5288_, v___x_5292_, lean_box(0));
lean_inc(v_a_5231_);
lean_inc_ref(v_a_5230_);
lean_inc(v_a_5229_);
lean_inc_ref(v_a_5228_);
lean_inc(v_a_5227_);
lean_inc_ref(v_a_5226_);
lean_inc(v_a_5225_);
lean_inc_ref(v_a_5224_);
lean_inc(v_a_5223_);
lean_inc(v_a_5222_);
lean_inc_ref(v_a_5221_);
v___x_5294_ = lean_apply_12(v___x_21853__overap_5293_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, lean_box(0));
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5324_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5297_ = v___x_5294_;
v_isShared_5298_ = v_isSharedCheck_5324_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___x_5294_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5324_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v_fst_5299_; 
v_fst_5299_ = lean_ctor_get(v_a_5295_, 0);
if (lean_obj_tag(v_fst_5299_) == 0)
{
lean_object* v_snd_5300_; lean_object* v___x_5301_; lean_object* v_caches_5302_; lean_object* v_typeAnalysis_5303_; lean_object* v_target_5304_; uint8_t v_didChange_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5318_; 
v_snd_5300_ = lean_ctor_get(v_a_5295_, 1);
lean_inc(v_snd_5300_);
lean_dec(v_a_5295_);
v___x_5301_ = lean_st_ref_take(v_a_5222_);
v_caches_5302_ = lean_ctor_get(v___x_5301_, 0);
v_typeAnalysis_5303_ = lean_ctor_get(v___x_5301_, 1);
v_target_5304_ = lean_ctor_get(v___x_5301_, 2);
v_didChange_5305_ = lean_ctor_get_uint8(v___x_5301_, sizeof(void*)*4);
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5318_ == 0)
{
lean_object* v_unused_5319_; 
v_unused_5319_ = lean_ctor_get(v___x_5301_, 3);
lean_dec(v_unused_5319_);
v___x_5307_ = v___x_5301_;
v_isShared_5308_ = v_isSharedCheck_5318_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_target_5304_);
lean_inc(v_typeAnalysis_5303_);
lean_inc(v_caches_5302_);
lean_dec(v___x_5301_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5318_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 3, v_snd_5300_);
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_caches_5302_);
lean_ctor_set(v_reuseFailAlloc_5317_, 1, v_typeAnalysis_5303_);
lean_ctor_set(v_reuseFailAlloc_5317_, 2, v_target_5304_);
lean_ctor_set(v_reuseFailAlloc_5317_, 3, v_snd_5300_);
lean_ctor_set_uint8(v_reuseFailAlloc_5317_, sizeof(void*)*4, v_didChange_5305_);
v___x_5310_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
lean_object* v___x_5311_; uint8_t v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5315_; 
v___x_5311_ = lean_st_ref_put(v_a_5222_, v___x_5310_);
v___x_5312_ = 0;
v___x_5313_ = lean_box(v___x_5312_);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v___x_5313_);
v___x_5315_ = v___x_5297_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5313_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
else
{
lean_object* v_val_5320_; lean_object* v___x_5322_; 
lean_inc_ref(v_fst_5299_);
lean_dec(v_a_5295_);
v_val_5320_ = lean_ctor_get(v_fst_5299_, 0);
lean_inc(v_val_5320_);
lean_dec_ref_known(v_fst_5299_, 1);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v_val_5320_);
v___x_5322_ = v___x_5297_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_val_5320_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
v_a_5325_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5294_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5294_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5325_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_5339_, lean_object* v_methods_5340_, lean_object* v_config_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_){
_start:
{
uint8_t v_cacheId_boxed_5354_; lean_object* v_res_5355_; 
v_cacheId_boxed_5354_ = lean_unbox(v_cacheId_5339_);
v_res_5355_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_5354_, v_methods_5340_, v_config_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec_ref(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec_ref(v_a_5347_);
lean_dec(v_a_5346_);
lean_dec_ref(v_a_5345_);
lean_dec(v_a_5344_);
lean_dec(v_a_5343_);
lean_dec_ref(v_a_5342_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_5356_, lean_object* v_a_5357_, lean_object* v___x_5358_, lean_object* v_____r_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_){
_start:
{
lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; 
v___x_5373_ = lean_array_push(v_snd_5356_, v_a_5357_);
v___x_5374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5374_, 0, v___x_5358_);
lean_ctor_set(v___x_5374_, 1, v___x_5373_);
v___x_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5374_);
v___x_5376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5376_, 0, v___x_5375_);
return v___x_5376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_5377_ = _args[0];
lean_object* v_a_5378_ = _args[1];
lean_object* v___x_5379_ = _args[2];
lean_object* v_____r_5380_ = _args[3];
lean_object* v___y_5381_ = _args[4];
lean_object* v___y_5382_ = _args[5];
lean_object* v___y_5383_ = _args[6];
lean_object* v___y_5384_ = _args[7];
lean_object* v___y_5385_ = _args[8];
lean_object* v___y_5386_ = _args[9];
lean_object* v___y_5387_ = _args[10];
lean_object* v___y_5388_ = _args[11];
lean_object* v___y_5389_ = _args[12];
lean_object* v___y_5390_ = _args[13];
lean_object* v___y_5391_ = _args[14];
lean_object* v___y_5392_ = _args[15];
lean_object* v___y_5393_ = _args[16];
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5377_, v_a_5378_, v___x_5379_, v_____r_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
lean_dec(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
return v_res_5394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_5395_, lean_object* v___f_5396_, lean_object* v_____r_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_){
_start:
{
lean_object* v___x_5411_; lean_object* v_caches_5412_; lean_object* v_typeAnalysis_5413_; lean_object* v_target_5414_; lean_object* v_hypotheses_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5425_; 
v___x_5411_ = lean_st_ref_take(v___y_5400_);
v_caches_5412_ = lean_ctor_get(v___x_5411_, 0);
v_typeAnalysis_5413_ = lean_ctor_get(v___x_5411_, 1);
v_target_5414_ = lean_ctor_get(v___x_5411_, 2);
v_hypotheses_5415_ = lean_ctor_get(v___x_5411_, 3);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5417_ = v___x_5411_;
v_isShared_5418_ = v_isSharedCheck_5425_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_hypotheses_5415_);
lean_inc(v_target_5414_);
lean_inc(v_typeAnalysis_5413_);
lean_inc(v_caches_5412_);
lean_dec(v___x_5411_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5425_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_caches_5412_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_typeAnalysis_5413_);
lean_ctor_set(v_reuseFailAlloc_5424_, 2, v_target_5414_);
lean_ctor_set(v_reuseFailAlloc_5424_, 3, v_hypotheses_5415_);
v___x_5420_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
lean_ctor_set_uint8(v___x_5420_, sizeof(void*)*4, v___x_5395_);
v___x_5421_ = lean_st_ref_put(v___y_5400_, v___x_5420_);
v___x_5422_ = lean_box(0);
lean_inc(v___y_5409_);
lean_inc_ref(v___y_5408_);
lean_inc(v___y_5407_);
lean_inc_ref(v___y_5406_);
lean_inc(v___y_5405_);
lean_inc_ref(v___y_5404_);
lean_inc(v___y_5403_);
lean_inc_ref(v___y_5402_);
lean_inc(v___y_5401_);
lean_inc(v___y_5400_);
lean_inc_ref(v___y_5399_);
lean_inc(v___y_5398_);
v___x_5423_ = lean_apply_14(v___f_5396_, v___x_5422_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, lean_box(0));
return v___x_5423_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_5426_, lean_object* v___f_5427_, lean_object* v_____r_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_){
_start:
{
uint8_t v___x_35638__boxed_5442_; lean_object* v_res_5443_; 
v___x_35638__boxed_5442_ = lean_unbox(v___x_5426_);
v_res_5443_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35638__boxed_5442_, v___f_5427_, v_____r_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec(v___y_5431_);
lean_dec_ref(v___y_5430_);
lean_dec(v___y_5429_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_){
_start:
{
lean_object* v___x_5450_; lean_object* v_env_5451_; lean_object* v___x_5452_; lean_object* v_mctx_5453_; lean_object* v_lctx_5454_; lean_object* v_options_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; 
v___x_5450_ = lean_st_ref_get(v___y_5448_);
v_env_5451_ = lean_ctor_get(v___x_5450_, 0);
lean_inc_ref(v_env_5451_);
lean_dec(v___x_5450_);
v___x_5452_ = lean_st_ref_get(v___y_5446_);
v_mctx_5453_ = lean_ctor_get(v___x_5452_, 0);
lean_inc_ref(v_mctx_5453_);
lean_dec(v___x_5452_);
v_lctx_5454_ = lean_ctor_get(v___y_5445_, 2);
v_options_5455_ = lean_ctor_get(v___y_5447_, 2);
lean_inc_ref(v_options_5455_);
lean_inc_ref(v_lctx_5454_);
v___x_5456_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5456_, 0, v_env_5451_);
lean_ctor_set(v___x_5456_, 1, v_mctx_5453_);
lean_ctor_set(v___x_5456_, 2, v_lctx_5454_);
lean_ctor_set(v___x_5456_, 3, v_options_5455_);
v___x_5457_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5456_);
lean_ctor_set(v___x_5457_, 1, v_msgData_5444_);
v___x_5458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5458_, 0, v___x_5457_);
return v___x_5458_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
return v_res_5465_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5466_; double v___x_5467_; 
v___x_5466_ = lean_unsigned_to_nat(0u);
v___x_5467_ = lean_float_of_nat(v___x_5466_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_5471_, lean_object* v_msg_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v_ref_5478_; lean_object* v___x_5479_; lean_object* v_a_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5524_; 
v_ref_5478_ = lean_ctor_get(v___y_5475_, 5);
v___x_5479_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
v_a_5480_ = lean_ctor_get(v___x_5479_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5479_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5482_ = v___x_5479_;
v_isShared_5483_ = v_isSharedCheck_5524_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_a_5480_);
lean_dec(v___x_5479_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5524_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5484_; lean_object* v_traceState_5485_; lean_object* v_env_5486_; lean_object* v_nextMacroScope_5487_; lean_object* v_ngen_5488_; lean_object* v_auxDeclNGen_5489_; lean_object* v_cache_5490_; lean_object* v_messages_5491_; lean_object* v_infoState_5492_; lean_object* v_snapshotTasks_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5523_; 
v___x_5484_ = lean_st_ref_take(v___y_5476_);
v_traceState_5485_ = lean_ctor_get(v___x_5484_, 4);
v_env_5486_ = lean_ctor_get(v___x_5484_, 0);
v_nextMacroScope_5487_ = lean_ctor_get(v___x_5484_, 1);
v_ngen_5488_ = lean_ctor_get(v___x_5484_, 2);
v_auxDeclNGen_5489_ = lean_ctor_get(v___x_5484_, 3);
v_cache_5490_ = lean_ctor_get(v___x_5484_, 5);
v_messages_5491_ = lean_ctor_get(v___x_5484_, 6);
v_infoState_5492_ = lean_ctor_get(v___x_5484_, 7);
v_snapshotTasks_5493_ = lean_ctor_get(v___x_5484_, 8);
v_isSharedCheck_5523_ = !lean_is_exclusive(v___x_5484_);
if (v_isSharedCheck_5523_ == 0)
{
v___x_5495_ = v___x_5484_;
v_isShared_5496_ = v_isSharedCheck_5523_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_snapshotTasks_5493_);
lean_inc(v_infoState_5492_);
lean_inc(v_messages_5491_);
lean_inc(v_cache_5490_);
lean_inc(v_traceState_5485_);
lean_inc(v_auxDeclNGen_5489_);
lean_inc(v_ngen_5488_);
lean_inc(v_nextMacroScope_5487_);
lean_inc(v_env_5486_);
lean_dec(v___x_5484_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5523_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
uint64_t v_tid_5497_; lean_object* v_traces_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5522_; 
v_tid_5497_ = lean_ctor_get_uint64(v_traceState_5485_, sizeof(void*)*1);
v_traces_5498_ = lean_ctor_get(v_traceState_5485_, 0);
v_isSharedCheck_5522_ = !lean_is_exclusive(v_traceState_5485_);
if (v_isSharedCheck_5522_ == 0)
{
v___x_5500_ = v_traceState_5485_;
v_isShared_5501_ = v_isSharedCheck_5522_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_traces_5498_);
lean_dec(v_traceState_5485_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5522_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5502_; double v___x_5503_; uint8_t v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5512_; 
v___x_5502_ = lean_box(0);
v___x_5503_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5504_ = 0;
v___x_5505_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5506_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5506_, 0, v_cls_5471_);
lean_ctor_set(v___x_5506_, 1, v___x_5502_);
lean_ctor_set(v___x_5506_, 2, v___x_5505_);
lean_ctor_set_float(v___x_5506_, sizeof(void*)*3, v___x_5503_);
lean_ctor_set_float(v___x_5506_, sizeof(void*)*3 + 8, v___x_5503_);
lean_ctor_set_uint8(v___x_5506_, sizeof(void*)*3 + 16, v___x_5504_);
v___x_5507_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5508_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5508_, 0, v___x_5506_);
lean_ctor_set(v___x_5508_, 1, v_a_5480_);
lean_ctor_set(v___x_5508_, 2, v___x_5507_);
lean_inc(v_ref_5478_);
v___x_5509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5509_, 0, v_ref_5478_);
lean_ctor_set(v___x_5509_, 1, v___x_5508_);
v___x_5510_ = l_Lean_PersistentArray_push___redArg(v_traces_5498_, v___x_5509_);
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 0, v___x_5510_);
v___x_5512_ = v___x_5500_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5510_);
lean_ctor_set_uint64(v_reuseFailAlloc_5521_, sizeof(void*)*1, v_tid_5497_);
v___x_5512_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
lean_object* v___x_5514_; 
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 4, v___x_5512_);
v___x_5514_ = v___x_5495_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_env_5486_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_nextMacroScope_5487_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_ngen_5488_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v_auxDeclNGen_5489_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v___x_5512_);
lean_ctor_set(v_reuseFailAlloc_5520_, 5, v_cache_5490_);
lean_ctor_set(v_reuseFailAlloc_5520_, 6, v_messages_5491_);
lean_ctor_set(v_reuseFailAlloc_5520_, 7, v_infoState_5492_);
lean_ctor_set(v_reuseFailAlloc_5520_, 8, v_snapshotTasks_5493_);
v___x_5514_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5518_; 
v___x_5515_ = lean_st_ref_put(v___y_5476_, v___x_5514_);
v___x_5516_ = lean_box(0);
if (v_isShared_5483_ == 0)
{
lean_ctor_set(v___x_5482_, 0, v___x_5516_);
v___x_5518_ = v___x_5482_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v___x_5516_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5525_, lean_object* v_msg_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_){
_start:
{
lean_object* v_res_5532_; 
v_res_5532_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5525_, v_msg_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_);
lean_dec(v___y_5530_);
lean_dec_ref(v___y_5529_);
lean_dec(v___y_5528_);
lean_dec_ref(v___y_5527_);
return v_res_5532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5533_, lean_object* v___x_5534_, lean_object* v_methods_5535_, lean_object* v_config_5536_, lean_object* v_a_5537_, lean_object* v_b_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_){
_start:
{
lean_object* v___y_5553_; uint8_t v___x_5575_; 
v___x_5575_ = lean_nat_dec_lt(v_a_5537_, v_upperBound_5533_);
if (v___x_5575_ == 0)
{
lean_object* v___x_5576_; 
lean_dec(v_a_5537_);
lean_dec_ref(v_config_5536_);
lean_dec_ref(v_methods_5535_);
v___x_5576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5576_, 0, v_b_5538_);
return v___x_5576_;
}
else
{
lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v_type_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; 
v___x_5577_ = lean_st_ref_take(v___y_5539_);
v___x_5578_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_5579_ = lean_st_ref_put(v___y_5539_, v___x_5578_);
v___x_5580_ = lean_array_fget_borrowed(v___x_5534_, v_a_5537_);
v_type_5581_ = lean_ctor_get(v___x_5580_, 1);
v___x_5582_ = lean_unsigned_to_nat(0u);
v___x_5583_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5583_, 0, v___x_5582_);
lean_ctor_set(v___x_5583_, 1, v___x_5577_);
lean_ctor_set(v___x_5583_, 2, v___x_5578_);
lean_ctor_set(v___x_5583_, 3, v___x_5578_);
lean_inc_ref(v_type_5581_);
v___x_5584_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5584_, 0, v_type_5581_);
lean_inc_ref(v_config_5536_);
lean_inc_ref(v_methods_5535_);
v___x_5585_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5584_, v_methods_5535_, v_config_5536_, v___x_5583_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
if (lean_obj_tag(v___x_5585_) == 0)
{
lean_object* v_a_5586_; lean_object* v_snd_5587_; lean_object* v_fst_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5668_; 
v_a_5586_ = lean_ctor_get(v___x_5585_, 0);
lean_inc(v_a_5586_);
lean_dec_ref_known(v___x_5585_, 1);
v_snd_5587_ = lean_ctor_get(v_a_5586_, 1);
v_fst_5588_ = lean_ctor_get(v_a_5586_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v_a_5586_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5590_ = v_a_5586_;
v_isShared_5591_ = v_isSharedCheck_5668_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_snd_5587_);
lean_inc(v_fst_5588_);
lean_dec(v_a_5586_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5668_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v_persistentCache_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
v_persistentCache_5592_ = lean_ctor_get(v_snd_5587_, 1);
lean_inc_ref(v_persistentCache_5592_);
lean_dec(v_snd_5587_);
v___x_5593_ = lean_st_ref_swap(v___y_5539_, v_persistentCache_5592_);
lean_dec(v___x_5593_);
lean_inc(v___x_5580_);
v___x_5594_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5580_, v_fst_5588_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v_a_5595_; lean_object* v_snd_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5658_; 
v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
lean_inc(v_a_5595_);
lean_dec_ref_known(v___x_5594_, 1);
v_snd_5596_ = lean_ctor_get(v_b_5538_, 1);
v_isSharedCheck_5658_ = !lean_is_exclusive(v_b_5538_);
if (v_isSharedCheck_5658_ == 0)
{
lean_object* v_unused_5659_; 
v_unused_5659_ = lean_ctor_get(v_b_5538_, 0);
lean_dec(v_unused_5659_);
v___x_5598_ = v_b_5538_;
v_isShared_5599_ = v_isSharedCheck_5658_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_snd_5596_);
lean_dec(v_b_5538_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5658_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v_type_5600_; lean_object* v_value_5601_; uint8_t v___x_5602_; 
v_type_5600_ = lean_ctor_get(v_a_5595_, 1);
v_value_5601_ = lean_ctor_get(v_a_5595_, 2);
lean_inc_ref(v_type_5600_);
v___x_5602_ = l_Lean_Expr_isFalse(v_type_5600_);
if (v___x_5602_ == 0)
{
lean_object* v___x_5603_; lean_object* v___f_5604_; uint8_t v___x_5633_; 
lean_del_object(v___x_5598_);
v___x_5603_ = lean_box(0);
lean_inc(v_a_5595_);
lean_inc(v_snd_5596_);
v___f_5604_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5604_, 0, v_snd_5596_);
lean_closure_set(v___f_5604_, 1, v_a_5595_);
lean_closure_set(v___f_5604_, 2, v___x_5603_);
v___x_5633_ = lean_expr_eqv(v_type_5581_, v_type_5600_);
if (v___x_5633_ == 0)
{
lean_inc_ref(v_type_5600_);
lean_dec(v_snd_5596_);
lean_dec(v_a_5595_);
goto v___jp_5608_;
}
else
{
if (v___x_5602_ == 0)
{
lean_object* v___x_5634_; lean_object* v___x_5635_; 
lean_dec_ref(v___f_5604_);
lean_del_object(v___x_5590_);
v___x_5634_ = lean_box(0);
v___x_5635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5596_, v_a_5595_, v___x_5603_, v___x_5634_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
v___y_5553_ = v___x_5635_;
goto v___jp_5552_;
}
else
{
lean_inc_ref(v_type_5600_);
lean_dec(v_snd_5596_);
lean_dec(v_a_5595_);
goto v___jp_5608_;
}
}
v___jp_5605_:
{
lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___x_5606_ = lean_box(0);
v___x_5607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5575_, v___f_5604_, v___x_5606_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
v___y_5553_ = v___x_5607_;
goto v___jp_5552_;
}
v___jp_5608_:
{
lean_object* v_options_5609_; uint8_t v_hasTrace_5610_; 
v_options_5609_ = lean_ctor_get(v___y_5549_, 2);
v_hasTrace_5610_ = lean_ctor_get_uint8(v_options_5609_, sizeof(void*)*1);
if (v_hasTrace_5610_ == 0)
{
lean_dec_ref(v_type_5600_);
lean_del_object(v___x_5590_);
goto v___jp_5605_;
}
else
{
lean_object* v_inheritedTraceOptions_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; uint8_t v___x_5614_; 
v_inheritedTraceOptions_5611_ = lean_ctor_get(v___y_5549_, 13);
v___x_5612_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_5613_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_5614_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5611_, v_options_5609_, v___x_5613_);
if (v___x_5614_ == 0)
{
lean_dec_ref(v_type_5600_);
lean_del_object(v___x_5590_);
goto v___jp_5605_;
}
else
{
lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5618_; 
lean_inc_ref(v_type_5581_);
v___x_5615_ = l_Lean_MessageData_ofExpr(v_type_5581_);
v___x_5616_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5591_ == 0)
{
lean_ctor_set_tag(v___x_5590_, 7);
lean_ctor_set(v___x_5590_, 1, v___x_5616_);
lean_ctor_set(v___x_5590_, 0, v___x_5615_);
v___x_5618_ = v___x_5590_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v___x_5615_);
lean_ctor_set(v_reuseFailAlloc_5632_, 1, v___x_5616_);
v___x_5618_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; 
v___x_5619_ = l_Lean_MessageData_ofExpr(v_type_5600_);
v___x_5620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5620_, 0, v___x_5618_);
lean_ctor_set(v___x_5620_, 1, v___x_5619_);
v___x_5621_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5612_, v___x_5620_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
if (lean_obj_tag(v___x_5621_) == 0)
{
lean_object* v_a_5622_; lean_object* v___x_5623_; 
v_a_5622_ = lean_ctor_get(v___x_5621_, 0);
lean_inc(v_a_5622_);
lean_dec_ref_known(v___x_5621_, 1);
v___x_5623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5575_, v___f_5604_, v_a_5622_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
v___y_5553_ = v___x_5623_;
goto v___jp_5552_;
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_dec_ref(v___f_5604_);
lean_dec(v_a_5537_);
lean_dec_ref(v_config_5536_);
lean_dec_ref(v_methods_5535_);
v_a_5624_ = lean_ctor_get(v___x_5621_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5621_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5621_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5621_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
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
}
}
}
}
else
{
lean_object* v___x_5636_; 
lean_inc_ref(v_value_5601_);
lean_dec(v_a_5595_);
lean_del_object(v___x_5590_);
lean_dec(v_a_5537_);
lean_dec_ref(v_config_5536_);
lean_dec_ref(v_methods_5535_);
v___x_5636_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5601_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
if (lean_obj_tag(v___x_5636_) == 0)
{
lean_object* v___x_5638_; uint8_t v_isShared_5639_; uint8_t v_isSharedCheck_5648_; 
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5636_);
if (v_isSharedCheck_5648_ == 0)
{
lean_object* v_unused_5649_; 
v_unused_5649_ = lean_ctor_get(v___x_5636_, 0);
lean_dec(v_unused_5649_);
v___x_5638_ = v___x_5636_;
v_isShared_5639_ = v_isSharedCheck_5648_;
goto v_resetjp_5637_;
}
else
{
lean_dec(v___x_5636_);
v___x_5638_ = lean_box(0);
v_isShared_5639_ = v_isSharedCheck_5648_;
goto v_resetjp_5637_;
}
v_resetjp_5637_:
{
lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5643_; 
v___x_5640_ = lean_box(v___x_5602_);
v___x_5641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5640_);
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 0, v___x_5641_);
v___x_5643_ = v___x_5598_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v___x_5641_);
lean_ctor_set(v_reuseFailAlloc_5647_, 1, v_snd_5596_);
v___x_5643_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
lean_object* v___x_5645_; 
if (v_isShared_5639_ == 0)
{
lean_ctor_set(v___x_5638_, 0, v___x_5643_);
v___x_5645_ = v___x_5638_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5643_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
else
{
lean_object* v_a_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5657_; 
lean_del_object(v___x_5598_);
lean_dec(v_snd_5596_);
v_a_5650_ = lean_ctor_get(v___x_5636_, 0);
v_isSharedCheck_5657_ = !lean_is_exclusive(v___x_5636_);
if (v_isSharedCheck_5657_ == 0)
{
v___x_5652_ = v___x_5636_;
v_isShared_5653_ = v_isSharedCheck_5657_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_a_5650_);
lean_dec(v___x_5636_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5657_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___x_5655_; 
if (v_isShared_5653_ == 0)
{
v___x_5655_ = v___x_5652_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_a_5650_);
v___x_5655_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
return v___x_5655_;
}
}
}
}
}
}
else
{
lean_object* v_a_5660_; lean_object* v___x_5662_; uint8_t v_isShared_5663_; uint8_t v_isSharedCheck_5667_; 
lean_del_object(v___x_5590_);
lean_dec_ref(v_b_5538_);
lean_dec(v_a_5537_);
lean_dec_ref(v_config_5536_);
lean_dec_ref(v_methods_5535_);
v_a_5660_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5667_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5667_ == 0)
{
v___x_5662_ = v___x_5594_;
v_isShared_5663_ = v_isSharedCheck_5667_;
goto v_resetjp_5661_;
}
else
{
lean_inc(v_a_5660_);
lean_dec(v___x_5594_);
v___x_5662_ = lean_box(0);
v_isShared_5663_ = v_isSharedCheck_5667_;
goto v_resetjp_5661_;
}
v_resetjp_5661_:
{
lean_object* v___x_5665_; 
if (v_isShared_5663_ == 0)
{
v___x_5665_ = v___x_5662_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_a_5660_);
v___x_5665_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
return v___x_5665_;
}
}
}
}
}
else
{
lean_object* v_a_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5676_; 
lean_dec_ref(v_b_5538_);
lean_dec(v_a_5537_);
lean_dec_ref(v_config_5536_);
lean_dec_ref(v_methods_5535_);
v_a_5669_ = lean_ctor_get(v___x_5585_, 0);
v_isSharedCheck_5676_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5676_ == 0)
{
v___x_5671_ = v___x_5585_;
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_a_5669_);
lean_dec(v___x_5585_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v___x_5674_; 
if (v_isShared_5672_ == 0)
{
v___x_5674_ = v___x_5671_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
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
v___jp_5552_:
{
if (lean_obj_tag(v___y_5553_) == 0)
{
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5566_; 
v_a_5554_ = lean_ctor_get(v___y_5553_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___y_5553_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5556_ = v___y_5553_;
v_isShared_5557_ = v_isSharedCheck_5566_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___y_5553_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5566_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
if (lean_obj_tag(v_a_5554_) == 0)
{
lean_object* v_a_5558_; lean_object* v___x_5560_; 
lean_dec(v_a_5537_);
lean_dec_ref(v_config_5536_);
lean_dec_ref(v_methods_5535_);
v_a_5558_ = lean_ctor_get(v_a_5554_, 0);
lean_inc(v_a_5558_);
lean_dec_ref_known(v_a_5554_, 1);
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 0, v_a_5558_);
v___x_5560_ = v___x_5556_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5558_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
else
{
lean_object* v_a_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; 
lean_del_object(v___x_5556_);
v_a_5562_ = lean_ctor_get(v_a_5554_, 0);
lean_inc(v_a_5562_);
lean_dec_ref_known(v_a_5554_, 1);
v___x_5563_ = lean_unsigned_to_nat(1u);
v___x_5564_ = lean_nat_add(v_a_5537_, v___x_5563_);
lean_dec(v_a_5537_);
v_a_5537_ = v___x_5564_;
v_b_5538_ = v_a_5562_;
goto _start;
}
}
}
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5574_; 
lean_dec(v_a_5537_);
lean_dec_ref(v_config_5536_);
lean_dec_ref(v_methods_5535_);
v_a_5567_ = lean_ctor_get(v___y_5553_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___y_5553_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5569_ = v___y_5553_;
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___y_5553_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5572_; 
if (v_isShared_5570_ == 0)
{
v___x_5572_ = v___x_5569_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5677_ = _args[0];
lean_object* v___x_5678_ = _args[1];
lean_object* v_methods_5679_ = _args[2];
lean_object* v_config_5680_ = _args[3];
lean_object* v_a_5681_ = _args[4];
lean_object* v_b_5682_ = _args[5];
lean_object* v___y_5683_ = _args[6];
lean_object* v___y_5684_ = _args[7];
lean_object* v___y_5685_ = _args[8];
lean_object* v___y_5686_ = _args[9];
lean_object* v___y_5687_ = _args[10];
lean_object* v___y_5688_ = _args[11];
lean_object* v___y_5689_ = _args[12];
lean_object* v___y_5690_ = _args[13];
lean_object* v___y_5691_ = _args[14];
lean_object* v___y_5692_ = _args[15];
lean_object* v___y_5693_ = _args[16];
lean_object* v___y_5694_ = _args[17];
lean_object* v___y_5695_ = _args[18];
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5677_, v___x_5678_, v_methods_5679_, v_config_5680_, v_a_5681_, v_b_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
lean_dec(v___y_5694_);
lean_dec_ref(v___y_5693_);
lean_dec(v___y_5692_);
lean_dec_ref(v___y_5691_);
lean_dec(v___y_5690_);
lean_dec_ref(v___y_5689_);
lean_dec(v___y_5688_);
lean_dec_ref(v___y_5687_);
lean_dec(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___x_5678_);
lean_dec(v_upperBound_5677_);
return v_res_5696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_5697_, lean_object* v_config_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_){
_start:
{
lean_object* v___x_5712_; lean_object* v_hypotheses_5713_; lean_object* v___x_5714_; lean_object* v_newHyps_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; 
v___x_5712_ = lean_st_ref_get(v_a_5701_);
v_hypotheses_5713_ = lean_ctor_get(v___x_5712_, 3);
lean_inc_ref(v_hypotheses_5713_);
lean_dec(v___x_5712_);
v___x_5714_ = lean_array_get_size(v_hypotheses_5713_);
v_newHyps_5715_ = lean_mk_empty_array_with_capacity(v___x_5714_);
v___x_5716_ = lean_unsigned_to_nat(0u);
v___x_5717_ = lean_box(0);
v___x_5718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5717_);
lean_ctor_set(v___x_5718_, 1, v_newHyps_5715_);
v___x_5719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_5714_, v_hypotheses_5713_, v_methods_5697_, v_config_5698_, v___x_5716_, v___x_5718_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_);
lean_dec_ref(v_hypotheses_5713_);
if (lean_obj_tag(v___x_5719_) == 0)
{
lean_object* v_a_5720_; lean_object* v___x_5722_; uint8_t v_isShared_5723_; uint8_t v_isSharedCheck_5749_; 
v_a_5720_ = lean_ctor_get(v___x_5719_, 0);
v_isSharedCheck_5749_ = !lean_is_exclusive(v___x_5719_);
if (v_isSharedCheck_5749_ == 0)
{
v___x_5722_ = v___x_5719_;
v_isShared_5723_ = v_isSharedCheck_5749_;
goto v_resetjp_5721_;
}
else
{
lean_inc(v_a_5720_);
lean_dec(v___x_5719_);
v___x_5722_ = lean_box(0);
v_isShared_5723_ = v_isSharedCheck_5749_;
goto v_resetjp_5721_;
}
v_resetjp_5721_:
{
lean_object* v_fst_5724_; 
v_fst_5724_ = lean_ctor_get(v_a_5720_, 0);
if (lean_obj_tag(v_fst_5724_) == 0)
{
lean_object* v_snd_5725_; lean_object* v___x_5726_; lean_object* v_caches_5727_; lean_object* v_typeAnalysis_5728_; lean_object* v_target_5729_; uint8_t v_didChange_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5743_; 
v_snd_5725_ = lean_ctor_get(v_a_5720_, 1);
lean_inc(v_snd_5725_);
lean_dec(v_a_5720_);
v___x_5726_ = lean_st_ref_take(v_a_5701_);
v_caches_5727_ = lean_ctor_get(v___x_5726_, 0);
v_typeAnalysis_5728_ = lean_ctor_get(v___x_5726_, 1);
v_target_5729_ = lean_ctor_get(v___x_5726_, 2);
v_didChange_5730_ = lean_ctor_get_uint8(v___x_5726_, sizeof(void*)*4);
v_isSharedCheck_5743_ = !lean_is_exclusive(v___x_5726_);
if (v_isSharedCheck_5743_ == 0)
{
lean_object* v_unused_5744_; 
v_unused_5744_ = lean_ctor_get(v___x_5726_, 3);
lean_dec(v_unused_5744_);
v___x_5732_ = v___x_5726_;
v_isShared_5733_ = v_isSharedCheck_5743_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_target_5729_);
lean_inc(v_typeAnalysis_5728_);
lean_inc(v_caches_5727_);
lean_dec(v___x_5726_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5743_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5735_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 3, v_snd_5725_);
v___x_5735_ = v___x_5732_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_caches_5727_);
lean_ctor_set(v_reuseFailAlloc_5742_, 1, v_typeAnalysis_5728_);
lean_ctor_set(v_reuseFailAlloc_5742_, 2, v_target_5729_);
lean_ctor_set(v_reuseFailAlloc_5742_, 3, v_snd_5725_);
lean_ctor_set_uint8(v_reuseFailAlloc_5742_, sizeof(void*)*4, v_didChange_5730_);
v___x_5735_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
lean_object* v___x_5736_; uint8_t v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5740_; 
v___x_5736_ = lean_st_ref_put(v_a_5701_, v___x_5735_);
v___x_5737_ = 0;
v___x_5738_ = lean_box(v___x_5737_);
if (v_isShared_5723_ == 0)
{
lean_ctor_set(v___x_5722_, 0, v___x_5738_);
v___x_5740_ = v___x_5722_;
goto v_reusejp_5739_;
}
else
{
lean_object* v_reuseFailAlloc_5741_; 
v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5738_);
v___x_5740_ = v_reuseFailAlloc_5741_;
goto v_reusejp_5739_;
}
v_reusejp_5739_:
{
return v___x_5740_;
}
}
}
}
else
{
lean_object* v_val_5745_; lean_object* v___x_5747_; 
lean_inc_ref(v_fst_5724_);
lean_dec(v_a_5720_);
v_val_5745_ = lean_ctor_get(v_fst_5724_, 0);
lean_inc(v_val_5745_);
lean_dec_ref_known(v_fst_5724_, 1);
if (v_isShared_5723_ == 0)
{
lean_ctor_set(v___x_5722_, 0, v_val_5745_);
v___x_5747_ = v___x_5722_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5748_; 
v_reuseFailAlloc_5748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5748_, 0, v_val_5745_);
v___x_5747_ = v_reuseFailAlloc_5748_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
return v___x_5747_;
}
}
}
}
else
{
lean_object* v_a_5750_; lean_object* v___x_5752_; uint8_t v_isShared_5753_; uint8_t v_isSharedCheck_5757_; 
v_a_5750_ = lean_ctor_get(v___x_5719_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___x_5719_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5752_ = v___x_5719_;
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
else
{
lean_inc(v_a_5750_);
lean_dec(v___x_5719_);
v___x_5752_ = lean_box(0);
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
v_resetjp_5751_:
{
lean_object* v___x_5755_; 
if (v_isShared_5753_ == 0)
{
v___x_5755_ = v___x_5752_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_a_5750_);
v___x_5755_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
return v___x_5755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_5758_, lean_object* v_config_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_){
_start:
{
lean_object* v_res_5773_; 
v_res_5773_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5758_, v_config_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_);
lean_dec(v_a_5771_);
lean_dec_ref(v_a_5770_);
lean_dec(v_a_5769_);
lean_dec_ref(v_a_5768_);
lean_dec(v_a_5767_);
lean_dec_ref(v_a_5766_);
lean_dec(v_a_5765_);
lean_dec_ref(v_a_5764_);
lean_dec(v_a_5763_);
lean_dec(v_a_5762_);
lean_dec_ref(v_a_5761_);
lean_dec(v_a_5760_);
return v_res_5773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_5774_, lean_object* v_msg_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_){
_start:
{
lean_object* v___x_5789_; 
v___x_5789_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5774_, v_msg_5775_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_);
return v___x_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_5790_, lean_object* v_msg_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5790_, v_msg_5791_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
lean_dec(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___y_5801_);
lean_dec_ref(v___y_5800_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
lean_dec(v___y_5795_);
lean_dec(v___y_5794_);
lean_dec_ref(v___y_5793_);
lean_dec(v___y_5792_);
return v_res_5805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_upperBound_5806_, lean_object* v___x_5807_, lean_object* v_methods_5808_, lean_object* v_config_5809_, lean_object* v_inst_5810_, lean_object* v_R_5811_, lean_object* v_a_5812_, lean_object* v_b_5813_, lean_object* v_c_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
lean_object* v___x_5828_; 
v___x_5828_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5806_, v___x_5807_, v_methods_5808_, v_config_5809_, v_a_5812_, v_b_5813_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_);
return v___x_5828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5829_ = _args[0];
lean_object* v___x_5830_ = _args[1];
lean_object* v_methods_5831_ = _args[2];
lean_object* v_config_5832_ = _args[3];
lean_object* v_inst_5833_ = _args[4];
lean_object* v_R_5834_ = _args[5];
lean_object* v_a_5835_ = _args[6];
lean_object* v_b_5836_ = _args[7];
lean_object* v_c_5837_ = _args[8];
lean_object* v___y_5838_ = _args[9];
lean_object* v___y_5839_ = _args[10];
lean_object* v___y_5840_ = _args[11];
lean_object* v___y_5841_ = _args[12];
lean_object* v___y_5842_ = _args[13];
lean_object* v___y_5843_ = _args[14];
lean_object* v___y_5844_ = _args[15];
lean_object* v___y_5845_ = _args[16];
lean_object* v___y_5846_ = _args[17];
lean_object* v___y_5847_ = _args[18];
lean_object* v___y_5848_ = _args[19];
lean_object* v___y_5849_ = _args[20];
lean_object* v___y_5850_ = _args[21];
_start:
{
lean_object* v_res_5851_; 
v_res_5851_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5829_, v___x_5830_, v_methods_5831_, v_config_5832_, v_inst_5833_, v_R_5834_, v_a_5835_, v_b_5836_, v_c_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
lean_dec(v___y_5845_);
lean_dec_ref(v___y_5844_);
lean_dec(v___y_5843_);
lean_dec_ref(v___y_5842_);
lean_dec(v___y_5841_);
lean_dec(v___y_5840_);
lean_dec_ref(v___y_5839_);
lean_dec(v___y_5838_);
lean_dec_ref(v___x_5830_);
lean_dec(v_upperBound_5829_);
return v_res_5851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_5852_, lean_object* v_config_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_, lean_object* v_a_5863_, lean_object* v_a_5864_){
_start:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5866_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_5867_ = lean_st_mk_ref(v___x_5866_);
v___x_5868_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5852_, v_config_5853_, v___x_5867_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_, v_a_5864_);
if (lean_obj_tag(v___x_5868_) == 0)
{
lean_object* v_a_5869_; lean_object* v___x_5871_; uint8_t v_isShared_5872_; uint8_t v_isSharedCheck_5877_; 
v_a_5869_ = lean_ctor_get(v___x_5868_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5868_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5871_ = v___x_5868_;
v_isShared_5872_ = v_isSharedCheck_5877_;
goto v_resetjp_5870_;
}
else
{
lean_inc(v_a_5869_);
lean_dec(v___x_5868_);
v___x_5871_ = lean_box(0);
v_isShared_5872_ = v_isSharedCheck_5877_;
goto v_resetjp_5870_;
}
v_resetjp_5870_:
{
lean_object* v___x_5873_; lean_object* v___x_5875_; 
v___x_5873_ = lean_st_ref_get(v___x_5867_);
lean_dec(v___x_5867_);
lean_dec(v___x_5873_);
if (v_isShared_5872_ == 0)
{
v___x_5875_ = v___x_5871_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5869_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
}
}
else
{
lean_dec(v___x_5867_);
return v___x_5868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_5878_, lean_object* v_config_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_){
_start:
{
lean_object* v_res_5892_; 
v_res_5892_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5878_, v_config_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_);
lean_dec(v_a_5890_);
lean_dec_ref(v_a_5889_);
lean_dec(v_a_5888_);
lean_dec_ref(v_a_5887_);
lean_dec(v_a_5886_);
lean_dec_ref(v_a_5885_);
lean_dec(v_a_5884_);
lean_dec_ref(v_a_5883_);
lean_dec(v_a_5882_);
lean_dec(v_a_5881_);
lean_dec_ref(v_a_5880_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_5893_, lean_object* v_msg_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_){
_start:
{
lean_object* v_ref_5900_; lean_object* v___x_5901_; lean_object* v_a_5902_; lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_5946_; 
v_ref_5900_ = lean_ctor_get(v___y_5897_, 5);
v___x_5901_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
v_a_5902_ = lean_ctor_get(v___x_5901_, 0);
v_isSharedCheck_5946_ = !lean_is_exclusive(v___x_5901_);
if (v_isSharedCheck_5946_ == 0)
{
v___x_5904_ = v___x_5901_;
v_isShared_5905_ = v_isSharedCheck_5946_;
goto v_resetjp_5903_;
}
else
{
lean_inc(v_a_5902_);
lean_dec(v___x_5901_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_5946_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v___x_5906_; lean_object* v_traceState_5907_; lean_object* v_env_5908_; lean_object* v_nextMacroScope_5909_; lean_object* v_ngen_5910_; lean_object* v_auxDeclNGen_5911_; lean_object* v_cache_5912_; lean_object* v_messages_5913_; lean_object* v_infoState_5914_; lean_object* v_snapshotTasks_5915_; lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5945_; 
v___x_5906_ = lean_st_ref_take(v___y_5898_);
v_traceState_5907_ = lean_ctor_get(v___x_5906_, 4);
v_env_5908_ = lean_ctor_get(v___x_5906_, 0);
v_nextMacroScope_5909_ = lean_ctor_get(v___x_5906_, 1);
v_ngen_5910_ = lean_ctor_get(v___x_5906_, 2);
v_auxDeclNGen_5911_ = lean_ctor_get(v___x_5906_, 3);
v_cache_5912_ = lean_ctor_get(v___x_5906_, 5);
v_messages_5913_ = lean_ctor_get(v___x_5906_, 6);
v_infoState_5914_ = lean_ctor_get(v___x_5906_, 7);
v_snapshotTasks_5915_ = lean_ctor_get(v___x_5906_, 8);
v_isSharedCheck_5945_ = !lean_is_exclusive(v___x_5906_);
if (v_isSharedCheck_5945_ == 0)
{
v___x_5917_ = v___x_5906_;
v_isShared_5918_ = v_isSharedCheck_5945_;
goto v_resetjp_5916_;
}
else
{
lean_inc(v_snapshotTasks_5915_);
lean_inc(v_infoState_5914_);
lean_inc(v_messages_5913_);
lean_inc(v_cache_5912_);
lean_inc(v_traceState_5907_);
lean_inc(v_auxDeclNGen_5911_);
lean_inc(v_ngen_5910_);
lean_inc(v_nextMacroScope_5909_);
lean_inc(v_env_5908_);
lean_dec(v___x_5906_);
v___x_5917_ = lean_box(0);
v_isShared_5918_ = v_isSharedCheck_5945_;
goto v_resetjp_5916_;
}
v_resetjp_5916_:
{
uint64_t v_tid_5919_; lean_object* v_traces_5920_; lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5944_; 
v_tid_5919_ = lean_ctor_get_uint64(v_traceState_5907_, sizeof(void*)*1);
v_traces_5920_ = lean_ctor_get(v_traceState_5907_, 0);
v_isSharedCheck_5944_ = !lean_is_exclusive(v_traceState_5907_);
if (v_isSharedCheck_5944_ == 0)
{
v___x_5922_ = v_traceState_5907_;
v_isShared_5923_ = v_isSharedCheck_5944_;
goto v_resetjp_5921_;
}
else
{
lean_inc(v_traces_5920_);
lean_dec(v_traceState_5907_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5944_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___x_5924_; double v___x_5925_; uint8_t v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5934_; 
v___x_5924_ = lean_box(0);
v___x_5925_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5926_ = 0;
v___x_5927_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5928_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5928_, 0, v_cls_5893_);
lean_ctor_set(v___x_5928_, 1, v___x_5924_);
lean_ctor_set(v___x_5928_, 2, v___x_5927_);
lean_ctor_set_float(v___x_5928_, sizeof(void*)*3, v___x_5925_);
lean_ctor_set_float(v___x_5928_, sizeof(void*)*3 + 8, v___x_5925_);
lean_ctor_set_uint8(v___x_5928_, sizeof(void*)*3 + 16, v___x_5926_);
v___x_5929_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5930_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5928_);
lean_ctor_set(v___x_5930_, 1, v_a_5902_);
lean_ctor_set(v___x_5930_, 2, v___x_5929_);
lean_inc(v_ref_5900_);
v___x_5931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5931_, 0, v_ref_5900_);
lean_ctor_set(v___x_5931_, 1, v___x_5930_);
v___x_5932_ = l_Lean_PersistentArray_push___redArg(v_traces_5920_, v___x_5931_);
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 0, v___x_5932_);
v___x_5934_ = v___x_5922_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_5943_; 
v_reuseFailAlloc_5943_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5943_, 0, v___x_5932_);
lean_ctor_set_uint64(v_reuseFailAlloc_5943_, sizeof(void*)*1, v_tid_5919_);
v___x_5934_ = v_reuseFailAlloc_5943_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
lean_object* v___x_5936_; 
if (v_isShared_5918_ == 0)
{
lean_ctor_set(v___x_5917_, 4, v___x_5934_);
v___x_5936_ = v___x_5917_;
goto v_reusejp_5935_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_env_5908_);
lean_ctor_set(v_reuseFailAlloc_5942_, 1, v_nextMacroScope_5909_);
lean_ctor_set(v_reuseFailAlloc_5942_, 2, v_ngen_5910_);
lean_ctor_set(v_reuseFailAlloc_5942_, 3, v_auxDeclNGen_5911_);
lean_ctor_set(v_reuseFailAlloc_5942_, 4, v___x_5934_);
lean_ctor_set(v_reuseFailAlloc_5942_, 5, v_cache_5912_);
lean_ctor_set(v_reuseFailAlloc_5942_, 6, v_messages_5913_);
lean_ctor_set(v_reuseFailAlloc_5942_, 7, v_infoState_5914_);
lean_ctor_set(v_reuseFailAlloc_5942_, 8, v_snapshotTasks_5915_);
v___x_5936_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5935_;
}
v_reusejp_5935_:
{
lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5940_; 
v___x_5937_ = lean_st_ref_put(v___y_5898_, v___x_5936_);
v___x_5938_ = lean_box(0);
if (v_isShared_5905_ == 0)
{
lean_ctor_set(v___x_5904_, 0, v___x_5938_);
v___x_5940_ = v___x_5904_;
goto v_reusejp_5939_;
}
else
{
lean_object* v_reuseFailAlloc_5941_; 
v_reuseFailAlloc_5941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5941_, 0, v___x_5938_);
v___x_5940_ = v_reuseFailAlloc_5941_;
goto v_reusejp_5939_;
}
v_reusejp_5939_:
{
return v___x_5940_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5947_, lean_object* v_msg_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_){
_start:
{
lean_object* v_res_5954_; 
v_res_5954_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5947_, v_msg_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
lean_dec(v___y_5952_);
lean_dec_ref(v___y_5951_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
return v_res_5954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5955_, lean_object* v___x_5956_, lean_object* v_methods_5957_, lean_object* v_config_5958_, lean_object* v_a_5959_, lean_object* v_b_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_){
_start:
{
lean_object* v___y_5975_; uint8_t v___x_5997_; 
v___x_5997_ = lean_nat_dec_lt(v_a_5959_, v_upperBound_5955_);
if (v___x_5997_ == 0)
{
lean_object* v___x_5998_; 
lean_dec(v_a_5959_);
lean_dec_ref(v_config_5958_);
lean_dec_ref(v_methods_5957_);
v___x_5998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5998_, 0, v_b_5960_);
return v___x_5998_;
}
else
{
lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v_type_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_5999_ = lean_st_ref_take(v___y_5961_);
v___x_6000_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_6001_ = lean_st_ref_put(v___y_5961_, v___x_6000_);
v___x_6002_ = lean_array_fget_borrowed(v___x_5956_, v_a_5959_);
v_type_6003_ = lean_ctor_get(v___x_6002_, 1);
v___x_6004_ = lean_unsigned_to_nat(0u);
v___x_6005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
lean_ctor_set(v___x_6005_, 1, v___x_5999_);
lean_inc_ref(v_type_6003_);
v___x_6006_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_6006_, 0, v_type_6003_);
lean_inc_ref(v_config_5958_);
lean_inc_ref(v_methods_5957_);
v___x_6007_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_6006_, v_methods_5957_, v_config_5958_, v___x_6005_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
if (lean_obj_tag(v___x_6007_) == 0)
{
lean_object* v_a_6008_; lean_object* v_snd_6009_; lean_object* v_fst_6010_; lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6097_; 
v_a_6008_ = lean_ctor_get(v___x_6007_, 0);
lean_inc(v_a_6008_);
lean_dec_ref_known(v___x_6007_, 1);
v_snd_6009_ = lean_ctor_get(v_a_6008_, 1);
v_fst_6010_ = lean_ctor_get(v_a_6008_, 0);
v_isSharedCheck_6097_ = !lean_is_exclusive(v_a_6008_);
if (v_isSharedCheck_6097_ == 0)
{
v___x_6012_ = v_a_6008_;
v_isShared_6013_ = v_isSharedCheck_6097_;
goto v_resetjp_6011_;
}
else
{
lean_inc(v_snd_6009_);
lean_inc(v_fst_6010_);
lean_dec(v_a_6008_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6097_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v_cache_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6095_; 
v_cache_6014_ = lean_ctor_get(v_snd_6009_, 1);
v_isSharedCheck_6095_ = !lean_is_exclusive(v_snd_6009_);
if (v_isSharedCheck_6095_ == 0)
{
lean_object* v_unused_6096_; 
v_unused_6096_ = lean_ctor_get(v_snd_6009_, 0);
lean_dec(v_unused_6096_);
v___x_6016_ = v_snd_6009_;
v_isShared_6017_ = v_isSharedCheck_6095_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_cache_6014_);
lean_dec(v_snd_6009_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6095_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; 
v___x_6018_ = lean_st_ref_swap(v___y_5961_, v_cache_6014_);
lean_dec(v___x_6018_);
lean_inc(v___x_6002_);
v___x_6019_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_6002_, v_fst_6010_);
lean_dec(v_fst_6010_);
if (lean_obj_tag(v___x_6019_) == 0)
{
lean_object* v_a_6020_; lean_object* v_snd_6021_; lean_object* v___x_6023_; uint8_t v_isShared_6024_; uint8_t v_isSharedCheck_6085_; 
v_a_6020_ = lean_ctor_get(v___x_6019_, 0);
lean_inc(v_a_6020_);
lean_dec_ref_known(v___x_6019_, 1);
v_snd_6021_ = lean_ctor_get(v_b_5960_, 1);
v_isSharedCheck_6085_ = !lean_is_exclusive(v_b_5960_);
if (v_isSharedCheck_6085_ == 0)
{
lean_object* v_unused_6086_; 
v_unused_6086_ = lean_ctor_get(v_b_5960_, 0);
lean_dec(v_unused_6086_);
v___x_6023_ = v_b_5960_;
v_isShared_6024_ = v_isSharedCheck_6085_;
goto v_resetjp_6022_;
}
else
{
lean_inc(v_snd_6021_);
lean_dec(v_b_5960_);
v___x_6023_ = lean_box(0);
v_isShared_6024_ = v_isSharedCheck_6085_;
goto v_resetjp_6022_;
}
v_resetjp_6022_:
{
lean_object* v_type_6025_; lean_object* v_value_6026_; uint8_t v___x_6027_; 
v_type_6025_ = lean_ctor_get(v_a_6020_, 1);
v_value_6026_ = lean_ctor_get(v_a_6020_, 2);
lean_inc_ref(v_type_6025_);
v___x_6027_ = l_Lean_Expr_isFalse(v_type_6025_);
if (v___x_6027_ == 0)
{
lean_object* v___x_6028_; lean_object* v___f_6029_; uint8_t v___x_6060_; 
lean_del_object(v___x_6023_);
v___x_6028_ = lean_box(0);
lean_inc(v_a_6020_);
lean_inc(v_snd_6021_);
v___f_6029_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_6029_, 0, v_snd_6021_);
lean_closure_set(v___f_6029_, 1, v_a_6020_);
lean_closure_set(v___f_6029_, 2, v___x_6028_);
v___x_6060_ = lean_expr_eqv(v_type_6003_, v_type_6025_);
if (v___x_6060_ == 0)
{
lean_inc_ref(v_type_6025_);
lean_dec(v_snd_6021_);
lean_dec(v_a_6020_);
goto v___jp_6033_;
}
else
{
if (v___x_6027_ == 0)
{
lean_object* v___x_6061_; lean_object* v___x_6062_; 
lean_dec_ref(v___f_6029_);
lean_del_object(v___x_6016_);
lean_del_object(v___x_6012_);
v___x_6061_ = lean_box(0);
v___x_6062_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_6021_, v_a_6020_, v___x_6028_, v___x_6061_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
v___y_5975_ = v___x_6062_;
goto v___jp_5974_;
}
else
{
lean_inc_ref(v_type_6025_);
lean_dec(v_snd_6021_);
lean_dec(v_a_6020_);
goto v___jp_6033_;
}
}
v___jp_6030_:
{
lean_object* v___x_6031_; lean_object* v___x_6032_; 
v___x_6031_ = lean_box(0);
v___x_6032_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5997_, v___f_6029_, v___x_6031_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
v___y_5975_ = v___x_6032_;
goto v___jp_5974_;
}
v___jp_6033_:
{
lean_object* v_options_6034_; uint8_t v_hasTrace_6035_; 
v_options_6034_ = lean_ctor_get(v___y_5971_, 2);
v_hasTrace_6035_ = lean_ctor_get_uint8(v_options_6034_, sizeof(void*)*1);
if (v_hasTrace_6035_ == 0)
{
lean_dec_ref(v_type_6025_);
lean_del_object(v___x_6016_);
lean_del_object(v___x_6012_);
goto v___jp_6030_;
}
else
{
lean_object* v_inheritedTraceOptions_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; uint8_t v___x_6039_; 
v_inheritedTraceOptions_6036_ = lean_ctor_get(v___y_5971_, 13);
v___x_6037_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_6038_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_6039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6036_, v_options_6034_, v___x_6038_);
if (v___x_6039_ == 0)
{
lean_dec_ref(v_type_6025_);
lean_del_object(v___x_6016_);
lean_del_object(v___x_6012_);
goto v___jp_6030_;
}
else
{
lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6043_; 
lean_inc_ref(v_type_6003_);
v___x_6040_ = l_Lean_MessageData_ofExpr(v_type_6003_);
v___x_6041_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_6017_ == 0)
{
lean_ctor_set_tag(v___x_6016_, 7);
lean_ctor_set(v___x_6016_, 1, v___x_6041_);
lean_ctor_set(v___x_6016_, 0, v___x_6040_);
v___x_6043_ = v___x_6016_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6059_; 
v_reuseFailAlloc_6059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6059_, 0, v___x_6040_);
lean_ctor_set(v_reuseFailAlloc_6059_, 1, v___x_6041_);
v___x_6043_ = v_reuseFailAlloc_6059_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
lean_object* v___x_6044_; lean_object* v___x_6046_; 
v___x_6044_ = l_Lean_MessageData_ofExpr(v_type_6025_);
if (v_isShared_6013_ == 0)
{
lean_ctor_set_tag(v___x_6012_, 7);
lean_ctor_set(v___x_6012_, 1, v___x_6044_);
lean_ctor_set(v___x_6012_, 0, v___x_6043_);
v___x_6046_ = v___x_6012_;
goto v_reusejp_6045_;
}
else
{
lean_object* v_reuseFailAlloc_6058_; 
v_reuseFailAlloc_6058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6058_, 0, v___x_6043_);
lean_ctor_set(v_reuseFailAlloc_6058_, 1, v___x_6044_);
v___x_6046_ = v_reuseFailAlloc_6058_;
goto v_reusejp_6045_;
}
v_reusejp_6045_:
{
lean_object* v___x_6047_; 
v___x_6047_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_6037_, v___x_6046_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
if (lean_obj_tag(v___x_6047_) == 0)
{
lean_object* v_a_6048_; lean_object* v___x_6049_; 
v_a_6048_ = lean_ctor_get(v___x_6047_, 0);
lean_inc(v_a_6048_);
lean_dec_ref_known(v___x_6047_, 1);
v___x_6049_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5997_, v___f_6029_, v_a_6048_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
v___y_5975_ = v___x_6049_;
goto v___jp_5974_;
}
else
{
lean_object* v_a_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6057_; 
lean_dec_ref(v___f_6029_);
lean_dec(v_a_5959_);
lean_dec_ref(v_config_5958_);
lean_dec_ref(v_methods_5957_);
v_a_6050_ = lean_ctor_get(v___x_6047_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_6047_);
if (v_isSharedCheck_6057_ == 0)
{
v___x_6052_ = v___x_6047_;
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_a_6050_);
lean_dec(v___x_6047_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6055_; 
if (v_isShared_6053_ == 0)
{
v___x_6055_ = v___x_6052_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
v___x_6055_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
return v___x_6055_;
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
lean_object* v___x_6063_; 
lean_inc_ref(v_value_6026_);
lean_dec(v_a_6020_);
lean_del_object(v___x_6016_);
lean_del_object(v___x_6012_);
lean_dec(v_a_5959_);
lean_dec_ref(v_config_5958_);
lean_dec_ref(v_methods_5957_);
v___x_6063_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_6026_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
if (lean_obj_tag(v___x_6063_) == 0)
{
lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6075_; 
v_isSharedCheck_6075_ = !lean_is_exclusive(v___x_6063_);
if (v_isSharedCheck_6075_ == 0)
{
lean_object* v_unused_6076_; 
v_unused_6076_ = lean_ctor_get(v___x_6063_, 0);
lean_dec(v_unused_6076_);
v___x_6065_ = v___x_6063_;
v_isShared_6066_ = v_isSharedCheck_6075_;
goto v_resetjp_6064_;
}
else
{
lean_dec(v___x_6063_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6075_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6070_; 
v___x_6067_ = lean_box(v___x_6027_);
v___x_6068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6067_);
if (v_isShared_6024_ == 0)
{
lean_ctor_set(v___x_6023_, 0, v___x_6068_);
v___x_6070_ = v___x_6023_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v___x_6068_);
lean_ctor_set(v_reuseFailAlloc_6074_, 1, v_snd_6021_);
v___x_6070_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
lean_object* v___x_6072_; 
if (v_isShared_6066_ == 0)
{
lean_ctor_set(v___x_6065_, 0, v___x_6070_);
v___x_6072_ = v___x_6065_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6073_; 
v_reuseFailAlloc_6073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6073_, 0, v___x_6070_);
v___x_6072_ = v_reuseFailAlloc_6073_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
return v___x_6072_;
}
}
}
}
else
{
lean_object* v_a_6077_; lean_object* v___x_6079_; uint8_t v_isShared_6080_; uint8_t v_isSharedCheck_6084_; 
lean_del_object(v___x_6023_);
lean_dec(v_snd_6021_);
v_a_6077_ = lean_ctor_get(v___x_6063_, 0);
v_isSharedCheck_6084_ = !lean_is_exclusive(v___x_6063_);
if (v_isSharedCheck_6084_ == 0)
{
v___x_6079_ = v___x_6063_;
v_isShared_6080_ = v_isSharedCheck_6084_;
goto v_resetjp_6078_;
}
else
{
lean_inc(v_a_6077_);
lean_dec(v___x_6063_);
v___x_6079_ = lean_box(0);
v_isShared_6080_ = v_isSharedCheck_6084_;
goto v_resetjp_6078_;
}
v_resetjp_6078_:
{
lean_object* v___x_6082_; 
if (v_isShared_6080_ == 0)
{
v___x_6082_ = v___x_6079_;
goto v_reusejp_6081_;
}
else
{
lean_object* v_reuseFailAlloc_6083_; 
v_reuseFailAlloc_6083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6083_, 0, v_a_6077_);
v___x_6082_ = v_reuseFailAlloc_6083_;
goto v_reusejp_6081_;
}
v_reusejp_6081_:
{
return v___x_6082_;
}
}
}
}
}
}
else
{
lean_object* v_a_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6094_; 
lean_del_object(v___x_6016_);
lean_del_object(v___x_6012_);
lean_dec_ref(v_b_5960_);
lean_dec(v_a_5959_);
lean_dec_ref(v_config_5958_);
lean_dec_ref(v_methods_5957_);
v_a_6087_ = lean_ctor_get(v___x_6019_, 0);
v_isSharedCheck_6094_ = !lean_is_exclusive(v___x_6019_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6089_ = v___x_6019_;
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_a_6087_);
lean_dec(v___x_6019_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
lean_object* v___x_6092_; 
if (v_isShared_6090_ == 0)
{
v___x_6092_ = v___x_6089_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v_a_6087_);
v___x_6092_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
return v___x_6092_;
}
}
}
}
}
}
else
{
lean_object* v_a_6098_; lean_object* v___x_6100_; uint8_t v_isShared_6101_; uint8_t v_isSharedCheck_6105_; 
lean_dec_ref(v_b_5960_);
lean_dec(v_a_5959_);
lean_dec_ref(v_config_5958_);
lean_dec_ref(v_methods_5957_);
v_a_6098_ = lean_ctor_get(v___x_6007_, 0);
v_isSharedCheck_6105_ = !lean_is_exclusive(v___x_6007_);
if (v_isSharedCheck_6105_ == 0)
{
v___x_6100_ = v___x_6007_;
v_isShared_6101_ = v_isSharedCheck_6105_;
goto v_resetjp_6099_;
}
else
{
lean_inc(v_a_6098_);
lean_dec(v___x_6007_);
v___x_6100_ = lean_box(0);
v_isShared_6101_ = v_isSharedCheck_6105_;
goto v_resetjp_6099_;
}
v_resetjp_6099_:
{
lean_object* v___x_6103_; 
if (v_isShared_6101_ == 0)
{
v___x_6103_ = v___x_6100_;
goto v_reusejp_6102_;
}
else
{
lean_object* v_reuseFailAlloc_6104_; 
v_reuseFailAlloc_6104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6104_, 0, v_a_6098_);
v___x_6103_ = v_reuseFailAlloc_6104_;
goto v_reusejp_6102_;
}
v_reusejp_6102_:
{
return v___x_6103_;
}
}
}
}
v___jp_5974_:
{
if (lean_obj_tag(v___y_5975_) == 0)
{
lean_object* v_a_5976_; lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_5988_; 
v_a_5976_ = lean_ctor_get(v___y_5975_, 0);
v_isSharedCheck_5988_ = !lean_is_exclusive(v___y_5975_);
if (v_isSharedCheck_5988_ == 0)
{
v___x_5978_ = v___y_5975_;
v_isShared_5979_ = v_isSharedCheck_5988_;
goto v_resetjp_5977_;
}
else
{
lean_inc(v_a_5976_);
lean_dec(v___y_5975_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_5988_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
if (lean_obj_tag(v_a_5976_) == 0)
{
lean_object* v_a_5980_; lean_object* v___x_5982_; 
lean_dec(v_a_5959_);
lean_dec_ref(v_config_5958_);
lean_dec_ref(v_methods_5957_);
v_a_5980_ = lean_ctor_get(v_a_5976_, 0);
lean_inc(v_a_5980_);
lean_dec_ref_known(v_a_5976_, 1);
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 0, v_a_5980_);
v___x_5982_ = v___x_5978_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v_a_5980_);
v___x_5982_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
return v___x_5982_;
}
}
else
{
lean_object* v_a_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; 
lean_del_object(v___x_5978_);
v_a_5984_ = lean_ctor_get(v_a_5976_, 0);
lean_inc(v_a_5984_);
lean_dec_ref_known(v_a_5976_, 1);
v___x_5985_ = lean_unsigned_to_nat(1u);
v___x_5986_ = lean_nat_add(v_a_5959_, v___x_5985_);
lean_dec(v_a_5959_);
v_a_5959_ = v___x_5986_;
v_b_5960_ = v_a_5984_;
goto _start;
}
}
}
else
{
lean_object* v_a_5989_; lean_object* v___x_5991_; uint8_t v_isShared_5992_; uint8_t v_isSharedCheck_5996_; 
lean_dec(v_a_5959_);
lean_dec_ref(v_config_5958_);
lean_dec_ref(v_methods_5957_);
v_a_5989_ = lean_ctor_get(v___y_5975_, 0);
v_isSharedCheck_5996_ = !lean_is_exclusive(v___y_5975_);
if (v_isSharedCheck_5996_ == 0)
{
v___x_5991_ = v___y_5975_;
v_isShared_5992_ = v_isSharedCheck_5996_;
goto v_resetjp_5990_;
}
else
{
lean_inc(v_a_5989_);
lean_dec(v___y_5975_);
v___x_5991_ = lean_box(0);
v_isShared_5992_ = v_isSharedCheck_5996_;
goto v_resetjp_5990_;
}
v_resetjp_5990_:
{
lean_object* v___x_5994_; 
if (v_isShared_5992_ == 0)
{
v___x_5994_ = v___x_5991_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v_a_5989_);
v___x_5994_ = v_reuseFailAlloc_5995_;
goto v_reusejp_5993_;
}
v_reusejp_5993_:
{
return v___x_5994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_6106_ = _args[0];
lean_object* v___x_6107_ = _args[1];
lean_object* v_methods_6108_ = _args[2];
lean_object* v_config_6109_ = _args[3];
lean_object* v_a_6110_ = _args[4];
lean_object* v_b_6111_ = _args[5];
lean_object* v___y_6112_ = _args[6];
lean_object* v___y_6113_ = _args[7];
lean_object* v___y_6114_ = _args[8];
lean_object* v___y_6115_ = _args[9];
lean_object* v___y_6116_ = _args[10];
lean_object* v___y_6117_ = _args[11];
lean_object* v___y_6118_ = _args[12];
lean_object* v___y_6119_ = _args[13];
lean_object* v___y_6120_ = _args[14];
lean_object* v___y_6121_ = _args[15];
lean_object* v___y_6122_ = _args[16];
lean_object* v___y_6123_ = _args[17];
lean_object* v___y_6124_ = _args[18];
_start:
{
lean_object* v_res_6125_; 
v_res_6125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_6106_, v___x_6107_, v_methods_6108_, v_config_6109_, v_a_6110_, v_b_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
lean_dec(v___y_6121_);
lean_dec_ref(v___y_6120_);
lean_dec(v___y_6119_);
lean_dec_ref(v___y_6118_);
lean_dec(v___y_6117_);
lean_dec_ref(v___y_6116_);
lean_dec(v___y_6115_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___x_6107_);
lean_dec(v_upperBound_6106_);
return v_res_6125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_6126_, lean_object* v_config_6127_, lean_object* v_a_6128_, lean_object* v_a_6129_, lean_object* v_a_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_, lean_object* v_a_6133_, lean_object* v_a_6134_, lean_object* v_a_6135_, lean_object* v_a_6136_, lean_object* v_a_6137_, lean_object* v_a_6138_, lean_object* v_a_6139_){
_start:
{
lean_object* v___x_6141_; lean_object* v_hypotheses_6142_; lean_object* v___x_6143_; lean_object* v_newHyps_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6141_ = lean_st_ref_get(v_a_6130_);
v_hypotheses_6142_ = lean_ctor_get(v___x_6141_, 3);
lean_inc_ref(v_hypotheses_6142_);
lean_dec(v___x_6141_);
v___x_6143_ = lean_array_get_size(v_hypotheses_6142_);
v_newHyps_6144_ = lean_mk_empty_array_with_capacity(v___x_6143_);
v___x_6145_ = lean_unsigned_to_nat(0u);
v___x_6146_ = lean_box(0);
v___x_6147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
lean_ctor_set(v___x_6147_, 1, v_newHyps_6144_);
v___x_6148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_6143_, v_hypotheses_6142_, v_methods_6126_, v_config_6127_, v___x_6145_, v___x_6147_, v_a_6128_, v_a_6129_, v_a_6130_, v_a_6131_, v_a_6132_, v_a_6133_, v_a_6134_, v_a_6135_, v_a_6136_, v_a_6137_, v_a_6138_, v_a_6139_);
lean_dec_ref(v_hypotheses_6142_);
if (lean_obj_tag(v___x_6148_) == 0)
{
lean_object* v_a_6149_; lean_object* v___x_6151_; uint8_t v_isShared_6152_; uint8_t v_isSharedCheck_6178_; 
v_a_6149_ = lean_ctor_get(v___x_6148_, 0);
v_isSharedCheck_6178_ = !lean_is_exclusive(v___x_6148_);
if (v_isSharedCheck_6178_ == 0)
{
v___x_6151_ = v___x_6148_;
v_isShared_6152_ = v_isSharedCheck_6178_;
goto v_resetjp_6150_;
}
else
{
lean_inc(v_a_6149_);
lean_dec(v___x_6148_);
v___x_6151_ = lean_box(0);
v_isShared_6152_ = v_isSharedCheck_6178_;
goto v_resetjp_6150_;
}
v_resetjp_6150_:
{
lean_object* v_fst_6153_; 
v_fst_6153_ = lean_ctor_get(v_a_6149_, 0);
if (lean_obj_tag(v_fst_6153_) == 0)
{
lean_object* v_snd_6154_; lean_object* v___x_6155_; lean_object* v_caches_6156_; lean_object* v_typeAnalysis_6157_; lean_object* v_target_6158_; uint8_t v_didChange_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6172_; 
v_snd_6154_ = lean_ctor_get(v_a_6149_, 1);
lean_inc(v_snd_6154_);
lean_dec(v_a_6149_);
v___x_6155_ = lean_st_ref_take(v_a_6130_);
v_caches_6156_ = lean_ctor_get(v___x_6155_, 0);
v_typeAnalysis_6157_ = lean_ctor_get(v___x_6155_, 1);
v_target_6158_ = lean_ctor_get(v___x_6155_, 2);
v_didChange_6159_ = lean_ctor_get_uint8(v___x_6155_, sizeof(void*)*4);
v_isSharedCheck_6172_ = !lean_is_exclusive(v___x_6155_);
if (v_isSharedCheck_6172_ == 0)
{
lean_object* v_unused_6173_; 
v_unused_6173_ = lean_ctor_get(v___x_6155_, 3);
lean_dec(v_unused_6173_);
v___x_6161_ = v___x_6155_;
v_isShared_6162_ = v_isSharedCheck_6172_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_target_6158_);
lean_inc(v_typeAnalysis_6157_);
lean_inc(v_caches_6156_);
lean_dec(v___x_6155_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6172_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
lean_object* v___x_6164_; 
if (v_isShared_6162_ == 0)
{
lean_ctor_set(v___x_6161_, 3, v_snd_6154_);
v___x_6164_ = v___x_6161_;
goto v_reusejp_6163_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_caches_6156_);
lean_ctor_set(v_reuseFailAlloc_6171_, 1, v_typeAnalysis_6157_);
lean_ctor_set(v_reuseFailAlloc_6171_, 2, v_target_6158_);
lean_ctor_set(v_reuseFailAlloc_6171_, 3, v_snd_6154_);
lean_ctor_set_uint8(v_reuseFailAlloc_6171_, sizeof(void*)*4, v_didChange_6159_);
v___x_6164_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6163_;
}
v_reusejp_6163_:
{
lean_object* v___x_6165_; uint8_t v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6169_; 
v___x_6165_ = lean_st_ref_put(v_a_6130_, v___x_6164_);
v___x_6166_ = 0;
v___x_6167_ = lean_box(v___x_6166_);
if (v_isShared_6152_ == 0)
{
lean_ctor_set(v___x_6151_, 0, v___x_6167_);
v___x_6169_ = v___x_6151_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6170_; 
v_reuseFailAlloc_6170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6170_, 0, v___x_6167_);
v___x_6169_ = v_reuseFailAlloc_6170_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
return v___x_6169_;
}
}
}
}
else
{
lean_object* v_val_6174_; lean_object* v___x_6176_; 
lean_inc_ref(v_fst_6153_);
lean_dec(v_a_6149_);
v_val_6174_ = lean_ctor_get(v_fst_6153_, 0);
lean_inc(v_val_6174_);
lean_dec_ref_known(v_fst_6153_, 1);
if (v_isShared_6152_ == 0)
{
lean_ctor_set(v___x_6151_, 0, v_val_6174_);
v___x_6176_ = v___x_6151_;
goto v_reusejp_6175_;
}
else
{
lean_object* v_reuseFailAlloc_6177_; 
v_reuseFailAlloc_6177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6177_, 0, v_val_6174_);
v___x_6176_ = v_reuseFailAlloc_6177_;
goto v_reusejp_6175_;
}
v_reusejp_6175_:
{
return v___x_6176_;
}
}
}
}
else
{
lean_object* v_a_6179_; lean_object* v___x_6181_; uint8_t v_isShared_6182_; uint8_t v_isSharedCheck_6186_; 
v_a_6179_ = lean_ctor_get(v___x_6148_, 0);
v_isSharedCheck_6186_ = !lean_is_exclusive(v___x_6148_);
if (v_isSharedCheck_6186_ == 0)
{
v___x_6181_ = v___x_6148_;
v_isShared_6182_ = v_isSharedCheck_6186_;
goto v_resetjp_6180_;
}
else
{
lean_inc(v_a_6179_);
lean_dec(v___x_6148_);
v___x_6181_ = lean_box(0);
v_isShared_6182_ = v_isSharedCheck_6186_;
goto v_resetjp_6180_;
}
v_resetjp_6180_:
{
lean_object* v___x_6184_; 
if (v_isShared_6182_ == 0)
{
v___x_6184_ = v___x_6181_;
goto v_reusejp_6183_;
}
else
{
lean_object* v_reuseFailAlloc_6185_; 
v_reuseFailAlloc_6185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6185_, 0, v_a_6179_);
v___x_6184_ = v_reuseFailAlloc_6185_;
goto v_reusejp_6183_;
}
v_reusejp_6183_:
{
return v___x_6184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_6187_, lean_object* v_config_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_, lean_object* v_a_6191_, lean_object* v_a_6192_, lean_object* v_a_6193_, lean_object* v_a_6194_, lean_object* v_a_6195_, lean_object* v_a_6196_, lean_object* v_a_6197_, lean_object* v_a_6198_, lean_object* v_a_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_){
_start:
{
lean_object* v_res_6202_; 
v_res_6202_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_6187_, v_config_6188_, v_a_6189_, v_a_6190_, v_a_6191_, v_a_6192_, v_a_6193_, v_a_6194_, v_a_6195_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_, v_a_6200_);
lean_dec(v_a_6200_);
lean_dec_ref(v_a_6199_);
lean_dec(v_a_6198_);
lean_dec_ref(v_a_6197_);
lean_dec(v_a_6196_);
lean_dec_ref(v_a_6195_);
lean_dec(v_a_6194_);
lean_dec_ref(v_a_6193_);
lean_dec(v_a_6192_);
lean_dec(v_a_6191_);
lean_dec_ref(v_a_6190_);
lean_dec(v_a_6189_);
return v_res_6202_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_6203_, lean_object* v_msg_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_){
_start:
{
lean_object* v___x_6218_; 
v___x_6218_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_6203_, v_msg_6204_, v___y_6213_, v___y_6214_, v___y_6215_, v___y_6216_);
return v___x_6218_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_6219_, lean_object* v_msg_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_){
_start:
{
lean_object* v_res_6234_; 
v_res_6234_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_6219_, v_msg_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
lean_dec(v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
lean_dec(v___y_6226_);
lean_dec_ref(v___y_6225_);
lean_dec(v___y_6224_);
lean_dec(v___y_6223_);
lean_dec_ref(v___y_6222_);
lean_dec(v___y_6221_);
return v_res_6234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_6235_, lean_object* v___x_6236_, lean_object* v_methods_6237_, lean_object* v_config_6238_, lean_object* v_inst_6239_, lean_object* v_R_6240_, lean_object* v_a_6241_, lean_object* v_b_6242_, lean_object* v_c_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_){
_start:
{
lean_object* v___x_6257_; 
v___x_6257_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_6235_, v___x_6236_, v_methods_6237_, v_config_6238_, v_a_6241_, v_b_6242_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
return v___x_6257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_6258_ = _args[0];
lean_object* v___x_6259_ = _args[1];
lean_object* v_methods_6260_ = _args[2];
lean_object* v_config_6261_ = _args[3];
lean_object* v_inst_6262_ = _args[4];
lean_object* v_R_6263_ = _args[5];
lean_object* v_a_6264_ = _args[6];
lean_object* v_b_6265_ = _args[7];
lean_object* v_c_6266_ = _args[8];
lean_object* v___y_6267_ = _args[9];
lean_object* v___y_6268_ = _args[10];
lean_object* v___y_6269_ = _args[11];
lean_object* v___y_6270_ = _args[12];
lean_object* v___y_6271_ = _args[13];
lean_object* v___y_6272_ = _args[14];
lean_object* v___y_6273_ = _args[15];
lean_object* v___y_6274_ = _args[16];
lean_object* v___y_6275_ = _args[17];
lean_object* v___y_6276_ = _args[18];
lean_object* v___y_6277_ = _args[19];
lean_object* v___y_6278_ = _args[20];
lean_object* v___y_6279_ = _args[21];
_start:
{
lean_object* v_res_6280_; 
v_res_6280_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_6258_, v___x_6259_, v_methods_6260_, v_config_6261_, v_inst_6262_, v_R_6263_, v_a_6264_, v_b_6265_, v_c_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_);
lean_dec(v___y_6278_);
lean_dec_ref(v___y_6277_);
lean_dec(v___y_6276_);
lean_dec_ref(v___y_6275_);
lean_dec(v___y_6274_);
lean_dec_ref(v___y_6273_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
lean_dec(v___y_6270_);
lean_dec(v___y_6269_);
lean_dec_ref(v___y_6268_);
lean_dec(v___y_6267_);
lean_dec_ref(v___x_6259_);
lean_dec(v_upperBound_6258_);
return v_res_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_6281_, lean_object* v_config_6282_, lean_object* v_a_6283_, lean_object* v_a_6284_, lean_object* v_a_6285_, lean_object* v_a_6286_, lean_object* v_a_6287_, lean_object* v_a_6288_, lean_object* v_a_6289_, lean_object* v_a_6290_, lean_object* v_a_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_){
_start:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; 
v___x_6295_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_6296_ = lean_st_mk_ref(v___x_6295_);
v___x_6297_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_6281_, v_config_6282_, v___x_6296_, v_a_6283_, v_a_6284_, v_a_6285_, v_a_6286_, v_a_6287_, v_a_6288_, v_a_6289_, v_a_6290_, v_a_6291_, v_a_6292_, v_a_6293_);
if (lean_obj_tag(v___x_6297_) == 0)
{
lean_object* v_a_6298_; lean_object* v___x_6300_; uint8_t v_isShared_6301_; uint8_t v_isSharedCheck_6306_; 
v_a_6298_ = lean_ctor_get(v___x_6297_, 0);
v_isSharedCheck_6306_ = !lean_is_exclusive(v___x_6297_);
if (v_isSharedCheck_6306_ == 0)
{
v___x_6300_ = v___x_6297_;
v_isShared_6301_ = v_isSharedCheck_6306_;
goto v_resetjp_6299_;
}
else
{
lean_inc(v_a_6298_);
lean_dec(v___x_6297_);
v___x_6300_ = lean_box(0);
v_isShared_6301_ = v_isSharedCheck_6306_;
goto v_resetjp_6299_;
}
v_resetjp_6299_:
{
lean_object* v___x_6302_; lean_object* v___x_6304_; 
v___x_6302_ = lean_st_ref_get(v___x_6296_);
lean_dec(v___x_6296_);
lean_dec(v___x_6302_);
if (v_isShared_6301_ == 0)
{
v___x_6304_ = v___x_6300_;
goto v_reusejp_6303_;
}
else
{
lean_object* v_reuseFailAlloc_6305_; 
v_reuseFailAlloc_6305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_a_6298_);
v___x_6304_ = v_reuseFailAlloc_6305_;
goto v_reusejp_6303_;
}
v_reusejp_6303_:
{
return v___x_6304_;
}
}
}
else
{
lean_dec(v___x_6296_);
return v___x_6297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_6307_, lean_object* v_config_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_, lean_object* v_a_6311_, lean_object* v_a_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_, lean_object* v_a_6318_, lean_object* v_a_6319_, lean_object* v_a_6320_){
_start:
{
lean_object* v_res_6321_; 
v_res_6321_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_6307_, v_config_6308_, v_a_6309_, v_a_6310_, v_a_6311_, v_a_6312_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_, v_a_6319_);
lean_dec(v_a_6319_);
lean_dec_ref(v_a_6318_);
lean_dec(v_a_6317_);
lean_dec_ref(v_a_6316_);
lean_dec(v_a_6315_);
lean_dec_ref(v_a_6314_);
lean_dec(v_a_6313_);
lean_dec_ref(v_a_6312_);
lean_dec(v_a_6311_);
lean_dec(v_a_6310_);
lean_dec_ref(v_a_6309_);
return v_res_6321_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6323_; lean_object* v___x_6324_; 
v___x_6323_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_6324_ = l_Lean_stringToMessageData(v___x_6323_);
return v___x_6324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_6325_, lean_object* v_x_6326_, lean_object* v___y_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_){
_start:
{
lean_object* v___x_6339_; lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; 
v___x_6339_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_6340_ = l_Lean_MessageData_ofName(v_name_6325_);
v___x_6341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6341_, 0, v___x_6339_);
lean_ctor_set(v___x_6341_, 1, v___x_6340_);
v___x_6342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6342_, 0, v___x_6341_);
return v___x_6342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_6343_, lean_object* v_x_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_, lean_object* v___y_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_){
_start:
{
lean_object* v_res_6357_; 
v_res_6357_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_6343_, v_x_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_, v___y_6355_);
lean_dec(v___y_6355_);
lean_dec_ref(v___y_6354_);
lean_dec(v___y_6353_);
lean_dec_ref(v___y_6352_);
lean_dec(v___y_6351_);
lean_dec_ref(v___y_6350_);
lean_dec(v___y_6349_);
lean_dec_ref(v___y_6348_);
lean_dec(v___y_6347_);
lean_dec(v___y_6346_);
lean_dec_ref(v___y_6345_);
lean_dec_ref(v_x_6344_);
return v_res_6357_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_6358_; 
v___x_6358_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_6358_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_6359_; lean_object* v___x_6360_; 
v___x_6359_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_6360_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_6359_);
return v___x_6360_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_6361_; lean_object* v___x_6362_; 
v___x_6361_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_6362_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_6361_);
return v___x_6362_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_6363_; lean_object* v___x_6364_; 
v___x_6363_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_6364_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_6363_);
return v___x_6364_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6365_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_6366_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_6365_);
return v___x_6366_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; 
v___x_6367_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_6368_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_6367_);
return v___x_6368_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_6369_; lean_object* v___x_6370_; 
v___x_6369_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_6370_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_6369_);
return v___x_6370_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_6371_; lean_object* v___x_6372_; 
v___x_6371_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_6372_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_6371_);
return v___x_6372_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; 
v___x_6373_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_6374_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_6373_);
return v___x_6374_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_6375_; lean_object* v___x_6376_; 
v___x_6375_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_6376_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_6375_);
return v___x_6376_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_6377_; lean_object* v___x_6378_; 
v___x_6377_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_6378_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_6377_);
return v___x_6378_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6379_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_6380_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_6379_);
return v___x_6380_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_6382_; double v___x_6383_; 
v___x_6382_ = lean_unsigned_to_nat(1000000000u);
v___x_6383_ = lean_float_of_nat(v___x_6382_);
return v___x_6383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_, lean_object* v_a_6391_, lean_object* v_a_6392_, lean_object* v_a_6393_, lean_object* v_a_6394_, lean_object* v_a_6395_){
_start:
{
lean_object* v___x_6397_; lean_object* v_toApplicative_6398_; lean_object* v_toFunctor_6399_; lean_object* v_toSeq_6400_; lean_object* v_toSeqLeft_6401_; lean_object* v_toSeqRight_6402_; lean_object* v___f_6403_; lean_object* v___f_6404_; lean_object* v___f_6405_; lean_object* v___f_6406_; lean_object* v___x_6407_; lean_object* v___f_6408_; lean_object* v___f_6409_; lean_object* v___f_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v_toApplicative_6414_; lean_object* v___x_6416_; uint8_t v_isShared_6417_; uint8_t v_isSharedCheck_6558_; 
v___x_6397_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_6398_ = lean_ctor_get(v___x_6397_, 0);
v_toFunctor_6399_ = lean_ctor_get(v_toApplicative_6398_, 0);
v_toSeq_6400_ = lean_ctor_get(v_toApplicative_6398_, 2);
v_toSeqLeft_6401_ = lean_ctor_get(v_toApplicative_6398_, 3);
v_toSeqRight_6402_ = lean_ctor_get(v_toApplicative_6398_, 4);
v___f_6403_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_6404_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_6399_, 2);
v___f_6405_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_6405_, 0, v_toFunctor_6399_);
v___f_6406_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_6406_, 0, v_toFunctor_6399_);
v___x_6407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6407_, 0, v___f_6405_);
lean_ctor_set(v___x_6407_, 1, v___f_6406_);
lean_inc(v_toSeqRight_6402_);
v___f_6408_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_6408_, 0, v_toSeqRight_6402_);
lean_inc(v_toSeqLeft_6401_);
v___f_6409_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_6409_, 0, v_toSeqLeft_6401_);
lean_inc(v_toSeq_6400_);
v___f_6410_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_6410_, 0, v_toSeq_6400_);
v___x_6411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6411_, 0, v___x_6407_);
lean_ctor_set(v___x_6411_, 1, v___f_6403_);
lean_ctor_set(v___x_6411_, 2, v___f_6410_);
lean_ctor_set(v___x_6411_, 3, v___f_6409_);
lean_ctor_set(v___x_6411_, 4, v___f_6408_);
v___x_6412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6412_, 0, v___x_6411_);
lean_ctor_set(v___x_6412_, 1, v___f_6404_);
v___x_6413_ = l_StateRefT_x27_instMonad___redArg(v___x_6412_);
v_toApplicative_6414_ = lean_ctor_get(v___x_6413_, 0);
v_isSharedCheck_6558_ = !lean_is_exclusive(v___x_6413_);
if (v_isSharedCheck_6558_ == 0)
{
lean_object* v_unused_6559_; 
v_unused_6559_ = lean_ctor_get(v___x_6413_, 1);
lean_dec(v_unused_6559_);
v___x_6416_ = v___x_6413_;
v_isShared_6417_ = v_isSharedCheck_6558_;
goto v_resetjp_6415_;
}
else
{
lean_inc(v_toApplicative_6414_);
lean_dec(v___x_6413_);
v___x_6416_ = lean_box(0);
v_isShared_6417_ = v_isSharedCheck_6558_;
goto v_resetjp_6415_;
}
v_resetjp_6415_:
{
lean_object* v_toFunctor_6418_; lean_object* v_toSeq_6419_; lean_object* v_toSeqLeft_6420_; lean_object* v_toSeqRight_6421_; lean_object* v___x_6423_; uint8_t v_isShared_6424_; uint8_t v_isSharedCheck_6556_; 
v_toFunctor_6418_ = lean_ctor_get(v_toApplicative_6414_, 0);
v_toSeq_6419_ = lean_ctor_get(v_toApplicative_6414_, 2);
v_toSeqLeft_6420_ = lean_ctor_get(v_toApplicative_6414_, 3);
v_toSeqRight_6421_ = lean_ctor_get(v_toApplicative_6414_, 4);
v_isSharedCheck_6556_ = !lean_is_exclusive(v_toApplicative_6414_);
if (v_isSharedCheck_6556_ == 0)
{
lean_object* v_unused_6557_; 
v_unused_6557_ = lean_ctor_get(v_toApplicative_6414_, 1);
lean_dec(v_unused_6557_);
v___x_6423_ = v_toApplicative_6414_;
v_isShared_6424_ = v_isSharedCheck_6556_;
goto v_resetjp_6422_;
}
else
{
lean_inc(v_toSeqRight_6421_);
lean_inc(v_toSeqLeft_6420_);
lean_inc(v_toSeq_6419_);
lean_inc(v_toFunctor_6418_);
lean_dec(v_toApplicative_6414_);
v___x_6423_ = lean_box(0);
v_isShared_6424_ = v_isSharedCheck_6556_;
goto v_resetjp_6422_;
}
v_resetjp_6422_:
{
lean_object* v___f_6425_; lean_object* v___f_6426_; lean_object* v___f_6427_; lean_object* v___f_6428_; lean_object* v___x_6429_; lean_object* v___f_6430_; lean_object* v___f_6431_; lean_object* v___f_6432_; lean_object* v___x_6434_; 
v___f_6425_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_6426_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_6418_);
v___f_6427_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_6427_, 0, v_toFunctor_6418_);
v___f_6428_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_6428_, 0, v_toFunctor_6418_);
v___x_6429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6429_, 0, v___f_6427_);
lean_ctor_set(v___x_6429_, 1, v___f_6428_);
v___f_6430_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_6430_, 0, v_toSeqRight_6421_);
v___f_6431_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_6431_, 0, v_toSeqLeft_6420_);
v___f_6432_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_6432_, 0, v_toSeq_6419_);
if (v_isShared_6424_ == 0)
{
lean_ctor_set(v___x_6423_, 4, v___f_6430_);
lean_ctor_set(v___x_6423_, 3, v___f_6431_);
lean_ctor_set(v___x_6423_, 2, v___f_6432_);
lean_ctor_set(v___x_6423_, 1, v___f_6425_);
lean_ctor_set(v___x_6423_, 0, v___x_6429_);
v___x_6434_ = v___x_6423_;
goto v_reusejp_6433_;
}
else
{
lean_object* v_reuseFailAlloc_6555_; 
v_reuseFailAlloc_6555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6555_, 0, v___x_6429_);
lean_ctor_set(v_reuseFailAlloc_6555_, 1, v___f_6425_);
lean_ctor_set(v_reuseFailAlloc_6555_, 2, v___f_6432_);
lean_ctor_set(v_reuseFailAlloc_6555_, 3, v___f_6431_);
lean_ctor_set(v_reuseFailAlloc_6555_, 4, v___f_6430_);
v___x_6434_ = v_reuseFailAlloc_6555_;
goto v_reusejp_6433_;
}
v_reusejp_6433_:
{
lean_object* v___x_6436_; 
if (v_isShared_6417_ == 0)
{
lean_ctor_set(v___x_6416_, 1, v___f_6426_);
lean_ctor_set(v___x_6416_, 0, v___x_6434_);
v___x_6436_ = v___x_6416_;
goto v_reusejp_6435_;
}
else
{
lean_object* v_reuseFailAlloc_6554_; 
v_reuseFailAlloc_6554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6554_, 0, v___x_6434_);
lean_ctor_set(v_reuseFailAlloc_6554_, 1, v___f_6426_);
v___x_6436_ = v_reuseFailAlloc_6554_;
goto v_reusejp_6435_;
}
v_reusejp_6435_:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v___x_6445_; lean_object* v_toMonadRef_6446_; lean_object* v___x_6447_; lean_object* v_options_6448_; uint8_t v_hasTrace_6449_; 
v___x_6437_ = l_StateRefT_x27_instMonad___redArg(v___x_6436_);
v___x_6438_ = l_ReaderT_instMonad___redArg(v___x_6437_);
v___x_6439_ = l_StateRefT_x27_instMonad___redArg(v___x_6438_);
v___x_6440_ = l_ReaderT_instMonad___redArg(v___x_6439_);
v___x_6441_ = l_ReaderT_instMonad___redArg(v___x_6440_);
v___x_6442_ = l_StateRefT_x27_instMonad___redArg(v___x_6441_);
v___x_6443_ = l_ReaderT_instMonad___redArg(v___x_6442_);
v___x_6444_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_6445_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_6446_ = lean_ctor_get(v___x_6445_, 0);
v___x_6447_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_options_6448_ = lean_ctor_get(v_a_6394_, 2);
v_hasTrace_6449_ = lean_ctor_get_uint8(v_options_6448_, sizeof(void*)*1);
if (v_hasTrace_6449_ == 0)
{
lean_object* v_run_x27_6450_; lean_object* v___x_6451_; 
lean_dec_ref(v___x_6443_);
v_run_x27_6450_ = lean_ctor_get(v_pass_6384_, 1);
lean_inc_ref(v_run_x27_6450_);
lean_dec_ref(v_pass_6384_);
lean_inc(v_a_6395_);
lean_inc_ref(v_a_6394_);
lean_inc(v_a_6393_);
lean_inc_ref(v_a_6392_);
lean_inc(v_a_6391_);
lean_inc_ref(v_a_6390_);
lean_inc(v_a_6389_);
lean_inc_ref(v_a_6388_);
lean_inc(v_a_6387_);
lean_inc(v_a_6386_);
lean_inc_ref(v_a_6385_);
v___x_6451_ = lean_apply_12(v_run_x27_6450_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_, lean_box(0));
return v___x_6451_;
}
else
{
lean_object* v_name_6452_; lean_object* v_run_x27_6453_; lean_object* v___x_6455_; uint8_t v_isShared_6456_; uint8_t v_isSharedCheck_6553_; 
v_name_6452_ = lean_ctor_get(v_pass_6384_, 0);
v_run_x27_6453_ = lean_ctor_get(v_pass_6384_, 1);
v_isSharedCheck_6553_ = !lean_is_exclusive(v_pass_6384_);
if (v_isSharedCheck_6553_ == 0)
{
v___x_6455_ = v_pass_6384_;
v_isShared_6456_ = v_isSharedCheck_6553_;
goto v_resetjp_6454_;
}
else
{
lean_inc(v_run_x27_6453_);
lean_inc(v_name_6452_);
lean_dec(v_pass_6384_);
v___x_6455_ = lean_box(0);
v_isShared_6456_ = v_isSharedCheck_6553_;
goto v_resetjp_6454_;
}
v_resetjp_6454_:
{
lean_object* v_inheritedTraceOptions_6457_; lean_object* v___f_6458_; lean_object* v___f_6459_; lean_object* v___f_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; uint8_t v___x_6464_; lean_object* v___y_6466_; lean_object* v___y_6467_; lean_object* v_a_6468_; lean_object* v___y_6484_; lean_object* v___y_6485_; lean_object* v_a_6486_; 
v_inheritedTraceOptions_6457_ = lean_ctor_get(v_a_6394_, 13);
v___f_6458_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6458_, 0, v_name_6452_);
v___f_6459_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_6460_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_6461_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_6462_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6463_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_6464_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6457_, v_options_6448_, v___x_6463_);
if (v___x_6464_ == 0)
{
lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; uint8_t v___x_6551_; 
v___x_6548_ = l_Lean_KVMap_instValueBool;
v___x_6549_ = l_Lean_trace_profiler;
v___x_6550_ = l_Lean_Option_get___redArg(v___x_6548_, v_options_6448_, v___x_6549_);
v___x_6551_ = lean_unbox(v___x_6550_);
lean_dec(v___x_6550_);
if (v___x_6551_ == 0)
{
lean_object* v___x_6552_; 
lean_dec_ref(v___f_6458_);
lean_del_object(v___x_6455_);
lean_dec_ref(v___x_6443_);
lean_inc(v_a_6395_);
lean_inc_ref(v_a_6394_);
lean_inc(v_a_6393_);
lean_inc_ref(v_a_6392_);
lean_inc(v_a_6391_);
lean_inc_ref(v_a_6390_);
lean_inc(v_a_6389_);
lean_inc_ref(v_a_6388_);
lean_inc(v_a_6387_);
lean_inc(v_a_6386_);
lean_inc_ref(v_a_6385_);
v___x_6552_ = lean_apply_12(v_run_x27_6453_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_, lean_box(0));
return v___x_6552_;
}
else
{
goto v___jp_6496_;
}
}
else
{
goto v___jp_6496_;
}
v___jp_6465_:
{
lean_object* v___x_6469_; double v___x_6470_; double v___x_6471_; double v___x_6472_; double v___x_6473_; double v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6478_; 
v___x_6469_ = lean_io_mono_nanos_now();
v___x_6470_ = lean_float_of_nat(v___y_6466_);
v___x_6471_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6472_ = lean_float_div(v___x_6470_, v___x_6471_);
v___x_6473_ = lean_float_of_nat(v___x_6469_);
v___x_6474_ = lean_float_div(v___x_6473_, v___x_6471_);
v___x_6475_ = lean_box_float(v___x_6472_);
v___x_6476_ = lean_box_float(v___x_6474_);
if (v_isShared_6456_ == 0)
{
lean_ctor_set(v___x_6455_, 1, v___x_6476_);
lean_ctor_set(v___x_6455_, 0, v___x_6475_);
v___x_6478_ = v___x_6455_;
goto v_reusejp_6477_;
}
else
{
lean_object* v_reuseFailAlloc_6482_; 
v_reuseFailAlloc_6482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6482_, 0, v___x_6475_);
lean_ctor_set(v_reuseFailAlloc_6482_, 1, v___x_6476_);
v___x_6478_ = v_reuseFailAlloc_6482_;
goto v_reusejp_6477_;
}
v_reusejp_6477_:
{
lean_object* v___x_6479_; lean_object* v___x_29258__overap_6480_; lean_object* v___x_6481_; 
v___x_6479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6479_, 0, v_a_6468_);
lean_ctor_set(v___x_6479_, 1, v___x_6478_);
lean_inc_ref(v_toMonadRef_6446_);
v___x_29258__overap_6480_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_6443_, v___x_6444_, v_toMonadRef_6446_, v___f_6459_, lean_box(0), v___x_6447_, v___f_6460_, v___x_6461_, v_hasTrace_6449_, v___x_6462_, v_options_6448_, v___x_6464_, v___y_6467_, v___f_6458_, v___x_6479_);
lean_inc(v_a_6395_);
lean_inc_ref(v_a_6394_);
lean_inc(v_a_6393_);
lean_inc_ref(v_a_6392_);
lean_inc(v_a_6391_);
lean_inc_ref(v_a_6390_);
lean_inc(v_a_6389_);
lean_inc_ref(v_a_6388_);
lean_inc(v_a_6387_);
lean_inc(v_a_6386_);
lean_inc_ref(v_a_6385_);
v___x_6481_ = lean_apply_12(v___x_29258__overap_6480_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_, lean_box(0));
return v___x_6481_;
}
}
v___jp_6483_:
{
lean_object* v___x_6487_; double v___x_6488_; double v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_29279__overap_6494_; lean_object* v___x_6495_; 
v___x_6487_ = lean_io_get_num_heartbeats();
v___x_6488_ = lean_float_of_nat(v___y_6485_);
v___x_6489_ = lean_float_of_nat(v___x_6487_);
v___x_6490_ = lean_box_float(v___x_6488_);
v___x_6491_ = lean_box_float(v___x_6489_);
v___x_6492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6492_, 0, v___x_6490_);
lean_ctor_set(v___x_6492_, 1, v___x_6491_);
v___x_6493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6493_, 0, v_a_6486_);
lean_ctor_set(v___x_6493_, 1, v___x_6492_);
lean_inc_ref(v_toMonadRef_6446_);
v___x_29279__overap_6494_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_6443_, v___x_6444_, v_toMonadRef_6446_, v___f_6459_, lean_box(0), v___x_6447_, v___f_6460_, v___x_6461_, v_hasTrace_6449_, v___x_6462_, v_options_6448_, v___x_6464_, v___y_6484_, v___f_6458_, v___x_6493_);
lean_inc(v_a_6395_);
lean_inc_ref(v_a_6394_);
lean_inc(v_a_6393_);
lean_inc_ref(v_a_6392_);
lean_inc(v_a_6391_);
lean_inc_ref(v_a_6390_);
lean_inc(v_a_6389_);
lean_inc_ref(v_a_6388_);
lean_inc(v_a_6387_);
lean_inc(v_a_6386_);
lean_inc_ref(v_a_6385_);
v___x_6495_ = lean_apply_12(v___x_29279__overap_6494_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_, lean_box(0));
return v___x_6495_;
}
v___jp_6496_:
{
lean_object* v___x_29235__overap_6497_; lean_object* v___x_6498_; 
lean_inc_ref(v___x_6443_);
v___x_29235__overap_6497_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_6443_, v___x_6444_);
lean_inc(v_a_6395_);
lean_inc_ref(v_a_6394_);
lean_inc(v_a_6393_);
lean_inc_ref(v_a_6392_);
lean_inc(v_a_6391_);
lean_inc_ref(v_a_6390_);
lean_inc(v_a_6389_);
lean_inc_ref(v_a_6388_);
lean_inc(v_a_6387_);
lean_inc(v_a_6386_);
lean_inc_ref(v_a_6385_);
v___x_6498_ = lean_apply_12(v___x_29235__overap_6497_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_, lean_box(0));
if (lean_obj_tag(v___x_6498_) == 0)
{
lean_object* v_a_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; uint8_t v___x_6503_; 
v_a_6499_ = lean_ctor_get(v___x_6498_, 0);
lean_inc(v_a_6499_);
lean_dec_ref_known(v___x_6498_, 1);
v___x_6500_ = l_Lean_KVMap_instValueBool;
v___x_6501_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6502_ = l_Lean_Option_get___redArg(v___x_6500_, v_options_6448_, v___x_6501_);
v___x_6503_ = lean_unbox(v___x_6502_);
lean_dec(v___x_6502_);
if (v___x_6503_ == 0)
{
lean_object* v___x_6504_; lean_object* v___x_6505_; 
v___x_6504_ = lean_io_mono_nanos_now();
lean_inc(v_a_6395_);
lean_inc_ref(v_a_6394_);
lean_inc(v_a_6393_);
lean_inc_ref(v_a_6392_);
lean_inc(v_a_6391_);
lean_inc_ref(v_a_6390_);
lean_inc(v_a_6389_);
lean_inc_ref(v_a_6388_);
lean_inc(v_a_6387_);
lean_inc(v_a_6386_);
lean_inc_ref(v_a_6385_);
v___x_6505_ = lean_apply_12(v_run_x27_6453_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_, lean_box(0));
if (lean_obj_tag(v___x_6505_) == 0)
{
lean_object* v_a_6506_; lean_object* v___x_6508_; uint8_t v_isShared_6509_; uint8_t v_isSharedCheck_6513_; 
v_a_6506_ = lean_ctor_get(v___x_6505_, 0);
v_isSharedCheck_6513_ = !lean_is_exclusive(v___x_6505_);
if (v_isSharedCheck_6513_ == 0)
{
v___x_6508_ = v___x_6505_;
v_isShared_6509_ = v_isSharedCheck_6513_;
goto v_resetjp_6507_;
}
else
{
lean_inc(v_a_6506_);
lean_dec(v___x_6505_);
v___x_6508_ = lean_box(0);
v_isShared_6509_ = v_isSharedCheck_6513_;
goto v_resetjp_6507_;
}
v_resetjp_6507_:
{
lean_object* v___x_6511_; 
if (v_isShared_6509_ == 0)
{
lean_ctor_set_tag(v___x_6508_, 1);
v___x_6511_ = v___x_6508_;
goto v_reusejp_6510_;
}
else
{
lean_object* v_reuseFailAlloc_6512_; 
v_reuseFailAlloc_6512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6512_, 0, v_a_6506_);
v___x_6511_ = v_reuseFailAlloc_6512_;
goto v_reusejp_6510_;
}
v_reusejp_6510_:
{
v___y_6466_ = v___x_6504_;
v___y_6467_ = v_a_6499_;
v_a_6468_ = v___x_6511_;
goto v___jp_6465_;
}
}
}
else
{
lean_object* v_a_6514_; lean_object* v___x_6516_; uint8_t v_isShared_6517_; uint8_t v_isSharedCheck_6521_; 
v_a_6514_ = lean_ctor_get(v___x_6505_, 0);
v_isSharedCheck_6521_ = !lean_is_exclusive(v___x_6505_);
if (v_isSharedCheck_6521_ == 0)
{
v___x_6516_ = v___x_6505_;
v_isShared_6517_ = v_isSharedCheck_6521_;
goto v_resetjp_6515_;
}
else
{
lean_inc(v_a_6514_);
lean_dec(v___x_6505_);
v___x_6516_ = lean_box(0);
v_isShared_6517_ = v_isSharedCheck_6521_;
goto v_resetjp_6515_;
}
v_resetjp_6515_:
{
lean_object* v___x_6519_; 
if (v_isShared_6517_ == 0)
{
lean_ctor_set_tag(v___x_6516_, 0);
v___x_6519_ = v___x_6516_;
goto v_reusejp_6518_;
}
else
{
lean_object* v_reuseFailAlloc_6520_; 
v_reuseFailAlloc_6520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6520_, 0, v_a_6514_);
v___x_6519_ = v_reuseFailAlloc_6520_;
goto v_reusejp_6518_;
}
v_reusejp_6518_:
{
v___y_6466_ = v___x_6504_;
v___y_6467_ = v_a_6499_;
v_a_6468_ = v___x_6519_;
goto v___jp_6465_;
}
}
}
}
else
{
lean_object* v___x_6522_; lean_object* v___x_6523_; 
lean_del_object(v___x_6455_);
v___x_6522_ = lean_io_get_num_heartbeats();
lean_inc(v_a_6395_);
lean_inc_ref(v_a_6394_);
lean_inc(v_a_6393_);
lean_inc_ref(v_a_6392_);
lean_inc(v_a_6391_);
lean_inc_ref(v_a_6390_);
lean_inc(v_a_6389_);
lean_inc_ref(v_a_6388_);
lean_inc(v_a_6387_);
lean_inc(v_a_6386_);
lean_inc_ref(v_a_6385_);
v___x_6523_ = lean_apply_12(v_run_x27_6453_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_, lean_box(0));
if (lean_obj_tag(v___x_6523_) == 0)
{
lean_object* v_a_6524_; lean_object* v___x_6526_; uint8_t v_isShared_6527_; uint8_t v_isSharedCheck_6531_; 
v_a_6524_ = lean_ctor_get(v___x_6523_, 0);
v_isSharedCheck_6531_ = !lean_is_exclusive(v___x_6523_);
if (v_isSharedCheck_6531_ == 0)
{
v___x_6526_ = v___x_6523_;
v_isShared_6527_ = v_isSharedCheck_6531_;
goto v_resetjp_6525_;
}
else
{
lean_inc(v_a_6524_);
lean_dec(v___x_6523_);
v___x_6526_ = lean_box(0);
v_isShared_6527_ = v_isSharedCheck_6531_;
goto v_resetjp_6525_;
}
v_resetjp_6525_:
{
lean_object* v___x_6529_; 
if (v_isShared_6527_ == 0)
{
lean_ctor_set_tag(v___x_6526_, 1);
v___x_6529_ = v___x_6526_;
goto v_reusejp_6528_;
}
else
{
lean_object* v_reuseFailAlloc_6530_; 
v_reuseFailAlloc_6530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6530_, 0, v_a_6524_);
v___x_6529_ = v_reuseFailAlloc_6530_;
goto v_reusejp_6528_;
}
v_reusejp_6528_:
{
v___y_6484_ = v_a_6499_;
v___y_6485_ = v___x_6522_;
v_a_6486_ = v___x_6529_;
goto v___jp_6483_;
}
}
}
else
{
lean_object* v_a_6532_; lean_object* v___x_6534_; uint8_t v_isShared_6535_; uint8_t v_isSharedCheck_6539_; 
v_a_6532_ = lean_ctor_get(v___x_6523_, 0);
v_isSharedCheck_6539_ = !lean_is_exclusive(v___x_6523_);
if (v_isSharedCheck_6539_ == 0)
{
v___x_6534_ = v___x_6523_;
v_isShared_6535_ = v_isSharedCheck_6539_;
goto v_resetjp_6533_;
}
else
{
lean_inc(v_a_6532_);
lean_dec(v___x_6523_);
v___x_6534_ = lean_box(0);
v_isShared_6535_ = v_isSharedCheck_6539_;
goto v_resetjp_6533_;
}
v_resetjp_6533_:
{
lean_object* v___x_6537_; 
if (v_isShared_6535_ == 0)
{
lean_ctor_set_tag(v___x_6534_, 0);
v___x_6537_ = v___x_6534_;
goto v_reusejp_6536_;
}
else
{
lean_object* v_reuseFailAlloc_6538_; 
v_reuseFailAlloc_6538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_a_6532_);
v___x_6537_ = v_reuseFailAlloc_6538_;
goto v_reusejp_6536_;
}
v_reusejp_6536_:
{
v___y_6484_ = v_a_6499_;
v___y_6485_ = v___x_6522_;
v_a_6486_ = v___x_6537_;
goto v___jp_6483_;
}
}
}
}
}
else
{
lean_object* v_a_6540_; lean_object* v___x_6542_; uint8_t v_isShared_6543_; uint8_t v_isSharedCheck_6547_; 
lean_dec_ref(v___f_6458_);
lean_del_object(v___x_6455_);
lean_dec_ref(v_run_x27_6453_);
lean_dec_ref(v___x_6443_);
v_a_6540_ = lean_ctor_get(v___x_6498_, 0);
v_isSharedCheck_6547_ = !lean_is_exclusive(v___x_6498_);
if (v_isSharedCheck_6547_ == 0)
{
v___x_6542_ = v___x_6498_;
v_isShared_6543_ = v_isSharedCheck_6547_;
goto v_resetjp_6541_;
}
else
{
lean_inc(v_a_6540_);
lean_dec(v___x_6498_);
v___x_6542_ = lean_box(0);
v_isShared_6543_ = v_isSharedCheck_6547_;
goto v_resetjp_6541_;
}
v_resetjp_6541_:
{
lean_object* v___x_6545_; 
if (v_isShared_6543_ == 0)
{
v___x_6545_ = v___x_6542_;
goto v_reusejp_6544_;
}
else
{
lean_object* v_reuseFailAlloc_6546_; 
v_reuseFailAlloc_6546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6546_, 0, v_a_6540_);
v___x_6545_ = v_reuseFailAlloc_6546_;
goto v_reusejp_6544_;
}
v_reusejp_6544_:
{
return v___x_6545_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6560_, lean_object* v_a_6561_, lean_object* v_a_6562_, lean_object* v_a_6563_, lean_object* v_a_6564_, lean_object* v_a_6565_, lean_object* v_a_6566_, lean_object* v_a_6567_, lean_object* v_a_6568_, lean_object* v_a_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_){
_start:
{
lean_object* v_res_6573_; 
v_res_6573_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6560_, v_a_6561_, v_a_6562_, v_a_6563_, v_a_6564_, v_a_6565_, v_a_6566_, v_a_6567_, v_a_6568_, v_a_6569_, v_a_6570_, v_a_6571_);
lean_dec(v_a_6571_);
lean_dec_ref(v_a_6570_);
lean_dec(v_a_6569_);
lean_dec_ref(v_a_6568_);
lean_dec(v_a_6567_);
lean_dec_ref(v_a_6566_);
lean_dec(v_a_6565_);
lean_dec_ref(v_a_6564_);
lean_dec(v_a_6563_);
lean_dec(v_a_6562_);
lean_dec_ref(v_a_6561_);
return v_res_6573_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; 
v___x_6574_ = lean_unsigned_to_nat(32u);
v___x_6575_ = lean_mk_empty_array_with_capacity(v___x_6574_);
v___x_6576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6576_, 0, v___x_6575_);
return v___x_6576_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; 
v___x_6577_ = ((size_t)5ULL);
v___x_6578_ = lean_unsigned_to_nat(0u);
v___x_6579_ = lean_unsigned_to_nat(32u);
v___x_6580_ = lean_mk_empty_array_with_capacity(v___x_6579_);
v___x_6581_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6582_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6582_, 0, v___x_6581_);
lean_ctor_set(v___x_6582_, 1, v___x_6580_);
lean_ctor_set(v___x_6582_, 2, v___x_6578_);
lean_ctor_set(v___x_6582_, 3, v___x_6578_);
lean_ctor_set_usize(v___x_6582_, 4, v___x_6577_);
return v___x_6582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6583_){
_start:
{
lean_object* v___x_6585_; lean_object* v_traceState_6586_; lean_object* v_traces_6587_; lean_object* v___x_6588_; lean_object* v_traceState_6589_; lean_object* v_env_6590_; lean_object* v_nextMacroScope_6591_; lean_object* v_ngen_6592_; lean_object* v_auxDeclNGen_6593_; lean_object* v_cache_6594_; lean_object* v_messages_6595_; lean_object* v_infoState_6596_; lean_object* v_snapshotTasks_6597_; lean_object* v___x_6599_; uint8_t v_isShared_6600_; uint8_t v_isSharedCheck_6616_; 
v___x_6585_ = lean_st_ref_get(v___y_6583_);
v_traceState_6586_ = lean_ctor_get(v___x_6585_, 4);
lean_inc_ref(v_traceState_6586_);
lean_dec(v___x_6585_);
v_traces_6587_ = lean_ctor_get(v_traceState_6586_, 0);
lean_inc_ref(v_traces_6587_);
lean_dec_ref(v_traceState_6586_);
v___x_6588_ = lean_st_ref_take(v___y_6583_);
v_traceState_6589_ = lean_ctor_get(v___x_6588_, 4);
v_env_6590_ = lean_ctor_get(v___x_6588_, 0);
v_nextMacroScope_6591_ = lean_ctor_get(v___x_6588_, 1);
v_ngen_6592_ = lean_ctor_get(v___x_6588_, 2);
v_auxDeclNGen_6593_ = lean_ctor_get(v___x_6588_, 3);
v_cache_6594_ = lean_ctor_get(v___x_6588_, 5);
v_messages_6595_ = lean_ctor_get(v___x_6588_, 6);
v_infoState_6596_ = lean_ctor_get(v___x_6588_, 7);
v_snapshotTasks_6597_ = lean_ctor_get(v___x_6588_, 8);
v_isSharedCheck_6616_ = !lean_is_exclusive(v___x_6588_);
if (v_isSharedCheck_6616_ == 0)
{
v___x_6599_ = v___x_6588_;
v_isShared_6600_ = v_isSharedCheck_6616_;
goto v_resetjp_6598_;
}
else
{
lean_inc(v_snapshotTasks_6597_);
lean_inc(v_infoState_6596_);
lean_inc(v_messages_6595_);
lean_inc(v_cache_6594_);
lean_inc(v_traceState_6589_);
lean_inc(v_auxDeclNGen_6593_);
lean_inc(v_ngen_6592_);
lean_inc(v_nextMacroScope_6591_);
lean_inc(v_env_6590_);
lean_dec(v___x_6588_);
v___x_6599_ = lean_box(0);
v_isShared_6600_ = v_isSharedCheck_6616_;
goto v_resetjp_6598_;
}
v_resetjp_6598_:
{
uint64_t v_tid_6601_; lean_object* v___x_6603_; uint8_t v_isShared_6604_; uint8_t v_isSharedCheck_6614_; 
v_tid_6601_ = lean_ctor_get_uint64(v_traceState_6589_, sizeof(void*)*1);
v_isSharedCheck_6614_ = !lean_is_exclusive(v_traceState_6589_);
if (v_isSharedCheck_6614_ == 0)
{
lean_object* v_unused_6615_; 
v_unused_6615_ = lean_ctor_get(v_traceState_6589_, 0);
lean_dec(v_unused_6615_);
v___x_6603_ = v_traceState_6589_;
v_isShared_6604_ = v_isSharedCheck_6614_;
goto v_resetjp_6602_;
}
else
{
lean_dec(v_traceState_6589_);
v___x_6603_ = lean_box(0);
v_isShared_6604_ = v_isSharedCheck_6614_;
goto v_resetjp_6602_;
}
v_resetjp_6602_:
{
lean_object* v___x_6605_; lean_object* v___x_6607_; 
v___x_6605_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6604_ == 0)
{
lean_ctor_set(v___x_6603_, 0, v___x_6605_);
v___x_6607_ = v___x_6603_;
goto v_reusejp_6606_;
}
else
{
lean_object* v_reuseFailAlloc_6613_; 
v_reuseFailAlloc_6613_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6613_, 0, v___x_6605_);
lean_ctor_set_uint64(v_reuseFailAlloc_6613_, sizeof(void*)*1, v_tid_6601_);
v___x_6607_ = v_reuseFailAlloc_6613_;
goto v_reusejp_6606_;
}
v_reusejp_6606_:
{
lean_object* v___x_6609_; 
if (v_isShared_6600_ == 0)
{
lean_ctor_set(v___x_6599_, 4, v___x_6607_);
v___x_6609_ = v___x_6599_;
goto v_reusejp_6608_;
}
else
{
lean_object* v_reuseFailAlloc_6612_; 
v_reuseFailAlloc_6612_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6612_, 0, v_env_6590_);
lean_ctor_set(v_reuseFailAlloc_6612_, 1, v_nextMacroScope_6591_);
lean_ctor_set(v_reuseFailAlloc_6612_, 2, v_ngen_6592_);
lean_ctor_set(v_reuseFailAlloc_6612_, 3, v_auxDeclNGen_6593_);
lean_ctor_set(v_reuseFailAlloc_6612_, 4, v___x_6607_);
lean_ctor_set(v_reuseFailAlloc_6612_, 5, v_cache_6594_);
lean_ctor_set(v_reuseFailAlloc_6612_, 6, v_messages_6595_);
lean_ctor_set(v_reuseFailAlloc_6612_, 7, v_infoState_6596_);
lean_ctor_set(v_reuseFailAlloc_6612_, 8, v_snapshotTasks_6597_);
v___x_6609_ = v_reuseFailAlloc_6612_;
goto v_reusejp_6608_;
}
v_reusejp_6608_:
{
lean_object* v___x_6610_; lean_object* v___x_6611_; 
v___x_6610_ = lean_st_ref_put(v___y_6583_, v___x_6609_);
v___x_6611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6611_, 0, v_traces_6587_);
return v___x_6611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6617_, lean_object* v___y_6618_){
_start:
{
lean_object* v_res_6619_; 
v_res_6619_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6617_);
lean_dec(v___y_6617_);
return v_res_6619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6620_, lean_object* v___y_6621_, lean_object* v___y_6622_, lean_object* v___y_6623_, lean_object* v___y_6624_, lean_object* v___y_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_){
_start:
{
lean_object* v___x_6632_; 
v___x_6632_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6630_);
return v___x_6632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_, lean_object* v___y_6640_, lean_object* v___y_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_, lean_object* v___y_6644_){
_start:
{
lean_object* v_res_6645_; 
v_res_6645_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_, v___y_6642_, v___y_6643_);
lean_dec(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec(v___y_6641_);
lean_dec_ref(v___y_6640_);
lean_dec(v___y_6639_);
lean_dec_ref(v___y_6638_);
lean_dec(v___y_6637_);
lean_dec_ref(v___y_6636_);
lean_dec(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
return v_res_6645_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6646_, lean_object* v_opt_6647_){
_start:
{
lean_object* v_name_6648_; lean_object* v_defValue_6649_; lean_object* v_map_6650_; lean_object* v___x_6651_; 
v_name_6648_ = lean_ctor_get(v_opt_6647_, 0);
v_defValue_6649_ = lean_ctor_get(v_opt_6647_, 1);
v_map_6650_ = lean_ctor_get(v_opts_6646_, 0);
v___x_6651_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6650_, v_name_6648_);
if (lean_obj_tag(v___x_6651_) == 0)
{
uint8_t v___x_6652_; 
v___x_6652_ = lean_unbox(v_defValue_6649_);
return v___x_6652_;
}
else
{
lean_object* v_val_6653_; 
v_val_6653_ = lean_ctor_get(v___x_6651_, 0);
lean_inc(v_val_6653_);
lean_dec_ref_known(v___x_6651_, 1);
if (lean_obj_tag(v_val_6653_) == 1)
{
uint8_t v_v_6654_; 
v_v_6654_ = lean_ctor_get_uint8(v_val_6653_, 0);
lean_dec_ref_known(v_val_6653_, 0);
return v_v_6654_;
}
else
{
uint8_t v___x_6655_; 
lean_dec(v_val_6653_);
v___x_6655_ = lean_unbox(v_defValue_6649_);
return v___x_6655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6656_, lean_object* v_opt_6657_){
_start:
{
uint8_t v_res_6658_; lean_object* v_r_6659_; 
v_res_6658_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6656_, v_opt_6657_);
lean_dec_ref(v_opt_6657_);
lean_dec_ref(v_opts_6656_);
v_r_6659_ = lean_box(v_res_6658_);
return v_r_6659_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6660_, lean_object* v_msg_6661_, lean_object* v___y_6662_, lean_object* v___y_6663_, lean_object* v___y_6664_, lean_object* v___y_6665_){
_start:
{
lean_object* v_ref_6667_; lean_object* v___x_6668_; lean_object* v_a_6669_; lean_object* v___x_6671_; uint8_t v_isShared_6672_; uint8_t v_isSharedCheck_6713_; 
v_ref_6667_ = lean_ctor_get(v___y_6664_, 5);
v___x_6668_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6661_, v___y_6662_, v___y_6663_, v___y_6664_, v___y_6665_);
v_a_6669_ = lean_ctor_get(v___x_6668_, 0);
v_isSharedCheck_6713_ = !lean_is_exclusive(v___x_6668_);
if (v_isSharedCheck_6713_ == 0)
{
v___x_6671_ = v___x_6668_;
v_isShared_6672_ = v_isSharedCheck_6713_;
goto v_resetjp_6670_;
}
else
{
lean_inc(v_a_6669_);
lean_dec(v___x_6668_);
v___x_6671_ = lean_box(0);
v_isShared_6672_ = v_isSharedCheck_6713_;
goto v_resetjp_6670_;
}
v_resetjp_6670_:
{
lean_object* v___x_6673_; lean_object* v_traceState_6674_; lean_object* v_env_6675_; lean_object* v_nextMacroScope_6676_; lean_object* v_ngen_6677_; lean_object* v_auxDeclNGen_6678_; lean_object* v_cache_6679_; lean_object* v_messages_6680_; lean_object* v_infoState_6681_; lean_object* v_snapshotTasks_6682_; lean_object* v___x_6684_; uint8_t v_isShared_6685_; uint8_t v_isSharedCheck_6712_; 
v___x_6673_ = lean_st_ref_take(v___y_6665_);
v_traceState_6674_ = lean_ctor_get(v___x_6673_, 4);
v_env_6675_ = lean_ctor_get(v___x_6673_, 0);
v_nextMacroScope_6676_ = lean_ctor_get(v___x_6673_, 1);
v_ngen_6677_ = lean_ctor_get(v___x_6673_, 2);
v_auxDeclNGen_6678_ = lean_ctor_get(v___x_6673_, 3);
v_cache_6679_ = lean_ctor_get(v___x_6673_, 5);
v_messages_6680_ = lean_ctor_get(v___x_6673_, 6);
v_infoState_6681_ = lean_ctor_get(v___x_6673_, 7);
v_snapshotTasks_6682_ = lean_ctor_get(v___x_6673_, 8);
v_isSharedCheck_6712_ = !lean_is_exclusive(v___x_6673_);
if (v_isSharedCheck_6712_ == 0)
{
v___x_6684_ = v___x_6673_;
v_isShared_6685_ = v_isSharedCheck_6712_;
goto v_resetjp_6683_;
}
else
{
lean_inc(v_snapshotTasks_6682_);
lean_inc(v_infoState_6681_);
lean_inc(v_messages_6680_);
lean_inc(v_cache_6679_);
lean_inc(v_traceState_6674_);
lean_inc(v_auxDeclNGen_6678_);
lean_inc(v_ngen_6677_);
lean_inc(v_nextMacroScope_6676_);
lean_inc(v_env_6675_);
lean_dec(v___x_6673_);
v___x_6684_ = lean_box(0);
v_isShared_6685_ = v_isSharedCheck_6712_;
goto v_resetjp_6683_;
}
v_resetjp_6683_:
{
uint64_t v_tid_6686_; lean_object* v_traces_6687_; lean_object* v___x_6689_; uint8_t v_isShared_6690_; uint8_t v_isSharedCheck_6711_; 
v_tid_6686_ = lean_ctor_get_uint64(v_traceState_6674_, sizeof(void*)*1);
v_traces_6687_ = lean_ctor_get(v_traceState_6674_, 0);
v_isSharedCheck_6711_ = !lean_is_exclusive(v_traceState_6674_);
if (v_isSharedCheck_6711_ == 0)
{
v___x_6689_ = v_traceState_6674_;
v_isShared_6690_ = v_isSharedCheck_6711_;
goto v_resetjp_6688_;
}
else
{
lean_inc(v_traces_6687_);
lean_dec(v_traceState_6674_);
v___x_6689_ = lean_box(0);
v_isShared_6690_ = v_isSharedCheck_6711_;
goto v_resetjp_6688_;
}
v_resetjp_6688_:
{
lean_object* v___x_6691_; double v___x_6692_; uint8_t v___x_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; lean_object* v___x_6697_; lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___x_6701_; 
v___x_6691_ = lean_box(0);
v___x_6692_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6693_ = 0;
v___x_6694_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6695_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6695_, 0, v_cls_6660_);
lean_ctor_set(v___x_6695_, 1, v___x_6691_);
lean_ctor_set(v___x_6695_, 2, v___x_6694_);
lean_ctor_set_float(v___x_6695_, sizeof(void*)*3, v___x_6692_);
lean_ctor_set_float(v___x_6695_, sizeof(void*)*3 + 8, v___x_6692_);
lean_ctor_set_uint8(v___x_6695_, sizeof(void*)*3 + 16, v___x_6693_);
v___x_6696_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6697_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6697_, 0, v___x_6695_);
lean_ctor_set(v___x_6697_, 1, v_a_6669_);
lean_ctor_set(v___x_6697_, 2, v___x_6696_);
lean_inc(v_ref_6667_);
v___x_6698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6698_, 0, v_ref_6667_);
lean_ctor_set(v___x_6698_, 1, v___x_6697_);
v___x_6699_ = l_Lean_PersistentArray_push___redArg(v_traces_6687_, v___x_6698_);
if (v_isShared_6690_ == 0)
{
lean_ctor_set(v___x_6689_, 0, v___x_6699_);
v___x_6701_ = v___x_6689_;
goto v_reusejp_6700_;
}
else
{
lean_object* v_reuseFailAlloc_6710_; 
v_reuseFailAlloc_6710_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6710_, 0, v___x_6699_);
lean_ctor_set_uint64(v_reuseFailAlloc_6710_, sizeof(void*)*1, v_tid_6686_);
v___x_6701_ = v_reuseFailAlloc_6710_;
goto v_reusejp_6700_;
}
v_reusejp_6700_:
{
lean_object* v___x_6703_; 
if (v_isShared_6685_ == 0)
{
lean_ctor_set(v___x_6684_, 4, v___x_6701_);
v___x_6703_ = v___x_6684_;
goto v_reusejp_6702_;
}
else
{
lean_object* v_reuseFailAlloc_6709_; 
v_reuseFailAlloc_6709_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6709_, 0, v_env_6675_);
lean_ctor_set(v_reuseFailAlloc_6709_, 1, v_nextMacroScope_6676_);
lean_ctor_set(v_reuseFailAlloc_6709_, 2, v_ngen_6677_);
lean_ctor_set(v_reuseFailAlloc_6709_, 3, v_auxDeclNGen_6678_);
lean_ctor_set(v_reuseFailAlloc_6709_, 4, v___x_6701_);
lean_ctor_set(v_reuseFailAlloc_6709_, 5, v_cache_6679_);
lean_ctor_set(v_reuseFailAlloc_6709_, 6, v_messages_6680_);
lean_ctor_set(v_reuseFailAlloc_6709_, 7, v_infoState_6681_);
lean_ctor_set(v_reuseFailAlloc_6709_, 8, v_snapshotTasks_6682_);
v___x_6703_ = v_reuseFailAlloc_6709_;
goto v_reusejp_6702_;
}
v_reusejp_6702_:
{
lean_object* v___x_6704_; lean_object* v___x_6705_; lean_object* v___x_6707_; 
v___x_6704_ = lean_st_ref_put(v___y_6665_, v___x_6703_);
v___x_6705_ = lean_box(0);
if (v_isShared_6672_ == 0)
{
lean_ctor_set(v___x_6671_, 0, v___x_6705_);
v___x_6707_ = v___x_6671_;
goto v_reusejp_6706_;
}
else
{
lean_object* v_reuseFailAlloc_6708_; 
v_reuseFailAlloc_6708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6708_, 0, v___x_6705_);
v___x_6707_ = v_reuseFailAlloc_6708_;
goto v_reusejp_6706_;
}
v_reusejp_6706_:
{
return v___x_6707_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6714_, lean_object* v_msg_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_, lean_object* v___y_6718_, lean_object* v___y_6719_, lean_object* v___y_6720_){
_start:
{
lean_object* v_res_6721_; 
v_res_6721_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6714_, v_msg_6715_, v___y_6716_, v___y_6717_, v___y_6718_, v___y_6719_);
lean_dec(v___y_6719_);
lean_dec_ref(v___y_6718_);
lean_dec(v___y_6717_);
lean_dec_ref(v___y_6716_);
return v_res_6721_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6722_){
_start:
{
if (lean_obj_tag(v_e_6722_) == 0)
{
uint8_t v___x_6723_; 
v___x_6723_ = 2;
return v___x_6723_;
}
else
{
lean_object* v_a_6724_; uint8_t v___x_6725_; 
v_a_6724_ = lean_ctor_get(v_e_6722_, 0);
v___x_6725_ = lean_unbox(v_a_6724_);
if (v___x_6725_ == 0)
{
uint8_t v___x_6726_; 
v___x_6726_ = 1;
return v___x_6726_;
}
else
{
uint8_t v___x_6727_; 
v___x_6727_ = 0;
return v___x_6727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6728_){
_start:
{
uint8_t v_res_6729_; lean_object* v_r_6730_; 
v_res_6729_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6728_);
lean_dec_ref(v_e_6728_);
v_r_6730_ = lean_box(v_res_6729_);
return v_r_6730_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6731_){
_start:
{
if (lean_obj_tag(v_x_6731_) == 0)
{
lean_object* v_a_6733_; lean_object* v___x_6735_; uint8_t v_isShared_6736_; uint8_t v_isSharedCheck_6740_; 
v_a_6733_ = lean_ctor_get(v_x_6731_, 0);
v_isSharedCheck_6740_ = !lean_is_exclusive(v_x_6731_);
if (v_isSharedCheck_6740_ == 0)
{
v___x_6735_ = v_x_6731_;
v_isShared_6736_ = v_isSharedCheck_6740_;
goto v_resetjp_6734_;
}
else
{
lean_inc(v_a_6733_);
lean_dec(v_x_6731_);
v___x_6735_ = lean_box(0);
v_isShared_6736_ = v_isSharedCheck_6740_;
goto v_resetjp_6734_;
}
v_resetjp_6734_:
{
lean_object* v___x_6738_; 
if (v_isShared_6736_ == 0)
{
lean_ctor_set_tag(v___x_6735_, 1);
v___x_6738_ = v___x_6735_;
goto v_reusejp_6737_;
}
else
{
lean_object* v_reuseFailAlloc_6739_; 
v_reuseFailAlloc_6739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6739_, 0, v_a_6733_);
v___x_6738_ = v_reuseFailAlloc_6739_;
goto v_reusejp_6737_;
}
v_reusejp_6737_:
{
return v___x_6738_;
}
}
}
else
{
lean_object* v_a_6741_; lean_object* v___x_6743_; uint8_t v_isShared_6744_; uint8_t v_isSharedCheck_6748_; 
v_a_6741_ = lean_ctor_get(v_x_6731_, 0);
v_isSharedCheck_6748_ = !lean_is_exclusive(v_x_6731_);
if (v_isSharedCheck_6748_ == 0)
{
v___x_6743_ = v_x_6731_;
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
else
{
lean_inc(v_a_6741_);
lean_dec(v_x_6731_);
v___x_6743_ = lean_box(0);
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
v_resetjp_6742_:
{
lean_object* v___x_6746_; 
if (v_isShared_6744_ == 0)
{
lean_ctor_set_tag(v___x_6743_, 0);
v___x_6746_ = v___x_6743_;
goto v_reusejp_6745_;
}
else
{
lean_object* v_reuseFailAlloc_6747_; 
v_reuseFailAlloc_6747_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6749_, lean_object* v___y_6750_){
_start:
{
lean_object* v_res_6751_; 
v_res_6751_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6749_);
return v_res_6751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6752_, size_t v_i_6753_, lean_object* v_bs_6754_){
_start:
{
uint8_t v___x_6755_; 
v___x_6755_ = lean_usize_dec_lt(v_i_6753_, v_sz_6752_);
if (v___x_6755_ == 0)
{
return v_bs_6754_;
}
else
{
lean_object* v_v_6756_; lean_object* v_msg_6757_; lean_object* v___x_6758_; lean_object* v_bs_x27_6759_; size_t v___x_6760_; size_t v___x_6761_; lean_object* v___x_6762_; 
v_v_6756_ = lean_array_uget_borrowed(v_bs_6754_, v_i_6753_);
v_msg_6757_ = lean_ctor_get(v_v_6756_, 1);
lean_inc_ref(v_msg_6757_);
v___x_6758_ = lean_unsigned_to_nat(0u);
v_bs_x27_6759_ = lean_array_uset(v_bs_6754_, v_i_6753_, v___x_6758_);
v___x_6760_ = ((size_t)1ULL);
v___x_6761_ = lean_usize_add(v_i_6753_, v___x_6760_);
v___x_6762_ = lean_array_uset(v_bs_x27_6759_, v_i_6753_, v_msg_6757_);
v_i_6753_ = v___x_6761_;
v_bs_6754_ = v___x_6762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6764_, lean_object* v_i_6765_, lean_object* v_bs_6766_){
_start:
{
size_t v_sz_boxed_6767_; size_t v_i_boxed_6768_; lean_object* v_res_6769_; 
v_sz_boxed_6767_ = lean_unbox_usize(v_sz_6764_);
lean_dec(v_sz_6764_);
v_i_boxed_6768_ = lean_unbox_usize(v_i_6765_);
lean_dec(v_i_6765_);
v_res_6769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6767_, v_i_boxed_6768_, v_bs_6766_);
return v_res_6769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6770_, lean_object* v_data_6771_, lean_object* v_ref_6772_, lean_object* v_msg_6773_, lean_object* v___y_6774_, lean_object* v___y_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_){
_start:
{
lean_object* v_fileName_6779_; lean_object* v_fileMap_6780_; lean_object* v_options_6781_; lean_object* v_currRecDepth_6782_; lean_object* v_maxRecDepth_6783_; lean_object* v_ref_6784_; lean_object* v_currNamespace_6785_; lean_object* v_openDecls_6786_; lean_object* v_initHeartbeats_6787_; lean_object* v_maxHeartbeats_6788_; lean_object* v_quotContext_6789_; lean_object* v_currMacroScope_6790_; uint8_t v_diag_6791_; lean_object* v_cancelTk_x3f_6792_; uint8_t v_suppressElabErrors_6793_; lean_object* v_inheritedTraceOptions_6794_; lean_object* v___x_6795_; lean_object* v_traceState_6796_; lean_object* v_traces_6797_; lean_object* v_ref_6798_; lean_object* v___x_6799_; lean_object* v___x_6800_; size_t v_sz_6801_; size_t v___x_6802_; lean_object* v___x_6803_; lean_object* v_msg_6804_; lean_object* v___x_6805_; lean_object* v_a_6806_; lean_object* v___x_6808_; uint8_t v_isShared_6809_; uint8_t v_isSharedCheck_6843_; 
v_fileName_6779_ = lean_ctor_get(v___y_6776_, 0);
v_fileMap_6780_ = lean_ctor_get(v___y_6776_, 1);
v_options_6781_ = lean_ctor_get(v___y_6776_, 2);
v_currRecDepth_6782_ = lean_ctor_get(v___y_6776_, 3);
v_maxRecDepth_6783_ = lean_ctor_get(v___y_6776_, 4);
v_ref_6784_ = lean_ctor_get(v___y_6776_, 5);
v_currNamespace_6785_ = lean_ctor_get(v___y_6776_, 6);
v_openDecls_6786_ = lean_ctor_get(v___y_6776_, 7);
v_initHeartbeats_6787_ = lean_ctor_get(v___y_6776_, 8);
v_maxHeartbeats_6788_ = lean_ctor_get(v___y_6776_, 9);
v_quotContext_6789_ = lean_ctor_get(v___y_6776_, 10);
v_currMacroScope_6790_ = lean_ctor_get(v___y_6776_, 11);
v_diag_6791_ = lean_ctor_get_uint8(v___y_6776_, sizeof(void*)*14);
v_cancelTk_x3f_6792_ = lean_ctor_get(v___y_6776_, 12);
v_suppressElabErrors_6793_ = lean_ctor_get_uint8(v___y_6776_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_6794_ = lean_ctor_get(v___y_6776_, 13);
v___x_6795_ = lean_st_ref_get(v___y_6777_);
v_traceState_6796_ = lean_ctor_get(v___x_6795_, 4);
lean_inc_ref(v_traceState_6796_);
lean_dec(v___x_6795_);
v_traces_6797_ = lean_ctor_get(v_traceState_6796_, 0);
lean_inc_ref(v_traces_6797_);
lean_dec_ref(v_traceState_6796_);
v_ref_6798_ = l_Lean_replaceRef(v_ref_6772_, v_ref_6784_);
lean_inc_ref(v_inheritedTraceOptions_6794_);
lean_inc(v_cancelTk_x3f_6792_);
lean_inc(v_currMacroScope_6790_);
lean_inc(v_quotContext_6789_);
lean_inc(v_maxHeartbeats_6788_);
lean_inc(v_initHeartbeats_6787_);
lean_inc(v_openDecls_6786_);
lean_inc(v_currNamespace_6785_);
lean_inc(v_maxRecDepth_6783_);
lean_inc(v_currRecDepth_6782_);
lean_inc_ref(v_options_6781_);
lean_inc_ref(v_fileMap_6780_);
lean_inc_ref(v_fileName_6779_);
v___x_6799_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_6799_, 0, v_fileName_6779_);
lean_ctor_set(v___x_6799_, 1, v_fileMap_6780_);
lean_ctor_set(v___x_6799_, 2, v_options_6781_);
lean_ctor_set(v___x_6799_, 3, v_currRecDepth_6782_);
lean_ctor_set(v___x_6799_, 4, v_maxRecDepth_6783_);
lean_ctor_set(v___x_6799_, 5, v_ref_6798_);
lean_ctor_set(v___x_6799_, 6, v_currNamespace_6785_);
lean_ctor_set(v___x_6799_, 7, v_openDecls_6786_);
lean_ctor_set(v___x_6799_, 8, v_initHeartbeats_6787_);
lean_ctor_set(v___x_6799_, 9, v_maxHeartbeats_6788_);
lean_ctor_set(v___x_6799_, 10, v_quotContext_6789_);
lean_ctor_set(v___x_6799_, 11, v_currMacroScope_6790_);
lean_ctor_set(v___x_6799_, 12, v_cancelTk_x3f_6792_);
lean_ctor_set(v___x_6799_, 13, v_inheritedTraceOptions_6794_);
lean_ctor_set_uint8(v___x_6799_, sizeof(void*)*14, v_diag_6791_);
lean_ctor_set_uint8(v___x_6799_, sizeof(void*)*14 + 1, v_suppressElabErrors_6793_);
v___x_6800_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6797_);
lean_dec_ref(v_traces_6797_);
v_sz_6801_ = lean_array_size(v___x_6800_);
v___x_6802_ = ((size_t)0ULL);
v___x_6803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6801_, v___x_6802_, v___x_6800_);
v_msg_6804_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6804_, 0, v_data_6771_);
lean_ctor_set(v_msg_6804_, 1, v_msg_6773_);
lean_ctor_set(v_msg_6804_, 2, v___x_6803_);
v___x_6805_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6804_, v___y_6774_, v___y_6775_, v___x_6799_, v___y_6777_);
lean_dec_ref_known(v___x_6799_, 14);
v_a_6806_ = lean_ctor_get(v___x_6805_, 0);
v_isSharedCheck_6843_ = !lean_is_exclusive(v___x_6805_);
if (v_isSharedCheck_6843_ == 0)
{
v___x_6808_ = v___x_6805_;
v_isShared_6809_ = v_isSharedCheck_6843_;
goto v_resetjp_6807_;
}
else
{
lean_inc(v_a_6806_);
lean_dec(v___x_6805_);
v___x_6808_ = lean_box(0);
v_isShared_6809_ = v_isSharedCheck_6843_;
goto v_resetjp_6807_;
}
v_resetjp_6807_:
{
lean_object* v___x_6810_; lean_object* v_traceState_6811_; lean_object* v_env_6812_; lean_object* v_nextMacroScope_6813_; lean_object* v_ngen_6814_; lean_object* v_auxDeclNGen_6815_; lean_object* v_cache_6816_; lean_object* v_messages_6817_; lean_object* v_infoState_6818_; lean_object* v_snapshotTasks_6819_; lean_object* v___x_6821_; uint8_t v_isShared_6822_; uint8_t v_isSharedCheck_6842_; 
v___x_6810_ = lean_st_ref_take(v___y_6777_);
v_traceState_6811_ = lean_ctor_get(v___x_6810_, 4);
v_env_6812_ = lean_ctor_get(v___x_6810_, 0);
v_nextMacroScope_6813_ = lean_ctor_get(v___x_6810_, 1);
v_ngen_6814_ = lean_ctor_get(v___x_6810_, 2);
v_auxDeclNGen_6815_ = lean_ctor_get(v___x_6810_, 3);
v_cache_6816_ = lean_ctor_get(v___x_6810_, 5);
v_messages_6817_ = lean_ctor_get(v___x_6810_, 6);
v_infoState_6818_ = lean_ctor_get(v___x_6810_, 7);
v_snapshotTasks_6819_ = lean_ctor_get(v___x_6810_, 8);
v_isSharedCheck_6842_ = !lean_is_exclusive(v___x_6810_);
if (v_isSharedCheck_6842_ == 0)
{
v___x_6821_ = v___x_6810_;
v_isShared_6822_ = v_isSharedCheck_6842_;
goto v_resetjp_6820_;
}
else
{
lean_inc(v_snapshotTasks_6819_);
lean_inc(v_infoState_6818_);
lean_inc(v_messages_6817_);
lean_inc(v_cache_6816_);
lean_inc(v_traceState_6811_);
lean_inc(v_auxDeclNGen_6815_);
lean_inc(v_ngen_6814_);
lean_inc(v_nextMacroScope_6813_);
lean_inc(v_env_6812_);
lean_dec(v___x_6810_);
v___x_6821_ = lean_box(0);
v_isShared_6822_ = v_isSharedCheck_6842_;
goto v_resetjp_6820_;
}
v_resetjp_6820_:
{
uint64_t v_tid_6823_; lean_object* v___x_6825_; uint8_t v_isShared_6826_; uint8_t v_isSharedCheck_6840_; 
v_tid_6823_ = lean_ctor_get_uint64(v_traceState_6811_, sizeof(void*)*1);
v_isSharedCheck_6840_ = !lean_is_exclusive(v_traceState_6811_);
if (v_isSharedCheck_6840_ == 0)
{
lean_object* v_unused_6841_; 
v_unused_6841_ = lean_ctor_get(v_traceState_6811_, 0);
lean_dec(v_unused_6841_);
v___x_6825_ = v_traceState_6811_;
v_isShared_6826_ = v_isSharedCheck_6840_;
goto v_resetjp_6824_;
}
else
{
lean_dec(v_traceState_6811_);
v___x_6825_ = lean_box(0);
v_isShared_6826_ = v_isSharedCheck_6840_;
goto v_resetjp_6824_;
}
v_resetjp_6824_:
{
lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___x_6830_; 
v___x_6827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6827_, 0, v_ref_6772_);
lean_ctor_set(v___x_6827_, 1, v_a_6806_);
v___x_6828_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6770_, v___x_6827_);
if (v_isShared_6826_ == 0)
{
lean_ctor_set(v___x_6825_, 0, v___x_6828_);
v___x_6830_ = v___x_6825_;
goto v_reusejp_6829_;
}
else
{
lean_object* v_reuseFailAlloc_6839_; 
v_reuseFailAlloc_6839_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6839_, 0, v___x_6828_);
lean_ctor_set_uint64(v_reuseFailAlloc_6839_, sizeof(void*)*1, v_tid_6823_);
v___x_6830_ = v_reuseFailAlloc_6839_;
goto v_reusejp_6829_;
}
v_reusejp_6829_:
{
lean_object* v___x_6832_; 
if (v_isShared_6822_ == 0)
{
lean_ctor_set(v___x_6821_, 4, v___x_6830_);
v___x_6832_ = v___x_6821_;
goto v_reusejp_6831_;
}
else
{
lean_object* v_reuseFailAlloc_6838_; 
v_reuseFailAlloc_6838_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6838_, 0, v_env_6812_);
lean_ctor_set(v_reuseFailAlloc_6838_, 1, v_nextMacroScope_6813_);
lean_ctor_set(v_reuseFailAlloc_6838_, 2, v_ngen_6814_);
lean_ctor_set(v_reuseFailAlloc_6838_, 3, v_auxDeclNGen_6815_);
lean_ctor_set(v_reuseFailAlloc_6838_, 4, v___x_6830_);
lean_ctor_set(v_reuseFailAlloc_6838_, 5, v_cache_6816_);
lean_ctor_set(v_reuseFailAlloc_6838_, 6, v_messages_6817_);
lean_ctor_set(v_reuseFailAlloc_6838_, 7, v_infoState_6818_);
lean_ctor_set(v_reuseFailAlloc_6838_, 8, v_snapshotTasks_6819_);
v___x_6832_ = v_reuseFailAlloc_6838_;
goto v_reusejp_6831_;
}
v_reusejp_6831_:
{
lean_object* v___x_6833_; lean_object* v___x_6834_; lean_object* v___x_6836_; 
v___x_6833_ = lean_st_ref_put(v___y_6777_, v___x_6832_);
v___x_6834_ = lean_box(0);
if (v_isShared_6809_ == 0)
{
lean_ctor_set(v___x_6808_, 0, v___x_6834_);
v___x_6836_ = v___x_6808_;
goto v_reusejp_6835_;
}
else
{
lean_object* v_reuseFailAlloc_6837_; 
v_reuseFailAlloc_6837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6837_, 0, v___x_6834_);
v___x_6836_ = v_reuseFailAlloc_6837_;
goto v_reusejp_6835_;
}
v_reusejp_6835_:
{
return v___x_6836_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6844_, lean_object* v_data_6845_, lean_object* v_ref_6846_, lean_object* v_msg_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_, lean_object* v___y_6850_, lean_object* v___y_6851_, lean_object* v___y_6852_){
_start:
{
lean_object* v_res_6853_; 
v_res_6853_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6844_, v_data_6845_, v_ref_6846_, v_msg_6847_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_);
lean_dec(v___y_6851_);
lean_dec_ref(v___y_6850_);
lean_dec(v___y_6849_);
lean_dec_ref(v___y_6848_);
return v_res_6853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6854_, lean_object* v_opt_6855_){
_start:
{
lean_object* v_name_6856_; lean_object* v_defValue_6857_; lean_object* v_map_6858_; lean_object* v___x_6859_; 
v_name_6856_ = lean_ctor_get(v_opt_6855_, 0);
v_defValue_6857_ = lean_ctor_get(v_opt_6855_, 1);
v_map_6858_ = lean_ctor_get(v_opts_6854_, 0);
v___x_6859_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6858_, v_name_6856_);
if (lean_obj_tag(v___x_6859_) == 0)
{
lean_inc(v_defValue_6857_);
return v_defValue_6857_;
}
else
{
lean_object* v_val_6860_; 
v_val_6860_ = lean_ctor_get(v___x_6859_, 0);
lean_inc(v_val_6860_);
lean_dec_ref_known(v___x_6859_, 1);
if (lean_obj_tag(v_val_6860_) == 3)
{
lean_object* v_v_6861_; 
v_v_6861_ = lean_ctor_get(v_val_6860_, 0);
lean_inc(v_v_6861_);
lean_dec_ref_known(v_val_6860_, 1);
return v_v_6861_;
}
else
{
lean_dec(v_val_6860_);
lean_inc(v_defValue_6857_);
return v_defValue_6857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6862_, lean_object* v_opt_6863_){
_start:
{
lean_object* v_res_6864_; 
v_res_6864_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6862_, v_opt_6863_);
lean_dec_ref(v_opt_6863_);
lean_dec_ref(v_opts_6862_);
return v_res_6864_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6866_; lean_object* v___x_6867_; 
v___x_6866_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6867_ = l_Lean_stringToMessageData(v___x_6866_);
return v___x_6867_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6868_; double v___x_6869_; 
v___x_6868_ = lean_unsigned_to_nat(1000u);
v___x_6869_ = lean_float_of_nat(v___x_6868_);
return v___x_6869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6870_, uint8_t v_collapsed_6871_, lean_object* v_tag_6872_, lean_object* v_opts_6873_, uint8_t v_clsEnabled_6874_, lean_object* v_oldTraces_6875_, lean_object* v_msg_6876_, lean_object* v_resStartStop_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_, lean_object* v___y_6880_, lean_object* v___y_6881_, lean_object* v___y_6882_, lean_object* v___y_6883_, lean_object* v___y_6884_, lean_object* v___y_6885_, lean_object* v___y_6886_, lean_object* v___y_6887_, lean_object* v___y_6888_){
_start:
{
lean_object* v_fst_6890_; lean_object* v_snd_6891_; lean_object* v___y_6893_; lean_object* v___y_6894_; lean_object* v_data_6895_; lean_object* v_fst_6906_; lean_object* v_snd_6907_; lean_object* v___x_6908_; uint8_t v___x_6909_; lean_object* v___y_6911_; lean_object* v_a_6912_; uint8_t v___y_6927_; double v___y_6958_; 
v_fst_6890_ = lean_ctor_get(v_resStartStop_6877_, 0);
lean_inc(v_fst_6890_);
v_snd_6891_ = lean_ctor_get(v_resStartStop_6877_, 1);
lean_inc(v_snd_6891_);
lean_dec_ref(v_resStartStop_6877_);
v_fst_6906_ = lean_ctor_get(v_snd_6891_, 0);
lean_inc(v_fst_6906_);
v_snd_6907_ = lean_ctor_get(v_snd_6891_, 1);
lean_inc(v_snd_6907_);
lean_dec(v_snd_6891_);
v___x_6908_ = l_Lean_trace_profiler;
v___x_6909_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6873_, v___x_6908_);
if (v___x_6909_ == 0)
{
v___y_6927_ = v___x_6909_;
goto v___jp_6926_;
}
else
{
lean_object* v___x_6963_; uint8_t v___x_6964_; 
v___x_6963_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6964_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6873_, v___x_6963_);
if (v___x_6964_ == 0)
{
lean_object* v___x_6965_; lean_object* v___x_6966_; double v___x_6967_; double v___x_6968_; double v___x_6969_; 
v___x_6965_ = l_Lean_trace_profiler_threshold;
v___x_6966_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6873_, v___x_6965_);
v___x_6967_ = lean_float_of_nat(v___x_6966_);
v___x_6968_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6969_ = lean_float_div(v___x_6967_, v___x_6968_);
v___y_6958_ = v___x_6969_;
goto v___jp_6957_;
}
else
{
lean_object* v___x_6970_; lean_object* v___x_6971_; double v___x_6972_; 
v___x_6970_ = l_Lean_trace_profiler_threshold;
v___x_6971_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6873_, v___x_6970_);
v___x_6972_ = lean_float_of_nat(v___x_6971_);
v___y_6958_ = v___x_6972_;
goto v___jp_6957_;
}
}
v___jp_6892_:
{
lean_object* v___x_6896_; 
lean_inc(v___y_6893_);
v___x_6896_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6875_, v_data_6895_, v___y_6893_, v___y_6894_, v___y_6885_, v___y_6886_, v___y_6887_, v___y_6888_);
if (lean_obj_tag(v___x_6896_) == 0)
{
lean_object* v___x_6897_; 
lean_dec_ref_known(v___x_6896_, 1);
v___x_6897_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6890_);
return v___x_6897_;
}
else
{
lean_object* v_a_6898_; lean_object* v___x_6900_; uint8_t v_isShared_6901_; uint8_t v_isSharedCheck_6905_; 
lean_dec(v_fst_6890_);
v_a_6898_ = lean_ctor_get(v___x_6896_, 0);
v_isSharedCheck_6905_ = !lean_is_exclusive(v___x_6896_);
if (v_isSharedCheck_6905_ == 0)
{
v___x_6900_ = v___x_6896_;
v_isShared_6901_ = v_isSharedCheck_6905_;
goto v_resetjp_6899_;
}
else
{
lean_inc(v_a_6898_);
lean_dec(v___x_6896_);
v___x_6900_ = lean_box(0);
v_isShared_6901_ = v_isSharedCheck_6905_;
goto v_resetjp_6899_;
}
v_resetjp_6899_:
{
lean_object* v___x_6903_; 
if (v_isShared_6901_ == 0)
{
v___x_6903_ = v___x_6900_;
goto v_reusejp_6902_;
}
else
{
lean_object* v_reuseFailAlloc_6904_; 
v_reuseFailAlloc_6904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6904_, 0, v_a_6898_);
v___x_6903_ = v_reuseFailAlloc_6904_;
goto v_reusejp_6902_;
}
v_reusejp_6902_:
{
return v___x_6903_;
}
}
}
}
v___jp_6910_:
{
uint8_t v_result_6913_; lean_object* v___x_6914_; lean_object* v___x_6915_; double v___x_6916_; lean_object* v_data_6917_; 
v_result_6913_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6890_);
v___x_6914_ = lean_box(v_result_6913_);
v___x_6915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6915_, 0, v___x_6914_);
v___x_6916_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6872_);
lean_inc_ref(v___x_6915_);
lean_inc(v_cls_6870_);
v_data_6917_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6917_, 0, v_cls_6870_);
lean_ctor_set(v_data_6917_, 1, v___x_6915_);
lean_ctor_set(v_data_6917_, 2, v_tag_6872_);
lean_ctor_set_float(v_data_6917_, sizeof(void*)*3, v___x_6916_);
lean_ctor_set_float(v_data_6917_, sizeof(void*)*3 + 8, v___x_6916_);
lean_ctor_set_uint8(v_data_6917_, sizeof(void*)*3 + 16, v_collapsed_6871_);
if (v___x_6909_ == 0)
{
lean_dec_ref_known(v___x_6915_, 1);
lean_dec(v_snd_6907_);
lean_dec(v_fst_6906_);
lean_dec_ref(v_tag_6872_);
lean_dec(v_cls_6870_);
v___y_6893_ = v___y_6911_;
v___y_6894_ = v_a_6912_;
v_data_6895_ = v_data_6917_;
goto v___jp_6892_;
}
else
{
lean_object* v_data_6918_; double v___x_6919_; double v___x_6920_; 
lean_dec_ref_known(v_data_6917_, 3);
v_data_6918_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6918_, 0, v_cls_6870_);
lean_ctor_set(v_data_6918_, 1, v___x_6915_);
lean_ctor_set(v_data_6918_, 2, v_tag_6872_);
v___x_6919_ = lean_unbox_float(v_fst_6906_);
lean_dec(v_fst_6906_);
lean_ctor_set_float(v_data_6918_, sizeof(void*)*3, v___x_6919_);
v___x_6920_ = lean_unbox_float(v_snd_6907_);
lean_dec(v_snd_6907_);
lean_ctor_set_float(v_data_6918_, sizeof(void*)*3 + 8, v___x_6920_);
lean_ctor_set_uint8(v_data_6918_, sizeof(void*)*3 + 16, v_collapsed_6871_);
v___y_6893_ = v___y_6911_;
v___y_6894_ = v_a_6912_;
v_data_6895_ = v_data_6918_;
goto v___jp_6892_;
}
}
v___jp_6921_:
{
lean_object* v_ref_6922_; lean_object* v___x_6923_; 
v_ref_6922_ = lean_ctor_get(v___y_6887_, 5);
lean_inc(v___y_6888_);
lean_inc_ref(v___y_6887_);
lean_inc(v___y_6886_);
lean_inc_ref(v___y_6885_);
lean_inc(v___y_6884_);
lean_inc_ref(v___y_6883_);
lean_inc(v___y_6882_);
lean_inc_ref(v___y_6881_);
lean_inc(v___y_6880_);
lean_inc(v___y_6879_);
lean_inc_ref(v___y_6878_);
lean_inc(v_fst_6890_);
v___x_6923_ = lean_apply_13(v_msg_6876_, v_fst_6890_, v___y_6878_, v___y_6879_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_, v___y_6888_, lean_box(0));
if (lean_obj_tag(v___x_6923_) == 0)
{
lean_object* v_a_6924_; 
v_a_6924_ = lean_ctor_get(v___x_6923_, 0);
lean_inc(v_a_6924_);
lean_dec_ref_known(v___x_6923_, 1);
v___y_6911_ = v_ref_6922_;
v_a_6912_ = v_a_6924_;
goto v___jp_6910_;
}
else
{
lean_object* v___x_6925_; 
lean_dec_ref_known(v___x_6923_, 1);
v___x_6925_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6911_ = v_ref_6922_;
v_a_6912_ = v___x_6925_;
goto v___jp_6910_;
}
}
v___jp_6926_:
{
if (v_clsEnabled_6874_ == 0)
{
if (v___y_6927_ == 0)
{
lean_object* v___x_6928_; lean_object* v_traceState_6929_; lean_object* v_env_6930_; lean_object* v_nextMacroScope_6931_; lean_object* v_ngen_6932_; lean_object* v_auxDeclNGen_6933_; lean_object* v_cache_6934_; lean_object* v_messages_6935_; lean_object* v_infoState_6936_; lean_object* v_snapshotTasks_6937_; lean_object* v___x_6939_; uint8_t v_isShared_6940_; uint8_t v_isSharedCheck_6956_; 
lean_dec(v_snd_6907_);
lean_dec(v_fst_6906_);
lean_dec_ref(v_msg_6876_);
lean_dec_ref(v_tag_6872_);
lean_dec(v_cls_6870_);
v___x_6928_ = lean_st_ref_take(v___y_6888_);
v_traceState_6929_ = lean_ctor_get(v___x_6928_, 4);
v_env_6930_ = lean_ctor_get(v___x_6928_, 0);
v_nextMacroScope_6931_ = lean_ctor_get(v___x_6928_, 1);
v_ngen_6932_ = lean_ctor_get(v___x_6928_, 2);
v_auxDeclNGen_6933_ = lean_ctor_get(v___x_6928_, 3);
v_cache_6934_ = lean_ctor_get(v___x_6928_, 5);
v_messages_6935_ = lean_ctor_get(v___x_6928_, 6);
v_infoState_6936_ = lean_ctor_get(v___x_6928_, 7);
v_snapshotTasks_6937_ = lean_ctor_get(v___x_6928_, 8);
v_isSharedCheck_6956_ = !lean_is_exclusive(v___x_6928_);
if (v_isSharedCheck_6956_ == 0)
{
v___x_6939_ = v___x_6928_;
v_isShared_6940_ = v_isSharedCheck_6956_;
goto v_resetjp_6938_;
}
else
{
lean_inc(v_snapshotTasks_6937_);
lean_inc(v_infoState_6936_);
lean_inc(v_messages_6935_);
lean_inc(v_cache_6934_);
lean_inc(v_traceState_6929_);
lean_inc(v_auxDeclNGen_6933_);
lean_inc(v_ngen_6932_);
lean_inc(v_nextMacroScope_6931_);
lean_inc(v_env_6930_);
lean_dec(v___x_6928_);
v___x_6939_ = lean_box(0);
v_isShared_6940_ = v_isSharedCheck_6956_;
goto v_resetjp_6938_;
}
v_resetjp_6938_:
{
uint64_t v_tid_6941_; lean_object* v_traces_6942_; lean_object* v___x_6944_; uint8_t v_isShared_6945_; uint8_t v_isSharedCheck_6955_; 
v_tid_6941_ = lean_ctor_get_uint64(v_traceState_6929_, sizeof(void*)*1);
v_traces_6942_ = lean_ctor_get(v_traceState_6929_, 0);
v_isSharedCheck_6955_ = !lean_is_exclusive(v_traceState_6929_);
if (v_isSharedCheck_6955_ == 0)
{
v___x_6944_ = v_traceState_6929_;
v_isShared_6945_ = v_isSharedCheck_6955_;
goto v_resetjp_6943_;
}
else
{
lean_inc(v_traces_6942_);
lean_dec(v_traceState_6929_);
v___x_6944_ = lean_box(0);
v_isShared_6945_ = v_isSharedCheck_6955_;
goto v_resetjp_6943_;
}
v_resetjp_6943_:
{
lean_object* v___x_6946_; lean_object* v___x_6948_; 
v___x_6946_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6875_, v_traces_6942_);
lean_dec_ref(v_traces_6942_);
if (v_isShared_6945_ == 0)
{
lean_ctor_set(v___x_6944_, 0, v___x_6946_);
v___x_6948_ = v___x_6944_;
goto v_reusejp_6947_;
}
else
{
lean_object* v_reuseFailAlloc_6954_; 
v_reuseFailAlloc_6954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6954_, 0, v___x_6946_);
lean_ctor_set_uint64(v_reuseFailAlloc_6954_, sizeof(void*)*1, v_tid_6941_);
v___x_6948_ = v_reuseFailAlloc_6954_;
goto v_reusejp_6947_;
}
v_reusejp_6947_:
{
lean_object* v___x_6950_; 
if (v_isShared_6940_ == 0)
{
lean_ctor_set(v___x_6939_, 4, v___x_6948_);
v___x_6950_ = v___x_6939_;
goto v_reusejp_6949_;
}
else
{
lean_object* v_reuseFailAlloc_6953_; 
v_reuseFailAlloc_6953_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6953_, 0, v_env_6930_);
lean_ctor_set(v_reuseFailAlloc_6953_, 1, v_nextMacroScope_6931_);
lean_ctor_set(v_reuseFailAlloc_6953_, 2, v_ngen_6932_);
lean_ctor_set(v_reuseFailAlloc_6953_, 3, v_auxDeclNGen_6933_);
lean_ctor_set(v_reuseFailAlloc_6953_, 4, v___x_6948_);
lean_ctor_set(v_reuseFailAlloc_6953_, 5, v_cache_6934_);
lean_ctor_set(v_reuseFailAlloc_6953_, 6, v_messages_6935_);
lean_ctor_set(v_reuseFailAlloc_6953_, 7, v_infoState_6936_);
lean_ctor_set(v_reuseFailAlloc_6953_, 8, v_snapshotTasks_6937_);
v___x_6950_ = v_reuseFailAlloc_6953_;
goto v_reusejp_6949_;
}
v_reusejp_6949_:
{
lean_object* v___x_6951_; lean_object* v___x_6952_; 
v___x_6951_ = lean_st_ref_put(v___y_6888_, v___x_6950_);
v___x_6952_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6890_);
return v___x_6952_;
}
}
}
}
}
else
{
goto v___jp_6921_;
}
}
else
{
goto v___jp_6921_;
}
}
v___jp_6957_:
{
double v___x_6959_; double v___x_6960_; double v___x_6961_; uint8_t v___x_6962_; 
v___x_6959_ = lean_unbox_float(v_snd_6907_);
v___x_6960_ = lean_unbox_float(v_fst_6906_);
v___x_6961_ = lean_float_sub(v___x_6959_, v___x_6960_);
v___x_6962_ = lean_float_decLt(v___y_6958_, v___x_6961_);
v___y_6927_ = v___x_6962_;
goto v___jp_6926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6973_ = _args[0];
lean_object* v_collapsed_6974_ = _args[1];
lean_object* v_tag_6975_ = _args[2];
lean_object* v_opts_6976_ = _args[3];
lean_object* v_clsEnabled_6977_ = _args[4];
lean_object* v_oldTraces_6978_ = _args[5];
lean_object* v_msg_6979_ = _args[6];
lean_object* v_resStartStop_6980_ = _args[7];
lean_object* v___y_6981_ = _args[8];
lean_object* v___y_6982_ = _args[9];
lean_object* v___y_6983_ = _args[10];
lean_object* v___y_6984_ = _args[11];
lean_object* v___y_6985_ = _args[12];
lean_object* v___y_6986_ = _args[13];
lean_object* v___y_6987_ = _args[14];
lean_object* v___y_6988_ = _args[15];
lean_object* v___y_6989_ = _args[16];
lean_object* v___y_6990_ = _args[17];
lean_object* v___y_6991_ = _args[18];
lean_object* v___y_6992_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6993_; uint8_t v_clsEnabled_boxed_6994_; lean_object* v_res_6995_; 
v_collapsed_boxed_6993_ = lean_unbox(v_collapsed_6974_);
v_clsEnabled_boxed_6994_ = lean_unbox(v_clsEnabled_6977_);
v_res_6995_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6973_, v_collapsed_boxed_6993_, v_tag_6975_, v_opts_6976_, v_clsEnabled_boxed_6994_, v_oldTraces_6978_, v_msg_6979_, v_resStartStop_6980_, v___y_6981_, v___y_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_, v___y_6988_, v___y_6989_, v___y_6990_, v___y_6991_);
lean_dec(v___y_6991_);
lean_dec_ref(v___y_6990_);
lean_dec(v___y_6989_);
lean_dec_ref(v___y_6988_);
lean_dec(v___y_6987_);
lean_dec_ref(v___y_6986_);
lean_dec(v___y_6985_);
lean_dec_ref(v___y_6984_);
lean_dec(v___y_6983_);
lean_dec(v___y_6982_);
lean_dec_ref(v___y_6981_);
lean_dec_ref(v_opts_6976_);
return v_res_6995_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_7000_; lean_object* v___x_7001_; 
v___x_7000_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_7001_ = l_Lean_stringToMessageData(v___x_7000_);
return v___x_7001_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_7002_, lean_object* v_b_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_, lean_object* v___y_7008_, lean_object* v___y_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_){
_start:
{
if (lean_obj_tag(v_as_x27_7002_) == 0)
{
lean_object* v___x_7016_; 
v___x_7016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7016_, 0, v_b_7003_);
return v___x_7016_;
}
else
{
lean_object* v_head_7017_; lean_object* v_options_7018_; lean_object* v_tail_7019_; lean_object* v_name_7020_; lean_object* v_run_x27_7021_; lean_object* v_inheritedTraceOptions_7022_; uint8_t v_hasTrace_7023_; lean_object* v___x_7024_; uint8_t v___y_7026_; lean_object* v___x_7031_; lean_object* v___y_7033_; 
lean_dec_ref(v_b_7003_);
v_head_7017_ = lean_ctor_get(v_as_x27_7002_, 0);
v_options_7018_ = lean_ctor_get(v___y_7013_, 2);
v_tail_7019_ = lean_ctor_get(v_as_x27_7002_, 1);
v_name_7020_ = lean_ctor_get(v_head_7017_, 0);
v_run_x27_7021_ = lean_ctor_get(v_head_7017_, 1);
v_inheritedTraceOptions_7022_ = lean_ctor_get(v___y_7013_, 13);
v_hasTrace_7023_ = lean_ctor_get_uint8(v_options_7018_, sizeof(void*)*1);
v___x_7024_ = lean_box(0);
v___x_7031_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_7023_ == 0)
{
lean_object* v___x_7061_; 
lean_inc_ref(v_run_x27_7021_);
lean_inc(v___y_7014_);
lean_inc_ref(v___y_7013_);
lean_inc(v___y_7012_);
lean_inc_ref(v___y_7011_);
lean_inc(v___y_7010_);
lean_inc_ref(v___y_7009_);
lean_inc(v___y_7008_);
lean_inc_ref(v___y_7007_);
lean_inc(v___y_7006_);
lean_inc(v___y_7005_);
lean_inc_ref(v___y_7004_);
v___x_7061_ = lean_apply_12(v_run_x27_7021_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_, lean_box(0));
v___y_7033_ = v___x_7061_;
goto v___jp_7032_;
}
else
{
lean_object* v___f_7062_; lean_object* v___x_7063_; lean_object* v___x_7064_; lean_object* v___x_7065_; uint8_t v___x_7066_; lean_object* v___y_7068_; lean_object* v___y_7069_; lean_object* v_a_7070_; lean_object* v___y_7083_; lean_object* v___y_7084_; lean_object* v_a_7085_; 
lean_inc(v_name_7020_);
v___f_7062_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_7062_, 0, v_name_7020_);
v___x_7063_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_7064_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_7065_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_7066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7022_, v_options_7018_, v___x_7065_);
if (v___x_7066_ == 0)
{
lean_object* v___x_7135_; uint8_t v___x_7136_; 
v___x_7135_ = l_Lean_trace_profiler;
v___x_7136_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_7018_, v___x_7135_);
if (v___x_7136_ == 0)
{
lean_object* v___x_7137_; 
lean_dec_ref(v___f_7062_);
lean_inc_ref(v_run_x27_7021_);
lean_inc(v___y_7014_);
lean_inc_ref(v___y_7013_);
lean_inc(v___y_7012_);
lean_inc_ref(v___y_7011_);
lean_inc(v___y_7010_);
lean_inc_ref(v___y_7009_);
lean_inc(v___y_7008_);
lean_inc_ref(v___y_7007_);
lean_inc(v___y_7006_);
lean_inc(v___y_7005_);
lean_inc_ref(v___y_7004_);
v___x_7137_ = lean_apply_12(v_run_x27_7021_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_, lean_box(0));
v___y_7033_ = v___x_7137_;
goto v___jp_7032_;
}
else
{
goto v___jp_7094_;
}
}
else
{
goto v___jp_7094_;
}
v___jp_7067_:
{
lean_object* v___x_7071_; double v___x_7072_; double v___x_7073_; double v___x_7074_; double v___x_7075_; double v___x_7076_; lean_object* v___x_7077_; lean_object* v___x_7078_; lean_object* v___x_7079_; lean_object* v___x_7080_; lean_object* v___x_7081_; 
v___x_7071_ = lean_io_mono_nanos_now();
v___x_7072_ = lean_float_of_nat(v___y_7068_);
v___x_7073_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_7074_ = lean_float_div(v___x_7072_, v___x_7073_);
v___x_7075_ = lean_float_of_nat(v___x_7071_);
v___x_7076_ = lean_float_div(v___x_7075_, v___x_7073_);
v___x_7077_ = lean_box_float(v___x_7074_);
v___x_7078_ = lean_box_float(v___x_7076_);
v___x_7079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7079_, 0, v___x_7077_);
lean_ctor_set(v___x_7079_, 1, v___x_7078_);
v___x_7080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7080_, 0, v_a_7070_);
lean_ctor_set(v___x_7080_, 1, v___x_7079_);
v___x_7081_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_7063_, v_hasTrace_7023_, v___x_7064_, v_options_7018_, v___x_7066_, v___y_7069_, v___f_7062_, v___x_7080_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_);
v___y_7033_ = v___x_7081_;
goto v___jp_7032_;
}
v___jp_7082_:
{
lean_object* v___x_7086_; double v___x_7087_; double v___x_7088_; lean_object* v___x_7089_; lean_object* v___x_7090_; lean_object* v___x_7091_; lean_object* v___x_7092_; lean_object* v___x_7093_; 
v___x_7086_ = lean_io_get_num_heartbeats();
v___x_7087_ = lean_float_of_nat(v___y_7083_);
v___x_7088_ = lean_float_of_nat(v___x_7086_);
v___x_7089_ = lean_box_float(v___x_7087_);
v___x_7090_ = lean_box_float(v___x_7088_);
v___x_7091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7091_, 0, v___x_7089_);
lean_ctor_set(v___x_7091_, 1, v___x_7090_);
v___x_7092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7092_, 0, v_a_7085_);
lean_ctor_set(v___x_7092_, 1, v___x_7091_);
v___x_7093_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_7063_, v_hasTrace_7023_, v___x_7064_, v_options_7018_, v___x_7066_, v___y_7084_, v___f_7062_, v___x_7092_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_);
v___y_7033_ = v___x_7093_;
goto v___jp_7032_;
}
v___jp_7094_:
{
lean_object* v___x_7095_; lean_object* v_a_7096_; lean_object* v___x_7097_; uint8_t v___x_7098_; 
v___x_7095_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_7014_);
v_a_7096_ = lean_ctor_get(v___x_7095_, 0);
lean_inc(v_a_7096_);
lean_dec_ref(v___x_7095_);
v___x_7097_ = l_Lean_trace_profiler_useHeartbeats;
v___x_7098_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_7018_, v___x_7097_);
if (v___x_7098_ == 0)
{
lean_object* v___x_7099_; lean_object* v___x_7100_; 
v___x_7099_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_7021_);
lean_inc(v___y_7014_);
lean_inc_ref(v___y_7013_);
lean_inc(v___y_7012_);
lean_inc_ref(v___y_7011_);
lean_inc(v___y_7010_);
lean_inc_ref(v___y_7009_);
lean_inc(v___y_7008_);
lean_inc_ref(v___y_7007_);
lean_inc(v___y_7006_);
lean_inc(v___y_7005_);
lean_inc_ref(v___y_7004_);
v___x_7100_ = lean_apply_12(v_run_x27_7021_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_, lean_box(0));
if (lean_obj_tag(v___x_7100_) == 0)
{
lean_object* v_a_7101_; lean_object* v___x_7103_; uint8_t v_isShared_7104_; uint8_t v_isSharedCheck_7108_; 
v_a_7101_ = lean_ctor_get(v___x_7100_, 0);
v_isSharedCheck_7108_ = !lean_is_exclusive(v___x_7100_);
if (v_isSharedCheck_7108_ == 0)
{
v___x_7103_ = v___x_7100_;
v_isShared_7104_ = v_isSharedCheck_7108_;
goto v_resetjp_7102_;
}
else
{
lean_inc(v_a_7101_);
lean_dec(v___x_7100_);
v___x_7103_ = lean_box(0);
v_isShared_7104_ = v_isSharedCheck_7108_;
goto v_resetjp_7102_;
}
v_resetjp_7102_:
{
lean_object* v___x_7106_; 
if (v_isShared_7104_ == 0)
{
lean_ctor_set_tag(v___x_7103_, 1);
v___x_7106_ = v___x_7103_;
goto v_reusejp_7105_;
}
else
{
lean_object* v_reuseFailAlloc_7107_; 
v_reuseFailAlloc_7107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7107_, 0, v_a_7101_);
v___x_7106_ = v_reuseFailAlloc_7107_;
goto v_reusejp_7105_;
}
v_reusejp_7105_:
{
v___y_7068_ = v___x_7099_;
v___y_7069_ = v_a_7096_;
v_a_7070_ = v___x_7106_;
goto v___jp_7067_;
}
}
}
else
{
lean_object* v_a_7109_; lean_object* v___x_7111_; uint8_t v_isShared_7112_; uint8_t v_isSharedCheck_7116_; 
v_a_7109_ = lean_ctor_get(v___x_7100_, 0);
v_isSharedCheck_7116_ = !lean_is_exclusive(v___x_7100_);
if (v_isSharedCheck_7116_ == 0)
{
v___x_7111_ = v___x_7100_;
v_isShared_7112_ = v_isSharedCheck_7116_;
goto v_resetjp_7110_;
}
else
{
lean_inc(v_a_7109_);
lean_dec(v___x_7100_);
v___x_7111_ = lean_box(0);
v_isShared_7112_ = v_isSharedCheck_7116_;
goto v_resetjp_7110_;
}
v_resetjp_7110_:
{
lean_object* v___x_7114_; 
if (v_isShared_7112_ == 0)
{
lean_ctor_set_tag(v___x_7111_, 0);
v___x_7114_ = v___x_7111_;
goto v_reusejp_7113_;
}
else
{
lean_object* v_reuseFailAlloc_7115_; 
v_reuseFailAlloc_7115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7115_, 0, v_a_7109_);
v___x_7114_ = v_reuseFailAlloc_7115_;
goto v_reusejp_7113_;
}
v_reusejp_7113_:
{
v___y_7068_ = v___x_7099_;
v___y_7069_ = v_a_7096_;
v_a_7070_ = v___x_7114_;
goto v___jp_7067_;
}
}
}
}
else
{
lean_object* v___x_7117_; lean_object* v___x_7118_; 
v___x_7117_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_7021_);
lean_inc(v___y_7014_);
lean_inc_ref(v___y_7013_);
lean_inc(v___y_7012_);
lean_inc_ref(v___y_7011_);
lean_inc(v___y_7010_);
lean_inc_ref(v___y_7009_);
lean_inc(v___y_7008_);
lean_inc_ref(v___y_7007_);
lean_inc(v___y_7006_);
lean_inc(v___y_7005_);
lean_inc_ref(v___y_7004_);
v___x_7118_ = lean_apply_12(v_run_x27_7021_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_, lean_box(0));
if (lean_obj_tag(v___x_7118_) == 0)
{
lean_object* v_a_7119_; lean_object* v___x_7121_; uint8_t v_isShared_7122_; uint8_t v_isSharedCheck_7126_; 
v_a_7119_ = lean_ctor_get(v___x_7118_, 0);
v_isSharedCheck_7126_ = !lean_is_exclusive(v___x_7118_);
if (v_isSharedCheck_7126_ == 0)
{
v___x_7121_ = v___x_7118_;
v_isShared_7122_ = v_isSharedCheck_7126_;
goto v_resetjp_7120_;
}
else
{
lean_inc(v_a_7119_);
lean_dec(v___x_7118_);
v___x_7121_ = lean_box(0);
v_isShared_7122_ = v_isSharedCheck_7126_;
goto v_resetjp_7120_;
}
v_resetjp_7120_:
{
lean_object* v___x_7124_; 
if (v_isShared_7122_ == 0)
{
lean_ctor_set_tag(v___x_7121_, 1);
v___x_7124_ = v___x_7121_;
goto v_reusejp_7123_;
}
else
{
lean_object* v_reuseFailAlloc_7125_; 
v_reuseFailAlloc_7125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7125_, 0, v_a_7119_);
v___x_7124_ = v_reuseFailAlloc_7125_;
goto v_reusejp_7123_;
}
v_reusejp_7123_:
{
v___y_7083_ = v___x_7117_;
v___y_7084_ = v_a_7096_;
v_a_7085_ = v___x_7124_;
goto v___jp_7082_;
}
}
}
else
{
lean_object* v_a_7127_; lean_object* v___x_7129_; uint8_t v_isShared_7130_; uint8_t v_isSharedCheck_7134_; 
v_a_7127_ = lean_ctor_get(v___x_7118_, 0);
v_isSharedCheck_7134_ = !lean_is_exclusive(v___x_7118_);
if (v_isSharedCheck_7134_ == 0)
{
v___x_7129_ = v___x_7118_;
v_isShared_7130_ = v_isSharedCheck_7134_;
goto v_resetjp_7128_;
}
else
{
lean_inc(v_a_7127_);
lean_dec(v___x_7118_);
v___x_7129_ = lean_box(0);
v_isShared_7130_ = v_isSharedCheck_7134_;
goto v_resetjp_7128_;
}
v_resetjp_7128_:
{
lean_object* v___x_7132_; 
if (v_isShared_7130_ == 0)
{
lean_ctor_set_tag(v___x_7129_, 0);
v___x_7132_ = v___x_7129_;
goto v_reusejp_7131_;
}
else
{
lean_object* v_reuseFailAlloc_7133_; 
v_reuseFailAlloc_7133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7133_, 0, v_a_7127_);
v___x_7132_ = v_reuseFailAlloc_7133_;
goto v_reusejp_7131_;
}
v_reusejp_7131_:
{
v___y_7083_ = v___x_7117_;
v___y_7084_ = v_a_7096_;
v_a_7085_ = v___x_7132_;
goto v___jp_7082_;
}
}
}
}
}
}
v___jp_7025_:
{
lean_object* v___x_7027_; lean_object* v___x_7028_; lean_object* v___x_7029_; lean_object* v___x_7030_; 
v___x_7027_ = lean_box(v___y_7026_);
v___x_7028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7028_, 0, v___x_7027_);
v___x_7029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7029_, 0, v___x_7028_);
lean_ctor_set(v___x_7029_, 1, v___x_7024_);
v___x_7030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7030_, 0, v___x_7029_);
return v___x_7030_;
}
v___jp_7032_:
{
if (lean_obj_tag(v___y_7033_) == 0)
{
lean_object* v_a_7034_; uint8_t v___x_7035_; 
v_a_7034_ = lean_ctor_get(v___y_7033_, 0);
lean_inc(v_a_7034_);
lean_dec_ref_known(v___y_7033_, 1);
v___x_7035_ = lean_unbox(v_a_7034_);
if (v___x_7035_ == 0)
{
lean_dec(v_a_7034_);
v_as_x27_7002_ = v_tail_7019_;
v_b_7003_ = v___x_7031_;
goto _start;
}
else
{
if (v_hasTrace_7023_ == 0)
{
uint8_t v___x_7037_; 
v___x_7037_ = lean_unbox(v_a_7034_);
lean_dec(v_a_7034_);
v___y_7026_ = v___x_7037_;
goto v___jp_7025_;
}
else
{
lean_object* v___x_7038_; lean_object* v___x_7039_; uint8_t v___x_7040_; 
v___x_7038_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_7039_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_7040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7022_, v_options_7018_, v___x_7039_);
if (v___x_7040_ == 0)
{
uint8_t v___x_7041_; 
v___x_7041_ = lean_unbox(v_a_7034_);
lean_dec(v_a_7034_);
v___y_7026_ = v___x_7041_;
goto v___jp_7025_;
}
else
{
lean_object* v___x_7042_; lean_object* v___x_7043_; 
v___x_7042_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_7043_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_7038_, v___x_7042_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_);
if (lean_obj_tag(v___x_7043_) == 0)
{
uint8_t v___x_7044_; 
lean_dec_ref_known(v___x_7043_, 1);
v___x_7044_ = lean_unbox(v_a_7034_);
lean_dec(v_a_7034_);
v___y_7026_ = v___x_7044_;
goto v___jp_7025_;
}
else
{
lean_object* v_a_7045_; lean_object* v___x_7047_; uint8_t v_isShared_7048_; uint8_t v_isSharedCheck_7052_; 
lean_dec(v_a_7034_);
v_a_7045_ = lean_ctor_get(v___x_7043_, 0);
v_isSharedCheck_7052_ = !lean_is_exclusive(v___x_7043_);
if (v_isSharedCheck_7052_ == 0)
{
v___x_7047_ = v___x_7043_;
v_isShared_7048_ = v_isSharedCheck_7052_;
goto v_resetjp_7046_;
}
else
{
lean_inc(v_a_7045_);
lean_dec(v___x_7043_);
v___x_7047_ = lean_box(0);
v_isShared_7048_ = v_isSharedCheck_7052_;
goto v_resetjp_7046_;
}
v_resetjp_7046_:
{
lean_object* v___x_7050_; 
if (v_isShared_7048_ == 0)
{
v___x_7050_ = v___x_7047_;
goto v_reusejp_7049_;
}
else
{
lean_object* v_reuseFailAlloc_7051_; 
v_reuseFailAlloc_7051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7051_, 0, v_a_7045_);
v___x_7050_ = v_reuseFailAlloc_7051_;
goto v_reusejp_7049_;
}
v_reusejp_7049_:
{
return v___x_7050_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_7053_; lean_object* v___x_7055_; uint8_t v_isShared_7056_; uint8_t v_isSharedCheck_7060_; 
v_a_7053_ = lean_ctor_get(v___y_7033_, 0);
v_isSharedCheck_7060_ = !lean_is_exclusive(v___y_7033_);
if (v_isSharedCheck_7060_ == 0)
{
v___x_7055_ = v___y_7033_;
v_isShared_7056_ = v_isSharedCheck_7060_;
goto v_resetjp_7054_;
}
else
{
lean_inc(v_a_7053_);
lean_dec(v___y_7033_);
v___x_7055_ = lean_box(0);
v_isShared_7056_ = v_isSharedCheck_7060_;
goto v_resetjp_7054_;
}
v_resetjp_7054_:
{
lean_object* v___x_7058_; 
if (v_isShared_7056_ == 0)
{
v___x_7058_ = v___x_7055_;
goto v_reusejp_7057_;
}
else
{
lean_object* v_reuseFailAlloc_7059_; 
v_reuseFailAlloc_7059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7059_, 0, v_a_7053_);
v___x_7058_ = v_reuseFailAlloc_7059_;
goto v_reusejp_7057_;
}
v_reusejp_7057_:
{
return v___x_7058_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_7138_, lean_object* v_b_7139_, lean_object* v___y_7140_, lean_object* v___y_7141_, lean_object* v___y_7142_, lean_object* v___y_7143_, lean_object* v___y_7144_, lean_object* v___y_7145_, lean_object* v___y_7146_, lean_object* v___y_7147_, lean_object* v___y_7148_, lean_object* v___y_7149_, lean_object* v___y_7150_, lean_object* v___y_7151_){
_start:
{
lean_object* v_res_7152_; 
v_res_7152_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_7138_, v_b_7139_, v___y_7140_, v___y_7141_, v___y_7142_, v___y_7143_, v___y_7144_, v___y_7145_, v___y_7146_, v___y_7147_, v___y_7148_, v___y_7149_, v___y_7150_);
lean_dec(v___y_7150_);
lean_dec_ref(v___y_7149_);
lean_dec(v___y_7148_);
lean_dec_ref(v___y_7147_);
lean_dec(v___y_7146_);
lean_dec_ref(v___y_7145_);
lean_dec(v___y_7144_);
lean_dec_ref(v___y_7143_);
lean_dec(v___y_7142_);
lean_dec(v___y_7141_);
lean_dec_ref(v___y_7140_);
lean_dec(v_as_x27_7138_);
return v_res_7152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_7155_; lean_object* v___x_7156_; 
v___x_7155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_7156_ = l_Lean_stringToMessageData(v___x_7155_);
return v___x_7156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_7158_; lean_object* v___x_7159_; 
v___x_7158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_7159_ = l_Lean_stringToMessageData(v___x_7158_);
return v___x_7159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_7160_, lean_object* v_a_7161_, lean_object* v_a_7162_, lean_object* v_a_7163_, lean_object* v_a_7164_, lean_object* v_a_7165_, lean_object* v_a_7166_, lean_object* v_a_7167_, lean_object* v_a_7168_, lean_object* v_a_7169_, lean_object* v_a_7170_, lean_object* v_a_7171_){
_start:
{
lean_object* v___x_7173_; lean_object* v___x_7174_; 
v___x_7173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_7174_ = l_Lean_Core_checkSystem(v___x_7173_, v_a_7170_, v_a_7171_);
if (lean_obj_tag(v___x_7174_) == 0)
{
lean_object* v___x_7175_; lean_object* v_caches_7176_; lean_object* v_typeAnalysis_7177_; lean_object* v_target_7178_; lean_object* v_hypotheses_7179_; lean_object* v___x_7181_; uint8_t v_isShared_7182_; uint8_t v_isSharedCheck_7262_; 
lean_dec_ref_known(v___x_7174_, 1);
v___x_7175_ = lean_st_ref_take(v_a_7162_);
v_caches_7176_ = lean_ctor_get(v___x_7175_, 0);
v_typeAnalysis_7177_ = lean_ctor_get(v___x_7175_, 1);
v_target_7178_ = lean_ctor_get(v___x_7175_, 2);
v_hypotheses_7179_ = lean_ctor_get(v___x_7175_, 3);
v_isSharedCheck_7262_ = !lean_is_exclusive(v___x_7175_);
if (v_isSharedCheck_7262_ == 0)
{
v___x_7181_ = v___x_7175_;
v_isShared_7182_ = v_isSharedCheck_7262_;
goto v_resetjp_7180_;
}
else
{
lean_inc(v_hypotheses_7179_);
lean_inc(v_target_7178_);
lean_inc(v_typeAnalysis_7177_);
lean_inc(v_caches_7176_);
lean_dec(v___x_7175_);
v___x_7181_ = lean_box(0);
v_isShared_7182_ = v_isSharedCheck_7262_;
goto v_resetjp_7180_;
}
v_resetjp_7180_:
{
uint8_t v___x_7183_; lean_object* v___x_7185_; 
v___x_7183_ = 0;
if (v_isShared_7182_ == 0)
{
v___x_7185_ = v___x_7181_;
goto v_reusejp_7184_;
}
else
{
lean_object* v_reuseFailAlloc_7261_; 
v_reuseFailAlloc_7261_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_7261_, 0, v_caches_7176_);
lean_ctor_set(v_reuseFailAlloc_7261_, 1, v_typeAnalysis_7177_);
lean_ctor_set(v_reuseFailAlloc_7261_, 2, v_target_7178_);
lean_ctor_set(v_reuseFailAlloc_7261_, 3, v_hypotheses_7179_);
v___x_7185_ = v_reuseFailAlloc_7261_;
goto v_reusejp_7184_;
}
v_reusejp_7184_:
{
lean_object* v___x_7186_; lean_object* v___x_7187_; lean_object* v___x_7188_; 
lean_ctor_set_uint8(v___x_7185_, sizeof(void*)*4, v___x_7183_);
v___x_7186_ = lean_st_ref_put(v_a_7162_, v___x_7185_);
v___x_7187_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_7188_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_7160_, v___x_7187_, v_a_7161_, v_a_7162_, v_a_7163_, v_a_7164_, v_a_7165_, v_a_7166_, v_a_7167_, v_a_7168_, v_a_7169_, v_a_7170_, v_a_7171_);
if (lean_obj_tag(v___x_7188_) == 0)
{
lean_object* v_a_7189_; lean_object* v___x_7191_; uint8_t v_isShared_7192_; uint8_t v_isSharedCheck_7252_; 
v_a_7189_ = lean_ctor_get(v___x_7188_, 0);
v_isSharedCheck_7252_ = !lean_is_exclusive(v___x_7188_);
if (v_isSharedCheck_7252_ == 0)
{
v___x_7191_ = v___x_7188_;
v_isShared_7192_ = v_isSharedCheck_7252_;
goto v_resetjp_7190_;
}
else
{
lean_inc(v_a_7189_);
lean_dec(v___x_7188_);
v___x_7191_ = lean_box(0);
v_isShared_7192_ = v_isSharedCheck_7252_;
goto v_resetjp_7190_;
}
v_resetjp_7190_:
{
lean_object* v_fst_7193_; 
v_fst_7193_ = lean_ctor_get(v_a_7189_, 0);
lean_inc(v_fst_7193_);
lean_dec(v_a_7189_);
if (lean_obj_tag(v_fst_7193_) == 0)
{
lean_object* v___x_7194_; uint8_t v_didChange_7195_; 
v___x_7194_ = lean_st_ref_get(v_a_7162_);
v_didChange_7195_ = lean_ctor_get_uint8(v___x_7194_, sizeof(void*)*4);
lean_dec(v___x_7194_);
if (v_didChange_7195_ == 0)
{
lean_object* v_options_7196_; uint8_t v_hasTrace_7197_; 
v_options_7196_ = lean_ctor_get(v_a_7170_, 2);
v_hasTrace_7197_ = lean_ctor_get_uint8(v_options_7196_, sizeof(void*)*1);
if (v_hasTrace_7197_ == 0)
{
lean_object* v___x_7198_; lean_object* v___x_7200_; 
v___x_7198_ = lean_box(v_didChange_7195_);
if (v_isShared_7192_ == 0)
{
lean_ctor_set(v___x_7191_, 0, v___x_7198_);
v___x_7200_ = v___x_7191_;
goto v_reusejp_7199_;
}
else
{
lean_object* v_reuseFailAlloc_7201_; 
v_reuseFailAlloc_7201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7201_, 0, v___x_7198_);
v___x_7200_ = v_reuseFailAlloc_7201_;
goto v_reusejp_7199_;
}
v_reusejp_7199_:
{
return v___x_7200_;
}
}
else
{
lean_object* v_inheritedTraceOptions_7202_; lean_object* v___x_7203_; lean_object* v___x_7204_; uint8_t v___x_7205_; 
v_inheritedTraceOptions_7202_ = lean_ctor_get(v_a_7170_, 13);
v___x_7203_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_7204_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_7205_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7202_, v_options_7196_, v___x_7204_);
if (v___x_7205_ == 0)
{
lean_object* v___x_7206_; lean_object* v___x_7208_; 
v___x_7206_ = lean_box(v_didChange_7195_);
if (v_isShared_7192_ == 0)
{
lean_ctor_set(v___x_7191_, 0, v___x_7206_);
v___x_7208_ = v___x_7191_;
goto v_reusejp_7207_;
}
else
{
lean_object* v_reuseFailAlloc_7209_; 
v_reuseFailAlloc_7209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7209_, 0, v___x_7206_);
v___x_7208_ = v_reuseFailAlloc_7209_;
goto v_reusejp_7207_;
}
v_reusejp_7207_:
{
return v___x_7208_;
}
}
else
{
lean_object* v___x_7210_; lean_object* v___x_7211_; 
lean_del_object(v___x_7191_);
v___x_7210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_7211_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_7203_, v___x_7210_, v_a_7168_, v_a_7169_, v_a_7170_, v_a_7171_);
if (lean_obj_tag(v___x_7211_) == 0)
{
lean_object* v___x_7213_; uint8_t v_isShared_7214_; uint8_t v_isSharedCheck_7219_; 
v_isSharedCheck_7219_ = !lean_is_exclusive(v___x_7211_);
if (v_isSharedCheck_7219_ == 0)
{
lean_object* v_unused_7220_; 
v_unused_7220_ = lean_ctor_get(v___x_7211_, 0);
lean_dec(v_unused_7220_);
v___x_7213_ = v___x_7211_;
v_isShared_7214_ = v_isSharedCheck_7219_;
goto v_resetjp_7212_;
}
else
{
lean_dec(v___x_7211_);
v___x_7213_ = lean_box(0);
v_isShared_7214_ = v_isSharedCheck_7219_;
goto v_resetjp_7212_;
}
v_resetjp_7212_:
{
lean_object* v___x_7215_; lean_object* v___x_7217_; 
v___x_7215_ = lean_box(v_didChange_7195_);
if (v_isShared_7214_ == 0)
{
lean_ctor_set(v___x_7213_, 0, v___x_7215_);
v___x_7217_ = v___x_7213_;
goto v_reusejp_7216_;
}
else
{
lean_object* v_reuseFailAlloc_7218_; 
v_reuseFailAlloc_7218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7218_, 0, v___x_7215_);
v___x_7217_ = v_reuseFailAlloc_7218_;
goto v_reusejp_7216_;
}
v_reusejp_7216_:
{
return v___x_7217_;
}
}
}
else
{
lean_object* v_a_7221_; lean_object* v___x_7223_; uint8_t v_isShared_7224_; uint8_t v_isSharedCheck_7228_; 
v_a_7221_ = lean_ctor_get(v___x_7211_, 0);
v_isSharedCheck_7228_ = !lean_is_exclusive(v___x_7211_);
if (v_isSharedCheck_7228_ == 0)
{
v___x_7223_ = v___x_7211_;
v_isShared_7224_ = v_isSharedCheck_7228_;
goto v_resetjp_7222_;
}
else
{
lean_inc(v_a_7221_);
lean_dec(v___x_7211_);
v___x_7223_ = lean_box(0);
v_isShared_7224_ = v_isSharedCheck_7228_;
goto v_resetjp_7222_;
}
v_resetjp_7222_:
{
lean_object* v___x_7226_; 
if (v_isShared_7224_ == 0)
{
v___x_7226_ = v___x_7223_;
goto v_reusejp_7225_;
}
else
{
lean_object* v_reuseFailAlloc_7227_; 
v_reuseFailAlloc_7227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7227_, 0, v_a_7221_);
v___x_7226_ = v_reuseFailAlloc_7227_;
goto v_reusejp_7225_;
}
v_reusejp_7225_:
{
return v___x_7226_;
}
}
}
}
}
}
else
{
lean_object* v_options_7229_; uint8_t v_hasTrace_7230_; 
lean_del_object(v___x_7191_);
v_options_7229_ = lean_ctor_get(v_a_7170_, 2);
v_hasTrace_7230_ = lean_ctor_get_uint8(v_options_7229_, sizeof(void*)*1);
if (v_hasTrace_7230_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_7232_; lean_object* v___x_7233_; lean_object* v___x_7234_; uint8_t v___x_7235_; 
v_inheritedTraceOptions_7232_ = lean_ctor_get(v_a_7170_, 13);
v___x_7233_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_7234_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_7235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7232_, v_options_7229_, v___x_7234_);
if (v___x_7235_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_7237_; lean_object* v___x_7238_; 
v___x_7237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_7238_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_7233_, v___x_7237_, v_a_7168_, v_a_7169_, v_a_7170_, v_a_7171_);
if (lean_obj_tag(v___x_7238_) == 0)
{
lean_dec_ref_known(v___x_7238_, 1);
goto _start;
}
else
{
lean_object* v_a_7240_; lean_object* v___x_7242_; uint8_t v_isShared_7243_; uint8_t v_isSharedCheck_7247_; 
v_a_7240_ = lean_ctor_get(v___x_7238_, 0);
v_isSharedCheck_7247_ = !lean_is_exclusive(v___x_7238_);
if (v_isSharedCheck_7247_ == 0)
{
v___x_7242_ = v___x_7238_;
v_isShared_7243_ = v_isSharedCheck_7247_;
goto v_resetjp_7241_;
}
else
{
lean_inc(v_a_7240_);
lean_dec(v___x_7238_);
v___x_7242_ = lean_box(0);
v_isShared_7243_ = v_isSharedCheck_7247_;
goto v_resetjp_7241_;
}
v_resetjp_7241_:
{
lean_object* v___x_7245_; 
if (v_isShared_7243_ == 0)
{
v___x_7245_ = v___x_7242_;
goto v_reusejp_7244_;
}
else
{
lean_object* v_reuseFailAlloc_7246_; 
v_reuseFailAlloc_7246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7246_, 0, v_a_7240_);
v___x_7245_ = v_reuseFailAlloc_7246_;
goto v_reusejp_7244_;
}
v_reusejp_7244_:
{
return v___x_7245_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_7248_; lean_object* v___x_7250_; 
v_val_7248_ = lean_ctor_get(v_fst_7193_, 0);
lean_inc(v_val_7248_);
lean_dec_ref_known(v_fst_7193_, 1);
if (v_isShared_7192_ == 0)
{
lean_ctor_set(v___x_7191_, 0, v_val_7248_);
v___x_7250_ = v___x_7191_;
goto v_reusejp_7249_;
}
else
{
lean_object* v_reuseFailAlloc_7251_; 
v_reuseFailAlloc_7251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7251_, 0, v_val_7248_);
v___x_7250_ = v_reuseFailAlloc_7251_;
goto v_reusejp_7249_;
}
v_reusejp_7249_:
{
return v___x_7250_;
}
}
}
}
else
{
lean_object* v_a_7253_; lean_object* v___x_7255_; uint8_t v_isShared_7256_; uint8_t v_isSharedCheck_7260_; 
v_a_7253_ = lean_ctor_get(v___x_7188_, 0);
v_isSharedCheck_7260_ = !lean_is_exclusive(v___x_7188_);
if (v_isSharedCheck_7260_ == 0)
{
v___x_7255_ = v___x_7188_;
v_isShared_7256_ = v_isSharedCheck_7260_;
goto v_resetjp_7254_;
}
else
{
lean_inc(v_a_7253_);
lean_dec(v___x_7188_);
v___x_7255_ = lean_box(0);
v_isShared_7256_ = v_isSharedCheck_7260_;
goto v_resetjp_7254_;
}
v_resetjp_7254_:
{
lean_object* v___x_7258_; 
if (v_isShared_7256_ == 0)
{
v___x_7258_ = v___x_7255_;
goto v_reusejp_7257_;
}
else
{
lean_object* v_reuseFailAlloc_7259_; 
v_reuseFailAlloc_7259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7259_, 0, v_a_7253_);
v___x_7258_ = v_reuseFailAlloc_7259_;
goto v_reusejp_7257_;
}
v_reusejp_7257_:
{
return v___x_7258_;
}
}
}
}
}
}
else
{
lean_object* v_a_7263_; lean_object* v___x_7265_; uint8_t v_isShared_7266_; uint8_t v_isSharedCheck_7270_; 
v_a_7263_ = lean_ctor_get(v___x_7174_, 0);
v_isSharedCheck_7270_ = !lean_is_exclusive(v___x_7174_);
if (v_isSharedCheck_7270_ == 0)
{
v___x_7265_ = v___x_7174_;
v_isShared_7266_ = v_isSharedCheck_7270_;
goto v_resetjp_7264_;
}
else
{
lean_inc(v_a_7263_);
lean_dec(v___x_7174_);
v___x_7265_ = lean_box(0);
v_isShared_7266_ = v_isSharedCheck_7270_;
goto v_resetjp_7264_;
}
v_resetjp_7264_:
{
lean_object* v___x_7268_; 
if (v_isShared_7266_ == 0)
{
v___x_7268_ = v___x_7265_;
goto v_reusejp_7267_;
}
else
{
lean_object* v_reuseFailAlloc_7269_; 
v_reuseFailAlloc_7269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7269_, 0, v_a_7263_);
v___x_7268_ = v_reuseFailAlloc_7269_;
goto v_reusejp_7267_;
}
v_reusejp_7267_:
{
return v___x_7268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_7271_, lean_object* v_a_7272_, lean_object* v_a_7273_, lean_object* v_a_7274_, lean_object* v_a_7275_, lean_object* v_a_7276_, lean_object* v_a_7277_, lean_object* v_a_7278_, lean_object* v_a_7279_, lean_object* v_a_7280_, lean_object* v_a_7281_, lean_object* v_a_7282_, lean_object* v_a_7283_){
_start:
{
lean_object* v_res_7284_; 
v_res_7284_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_7271_, v_a_7272_, v_a_7273_, v_a_7274_, v_a_7275_, v_a_7276_, v_a_7277_, v_a_7278_, v_a_7279_, v_a_7280_, v_a_7281_, v_a_7282_);
lean_dec(v_a_7282_);
lean_dec_ref(v_a_7281_);
lean_dec(v_a_7280_);
lean_dec_ref(v_a_7279_);
lean_dec(v_a_7278_);
lean_dec_ref(v_a_7277_);
lean_dec(v_a_7276_);
lean_dec_ref(v_a_7275_);
lean_dec(v_a_7274_);
lean_dec(v_a_7273_);
lean_dec_ref(v_a_7272_);
lean_dec(v_passes_7271_);
return v_res_7284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_7285_, lean_object* v_msg_7286_, lean_object* v___y_7287_, lean_object* v___y_7288_, lean_object* v___y_7289_, lean_object* v___y_7290_, lean_object* v___y_7291_, lean_object* v___y_7292_, lean_object* v___y_7293_, lean_object* v___y_7294_, lean_object* v___y_7295_, lean_object* v___y_7296_, lean_object* v___y_7297_){
_start:
{
lean_object* v___x_7299_; 
v___x_7299_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_7285_, v_msg_7286_, v___y_7294_, v___y_7295_, v___y_7296_, v___y_7297_);
return v___x_7299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_7300_, lean_object* v_msg_7301_, lean_object* v___y_7302_, lean_object* v___y_7303_, lean_object* v___y_7304_, lean_object* v___y_7305_, lean_object* v___y_7306_, lean_object* v___y_7307_, lean_object* v___y_7308_, lean_object* v___y_7309_, lean_object* v___y_7310_, lean_object* v___y_7311_, lean_object* v___y_7312_, lean_object* v___y_7313_){
_start:
{
lean_object* v_res_7314_; 
v_res_7314_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_7300_, v_msg_7301_, v___y_7302_, v___y_7303_, v___y_7304_, v___y_7305_, v___y_7306_, v___y_7307_, v___y_7308_, v___y_7309_, v___y_7310_, v___y_7311_, v___y_7312_);
lean_dec(v___y_7312_);
lean_dec_ref(v___y_7311_);
lean_dec(v___y_7310_);
lean_dec_ref(v___y_7309_);
lean_dec(v___y_7308_);
lean_dec_ref(v___y_7307_);
lean_dec(v___y_7306_);
lean_dec_ref(v___y_7305_);
lean_dec(v___y_7304_);
lean_dec(v___y_7303_);
lean_dec_ref(v___y_7302_);
return v_res_7314_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_7315_, lean_object* v_x_7316_, lean_object* v___y_7317_, lean_object* v___y_7318_, lean_object* v___y_7319_, lean_object* v___y_7320_, lean_object* v___y_7321_, lean_object* v___y_7322_, lean_object* v___y_7323_, lean_object* v___y_7324_, lean_object* v___y_7325_, lean_object* v___y_7326_, lean_object* v___y_7327_){
_start:
{
lean_object* v___x_7329_; 
v___x_7329_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_7316_);
return v___x_7329_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_7330_, lean_object* v_x_7331_, lean_object* v___y_7332_, lean_object* v___y_7333_, lean_object* v___y_7334_, lean_object* v___y_7335_, lean_object* v___y_7336_, lean_object* v___y_7337_, lean_object* v___y_7338_, lean_object* v___y_7339_, lean_object* v___y_7340_, lean_object* v___y_7341_, lean_object* v___y_7342_, lean_object* v___y_7343_){
_start:
{
lean_object* v_res_7344_; 
v_res_7344_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_7330_, v_x_7331_, v___y_7332_, v___y_7333_, v___y_7334_, v___y_7335_, v___y_7336_, v___y_7337_, v___y_7338_, v___y_7339_, v___y_7340_, v___y_7341_, v___y_7342_);
lean_dec(v___y_7342_);
lean_dec_ref(v___y_7341_);
lean_dec(v___y_7340_);
lean_dec_ref(v___y_7339_);
lean_dec(v___y_7338_);
lean_dec_ref(v___y_7337_);
lean_dec(v___y_7336_);
lean_dec_ref(v___y_7335_);
lean_dec(v___y_7334_);
lean_dec(v___y_7333_);
lean_dec_ref(v___y_7332_);
return v_res_7344_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_7345_, lean_object* v_as_x27_7346_, lean_object* v_b_7347_, lean_object* v_a_7348_, lean_object* v___y_7349_, lean_object* v___y_7350_, lean_object* v___y_7351_, lean_object* v___y_7352_, lean_object* v___y_7353_, lean_object* v___y_7354_, lean_object* v___y_7355_, lean_object* v___y_7356_, lean_object* v___y_7357_, lean_object* v___y_7358_, lean_object* v___y_7359_){
_start:
{
lean_object* v___x_7361_; 
v___x_7361_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_7346_, v_b_7347_, v___y_7349_, v___y_7350_, v___y_7351_, v___y_7352_, v___y_7353_, v___y_7354_, v___y_7355_, v___y_7356_, v___y_7357_, v___y_7358_, v___y_7359_);
return v___x_7361_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_7362_, lean_object* v_as_x27_7363_, lean_object* v_b_7364_, lean_object* v_a_7365_, lean_object* v___y_7366_, lean_object* v___y_7367_, lean_object* v___y_7368_, lean_object* v___y_7369_, lean_object* v___y_7370_, lean_object* v___y_7371_, lean_object* v___y_7372_, lean_object* v___y_7373_, lean_object* v___y_7374_, lean_object* v___y_7375_, lean_object* v___y_7376_, lean_object* v___y_7377_){
_start:
{
lean_object* v_res_7378_; 
v_res_7378_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_7362_, v_as_x27_7363_, v_b_7364_, v_a_7365_, v___y_7366_, v___y_7367_, v___y_7368_, v___y_7369_, v___y_7370_, v___y_7371_, v___y_7372_, v___y_7373_, v___y_7374_, v___y_7375_, v___y_7376_);
lean_dec(v___y_7376_);
lean_dec_ref(v___y_7375_);
lean_dec(v___y_7374_);
lean_dec_ref(v___y_7373_);
lean_dec(v___y_7372_);
lean_dec_ref(v___y_7371_);
lean_dec(v___y_7370_);
lean_dec_ref(v___y_7369_);
lean_dec(v___y_7368_);
lean_dec(v___y_7367_);
lean_dec_ref(v___y_7366_);
lean_dec(v_as_x27_7363_);
lean_dec(v_as_7362_);
return v_res_7378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_7379_, lean_object* v_data_7380_, lean_object* v_ref_7381_, lean_object* v_msg_7382_, lean_object* v___y_7383_, lean_object* v___y_7384_, lean_object* v___y_7385_, lean_object* v___y_7386_, lean_object* v___y_7387_, lean_object* v___y_7388_, lean_object* v___y_7389_, lean_object* v___y_7390_, lean_object* v___y_7391_, lean_object* v___y_7392_, lean_object* v___y_7393_){
_start:
{
lean_object* v___x_7395_; 
v___x_7395_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_7379_, v_data_7380_, v_ref_7381_, v_msg_7382_, v___y_7390_, v___y_7391_, v___y_7392_, v___y_7393_);
return v___x_7395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_7396_, lean_object* v_data_7397_, lean_object* v_ref_7398_, lean_object* v_msg_7399_, lean_object* v___y_7400_, lean_object* v___y_7401_, lean_object* v___y_7402_, lean_object* v___y_7403_, lean_object* v___y_7404_, lean_object* v___y_7405_, lean_object* v___y_7406_, lean_object* v___y_7407_, lean_object* v___y_7408_, lean_object* v___y_7409_, lean_object* v___y_7410_, lean_object* v___y_7411_){
_start:
{
lean_object* v_res_7412_; 
v_res_7412_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_7396_, v_data_7397_, v_ref_7398_, v_msg_7399_, v___y_7400_, v___y_7401_, v___y_7402_, v___y_7403_, v___y_7404_, v___y_7405_, v___y_7406_, v___y_7407_, v___y_7408_, v___y_7409_, v___y_7410_);
lean_dec(v___y_7410_);
lean_dec_ref(v___y_7409_);
lean_dec(v___y_7408_);
lean_dec_ref(v___y_7407_);
lean_dec(v___y_7406_);
lean_dec_ref(v___y_7405_);
lean_dec(v___y_7404_);
lean_dec_ref(v___y_7403_);
lean_dec(v___y_7402_);
lean_dec(v___y_7401_);
lean_dec_ref(v___y_7400_);
return v_res_7412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_7413_, lean_object* v_a_7414_, lean_object* v_a_7415_, lean_object* v_a_7416_, lean_object* v_a_7417_, lean_object* v_a_7418_, lean_object* v_a_7419_, lean_object* v_a_7420_, lean_object* v_a_7421_, lean_object* v_a_7422_, lean_object* v_a_7423_, lean_object* v_a_7424_){
_start:
{
lean_object* v___x_7426_; 
v___x_7426_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_7413_, v_a_7414_, v_a_7415_, v_a_7416_, v_a_7417_, v_a_7418_, v_a_7419_, v_a_7420_, v_a_7421_, v_a_7422_, v_a_7423_, v_a_7424_);
if (lean_obj_tag(v___x_7426_) == 0)
{
lean_object* v_a_7427_; lean_object* v___x_7428_; lean_object* v___x_7430_; uint8_t v_isShared_7431_; uint8_t v_isSharedCheck_7435_; 
v_a_7427_ = lean_ctor_get(v___x_7426_, 0);
lean_inc(v_a_7427_);
lean_dec_ref_known(v___x_7426_, 1);
v___x_7428_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_7414_, v_a_7415_);
v_isSharedCheck_7435_ = !lean_is_exclusive(v___x_7428_);
if (v_isSharedCheck_7435_ == 0)
{
lean_object* v_unused_7436_; 
v_unused_7436_ = lean_ctor_get(v___x_7428_, 0);
lean_dec(v_unused_7436_);
v___x_7430_ = v___x_7428_;
v_isShared_7431_ = v_isSharedCheck_7435_;
goto v_resetjp_7429_;
}
else
{
lean_dec(v___x_7428_);
v___x_7430_ = lean_box(0);
v_isShared_7431_ = v_isSharedCheck_7435_;
goto v_resetjp_7429_;
}
v_resetjp_7429_:
{
lean_object* v___x_7433_; 
if (v_isShared_7431_ == 0)
{
lean_ctor_set(v___x_7430_, 0, v_a_7427_);
v___x_7433_ = v___x_7430_;
goto v_reusejp_7432_;
}
else
{
lean_object* v_reuseFailAlloc_7434_; 
v_reuseFailAlloc_7434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7434_, 0, v_a_7427_);
v___x_7433_ = v_reuseFailAlloc_7434_;
goto v_reusejp_7432_;
}
v_reusejp_7432_:
{
return v___x_7433_;
}
}
}
else
{
return v___x_7426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_7437_, lean_object* v_a_7438_, lean_object* v_a_7439_, lean_object* v_a_7440_, lean_object* v_a_7441_, lean_object* v_a_7442_, lean_object* v_a_7443_, lean_object* v_a_7444_, lean_object* v_a_7445_, lean_object* v_a_7446_, lean_object* v_a_7447_, lean_object* v_a_7448_, lean_object* v_a_7449_){
_start:
{
lean_object* v_res_7450_; 
v_res_7450_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_7437_, v_a_7438_, v_a_7439_, v_a_7440_, v_a_7441_, v_a_7442_, v_a_7443_, v_a_7444_, v_a_7445_, v_a_7446_, v_a_7447_, v_a_7448_);
lean_dec(v_a_7448_);
lean_dec_ref(v_a_7447_);
lean_dec(v_a_7446_);
lean_dec_ref(v_a_7445_);
lean_dec(v_a_7444_);
lean_dec_ref(v_a_7443_);
lean_dec(v_a_7442_);
lean_dec_ref(v_a_7441_);
lean_dec(v_a_7440_);
lean_dec(v_a_7439_);
lean_dec_ref(v_a_7438_);
lean_dec(v_passes_7437_);
return v_res_7450_;
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
