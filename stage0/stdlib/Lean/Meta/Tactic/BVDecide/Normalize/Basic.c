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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_mvarId_1058_; lean_object* v___x_1059_; lean_object* v___x_5005__overap_1060_; lean_object* v___x_1061_; 
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
v___x_5005__overap_1060_ = l_Lean_MVarId_withContext___redArg(v___x_1015_, v___x_1057_, v_mvarId_1058_, v___x_1059_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_a_966_);
lean_inc_ref(v_a_965_);
lean_inc(v_a_964_);
v___x_1061_ = lean_apply_10(v___x_5005__overap_1060_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
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
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_mvarId_1218_; lean_object* v___x_1219_; lean_object* v___x_5157__overap_1220_; lean_object* v___x_1221_; 
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
v___x_5157__overap_1220_ = l_Lean_MVarId_withContext___redArg(v___x_1175_, v___x_1217_, v_mvarId_1218_, v___x_1219_);
lean_inc(v_a_1132_);
lean_inc_ref(v_a_1131_);
lean_inc(v_a_1130_);
lean_inc_ref(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc_ref(v_a_1127_);
lean_inc(v_a_1126_);
lean_inc_ref(v_a_1125_);
lean_inc(v_a_1124_);
v___x_1221_ = lean_apply_10(v___x_5157__overap_1220_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, lean_box(0));
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
lean_object* v___x_2023_; lean_object* v_typeAnalysis_2024_; lean_object* v_caches_2025_; lean_object* v_target_2026_; lean_object* v_hypotheses_2027_; uint8_t v_didChange_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2052_; 
v___x_2023_ = lean_st_ref_take(v_a_2021_);
v_typeAnalysis_2024_ = lean_ctor_get(v___x_2023_, 1);
v_caches_2025_ = lean_ctor_get(v___x_2023_, 0);
v_target_2026_ = lean_ctor_get(v___x_2023_, 2);
v_hypotheses_2027_ = lean_ctor_get(v___x_2023_, 3);
v_didChange_2028_ = lean_ctor_get_uint8(v___x_2023_, sizeof(void*)*4);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2030_ = v___x_2023_;
v_isShared_2031_ = v_isSharedCheck_2052_;
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
v_isShared_2031_ = v_isSharedCheck_2052_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_interestingStructures_2032_; lean_object* v_interestingEnums_2033_; lean_object* v_interestingMatchers_2034_; lean_object* v_uninteresting_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2051_; 
v_interestingStructures_2032_ = lean_ctor_get(v_typeAnalysis_2024_, 0);
v_interestingEnums_2033_ = lean_ctor_get(v_typeAnalysis_2024_, 1);
v_interestingMatchers_2034_ = lean_ctor_get(v_typeAnalysis_2024_, 2);
v_uninteresting_2035_ = lean_ctor_get(v_typeAnalysis_2024_, 3);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_typeAnalysis_2024_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2037_ = v_typeAnalysis_2024_;
v_isShared_2038_ = v_isSharedCheck_2051_;
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
v_isShared_2038_ = v_isSharedCheck_2051_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2039_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2040_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2041_ = lean_box(0);
v___x_2042_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2039_, v___x_2040_, v_interestingStructures_2032_, v_n_2020_, v___x_2041_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2042_);
v___x_2044_ = v___x_2037_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_interestingEnums_2033_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_interestingMatchers_2034_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_uninteresting_2035_);
v___x_2044_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2044_);
v___x_2046_ = v___x_2030_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_caches_2025_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_target_2026_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_hypotheses_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*4, v_didChange_2028_);
v___x_2046_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_st_ref_put(v_a_2021_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2041_);
return v___x_2048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_2053_, v_a_2054_);
lean_dec(v_a_2054_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2070_; lean_object* v_typeAnalysis_2071_; lean_object* v_caches_2072_; lean_object* v_target_2073_; lean_object* v_hypotheses_2074_; uint8_t v_didChange_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2099_; 
v___x_2070_ = lean_st_ref_take(v_a_2059_);
v_typeAnalysis_2071_ = lean_ctor_get(v___x_2070_, 1);
v_caches_2072_ = lean_ctor_get(v___x_2070_, 0);
v_target_2073_ = lean_ctor_get(v___x_2070_, 2);
v_hypotheses_2074_ = lean_ctor_get(v___x_2070_, 3);
v_didChange_2075_ = lean_ctor_get_uint8(v___x_2070_, sizeof(void*)*4);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2077_ = v___x_2070_;
v_isShared_2078_ = v_isSharedCheck_2099_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_hypotheses_2074_);
lean_inc(v_target_2073_);
lean_inc(v_typeAnalysis_2071_);
lean_inc(v_caches_2072_);
lean_dec(v___x_2070_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2099_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_interestingStructures_2079_; lean_object* v_interestingEnums_2080_; lean_object* v_interestingMatchers_2081_; lean_object* v_uninteresting_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2098_; 
v_interestingStructures_2079_ = lean_ctor_get(v_typeAnalysis_2071_, 0);
v_interestingEnums_2080_ = lean_ctor_get(v_typeAnalysis_2071_, 1);
v_interestingMatchers_2081_ = lean_ctor_get(v_typeAnalysis_2071_, 2);
v_uninteresting_2082_ = lean_ctor_get(v_typeAnalysis_2071_, 3);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_typeAnalysis_2071_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2084_ = v_typeAnalysis_2071_;
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_uninteresting_2082_);
lean_inc(v_interestingMatchers_2081_);
lean_inc(v_interestingEnums_2080_);
lean_inc(v_interestingStructures_2079_);
lean_dec(v_typeAnalysis_2071_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2086_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2087_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2088_ = lean_box(0);
v___x_2089_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2086_, v___x_2087_, v_interestingStructures_2079_, v_n_2057_, v___x_2088_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2089_);
v___x_2091_ = v___x_2084_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_interestingEnums_2080_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_interestingMatchers_2081_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_uninteresting_2082_);
v___x_2091_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v___x_2091_);
v___x_2093_ = v___x_2077_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_caches_2072_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_target_2073_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_hypotheses_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2096_, sizeof(void*)*4, v_didChange_2075_);
v___x_2093_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_st_ref_put(v_a_2059_, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2088_);
return v___x_2095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v_typeAnalysis_2118_; lean_object* v_caches_2119_; lean_object* v_target_2120_; lean_object* v_hypotheses_2121_; uint8_t v_didChange_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2146_; 
v___x_2117_ = lean_st_ref_take(v_a_2115_);
v_typeAnalysis_2118_ = lean_ctor_get(v___x_2117_, 1);
v_caches_2119_ = lean_ctor_get(v___x_2117_, 0);
v_target_2120_ = lean_ctor_get(v___x_2117_, 2);
v_hypotheses_2121_ = lean_ctor_get(v___x_2117_, 3);
v_didChange_2122_ = lean_ctor_get_uint8(v___x_2117_, sizeof(void*)*4);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2124_ = v___x_2117_;
v_isShared_2125_ = v_isSharedCheck_2146_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_hypotheses_2121_);
lean_inc(v_target_2120_);
lean_inc(v_typeAnalysis_2118_);
lean_inc(v_caches_2119_);
lean_dec(v___x_2117_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2146_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_interestingStructures_2126_; lean_object* v_interestingEnums_2127_; lean_object* v_interestingMatchers_2128_; lean_object* v_uninteresting_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2145_; 
v_interestingStructures_2126_ = lean_ctor_get(v_typeAnalysis_2118_, 0);
v_interestingEnums_2127_ = lean_ctor_get(v_typeAnalysis_2118_, 1);
v_interestingMatchers_2128_ = lean_ctor_get(v_typeAnalysis_2118_, 2);
v_uninteresting_2129_ = lean_ctor_get(v_typeAnalysis_2118_, 3);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_typeAnalysis_2118_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2131_ = v_typeAnalysis_2118_;
v_isShared_2132_ = v_isSharedCheck_2145_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_uninteresting_2129_);
lean_inc(v_interestingMatchers_2128_);
lean_inc(v_interestingEnums_2127_);
lean_inc(v_interestingStructures_2126_);
lean_dec(v_typeAnalysis_2118_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2145_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2133_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2134_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2135_ = lean_box(0);
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2133_, v___x_2134_, v_interestingEnums_2127_, v_n_2114_, v___x_2135_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 1, v___x_2136_);
v___x_2138_ = v___x_2131_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_interestingStructures_2126_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_interestingMatchers_2128_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_uninteresting_2129_);
v___x_2138_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v___x_2138_);
v___x_2140_ = v___x_2124_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_caches_2119_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_target_2120_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_hypotheses_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*4, v_didChange_2122_);
v___x_2140_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_st_ref_put(v_a_2115_, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2135_);
return v___x_2142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_2147_, v_a_2148_);
lean_dec(v_a_2148_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2164_; lean_object* v_typeAnalysis_2165_; lean_object* v_caches_2166_; lean_object* v_target_2167_; lean_object* v_hypotheses_2168_; uint8_t v_didChange_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2193_; 
v___x_2164_ = lean_st_ref_take(v_a_2153_);
v_typeAnalysis_2165_ = lean_ctor_get(v___x_2164_, 1);
v_caches_2166_ = lean_ctor_get(v___x_2164_, 0);
v_target_2167_ = lean_ctor_get(v___x_2164_, 2);
v_hypotheses_2168_ = lean_ctor_get(v___x_2164_, 3);
v_didChange_2169_ = lean_ctor_get_uint8(v___x_2164_, sizeof(void*)*4);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2171_ = v___x_2164_;
v_isShared_2172_ = v_isSharedCheck_2193_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_hypotheses_2168_);
lean_inc(v_target_2167_);
lean_inc(v_typeAnalysis_2165_);
lean_inc(v_caches_2166_);
lean_dec(v___x_2164_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2193_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v_interestingStructures_2173_; lean_object* v_interestingEnums_2174_; lean_object* v_interestingMatchers_2175_; lean_object* v_uninteresting_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2192_; 
v_interestingStructures_2173_ = lean_ctor_get(v_typeAnalysis_2165_, 0);
v_interestingEnums_2174_ = lean_ctor_get(v_typeAnalysis_2165_, 1);
v_interestingMatchers_2175_ = lean_ctor_get(v_typeAnalysis_2165_, 2);
v_uninteresting_2176_ = lean_ctor_get(v_typeAnalysis_2165_, 3);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_typeAnalysis_2165_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2178_ = v_typeAnalysis_2165_;
v_isShared_2179_ = v_isSharedCheck_2192_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_uninteresting_2176_);
lean_inc(v_interestingMatchers_2175_);
lean_inc(v_interestingEnums_2174_);
lean_inc(v_interestingStructures_2173_);
lean_dec(v_typeAnalysis_2165_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2192_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2180_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2181_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2182_ = lean_box(0);
v___x_2183_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2180_, v___x_2181_, v_interestingEnums_2174_, v_n_2151_, v___x_2182_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v___x_2183_);
v___x_2185_ = v___x_2178_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_interestingStructures_2173_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_interestingMatchers_2175_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_uninteresting_2176_);
v___x_2185_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2187_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v___x_2185_);
v___x_2187_ = v___x_2171_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_caches_2166_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_target_2167_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_hypotheses_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*4, v_didChange_2169_);
v___x_2187_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_st_ref_put(v_a_2153_, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2182_);
return v___x_2189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_2208_, lean_object* v_k_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v_typeAnalysis_2213_; lean_object* v_caches_2214_; lean_object* v_target_2215_; lean_object* v_hypotheses_2216_; uint8_t v_didChange_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2241_; 
v___x_2212_ = lean_st_ref_take(v_a_2210_);
v_typeAnalysis_2213_ = lean_ctor_get(v___x_2212_, 1);
v_caches_2214_ = lean_ctor_get(v___x_2212_, 0);
v_target_2215_ = lean_ctor_get(v___x_2212_, 2);
v_hypotheses_2216_ = lean_ctor_get(v___x_2212_, 3);
v_didChange_2217_ = lean_ctor_get_uint8(v___x_2212_, sizeof(void*)*4);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2219_ = v___x_2212_;
v_isShared_2220_ = v_isSharedCheck_2241_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_hypotheses_2216_);
lean_inc(v_target_2215_);
lean_inc(v_typeAnalysis_2213_);
lean_inc(v_caches_2214_);
lean_dec(v___x_2212_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2241_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v_interestingStructures_2221_; lean_object* v_interestingEnums_2222_; lean_object* v_interestingMatchers_2223_; lean_object* v_uninteresting_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2240_; 
v_interestingStructures_2221_ = lean_ctor_get(v_typeAnalysis_2213_, 0);
v_interestingEnums_2222_ = lean_ctor_get(v_typeAnalysis_2213_, 1);
v_interestingMatchers_2223_ = lean_ctor_get(v_typeAnalysis_2213_, 2);
v_uninteresting_2224_ = lean_ctor_get(v_typeAnalysis_2213_, 3);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_typeAnalysis_2213_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2226_ = v_typeAnalysis_2213_;
v_isShared_2227_ = v_isSharedCheck_2240_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_uninteresting_2224_);
lean_inc(v_interestingMatchers_2223_);
lean_inc(v_interestingEnums_2222_);
lean_inc(v_interestingStructures_2221_);
lean_dec(v_typeAnalysis_2213_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2240_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2228_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2229_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2230_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2228_, v___x_2229_, v_interestingMatchers_2223_, v_n_2208_, v_k_2209_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 2, v___x_2230_);
v___x_2232_ = v___x_2226_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_interestingStructures_2221_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_interestingEnums_2222_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_uninteresting_2224_);
v___x_2232_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v___x_2232_);
v___x_2234_ = v___x_2219_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_caches_2214_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_target_2215_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_hypotheses_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*4, v_didChange_2217_);
v___x_2234_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_st_ref_put(v_a_2210_, v___x_2234_);
v___x_2236_ = lean_box(0);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_2242_, lean_object* v_k_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_2242_, v_k_2243_, v_a_2244_);
lean_dec(v_a_2244_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_2247_, lean_object* v_k_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; lean_object* v_typeAnalysis_2262_; lean_object* v_caches_2263_; lean_object* v_target_2264_; lean_object* v_hypotheses_2265_; uint8_t v_didChange_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2290_; 
v___x_2261_ = lean_st_ref_take(v_a_2250_);
v_typeAnalysis_2262_ = lean_ctor_get(v___x_2261_, 1);
v_caches_2263_ = lean_ctor_get(v___x_2261_, 0);
v_target_2264_ = lean_ctor_get(v___x_2261_, 2);
v_hypotheses_2265_ = lean_ctor_get(v___x_2261_, 3);
v_didChange_2266_ = lean_ctor_get_uint8(v___x_2261_, sizeof(void*)*4);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2268_ = v___x_2261_;
v_isShared_2269_ = v_isSharedCheck_2290_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_hypotheses_2265_);
lean_inc(v_target_2264_);
lean_inc(v_typeAnalysis_2262_);
lean_inc(v_caches_2263_);
lean_dec(v___x_2261_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2290_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v_interestingStructures_2270_; lean_object* v_interestingEnums_2271_; lean_object* v_interestingMatchers_2272_; lean_object* v_uninteresting_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2289_; 
v_interestingStructures_2270_ = lean_ctor_get(v_typeAnalysis_2262_, 0);
v_interestingEnums_2271_ = lean_ctor_get(v_typeAnalysis_2262_, 1);
v_interestingMatchers_2272_ = lean_ctor_get(v_typeAnalysis_2262_, 2);
v_uninteresting_2273_ = lean_ctor_get(v_typeAnalysis_2262_, 3);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_typeAnalysis_2262_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2275_ = v_typeAnalysis_2262_;
v_isShared_2276_ = v_isSharedCheck_2289_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_uninteresting_2273_);
lean_inc(v_interestingMatchers_2272_);
lean_inc(v_interestingEnums_2271_);
lean_inc(v_interestingStructures_2270_);
lean_dec(v_typeAnalysis_2262_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2289_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2277_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2279_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2277_, v___x_2278_, v_interestingMatchers_2272_, v_n_2247_, v_k_2248_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 2, v___x_2279_);
v___x_2281_ = v___x_2275_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_interestingStructures_2270_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_interestingEnums_2271_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_uninteresting_2273_);
v___x_2281_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2283_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v___x_2281_);
v___x_2283_ = v___x_2268_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_caches_2263_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_target_2264_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_hypotheses_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*4, v_didChange_2266_);
v___x_2283_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = lean_st_ref_put(v_a_2250_, v___x_2283_);
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_2291_, lean_object* v_k_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_2291_, v_k_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2309_; lean_object* v_typeAnalysis_2310_; lean_object* v_caches_2311_; lean_object* v_target_2312_; lean_object* v_hypotheses_2313_; uint8_t v_didChange_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2338_; 
v___x_2309_ = lean_st_ref_take(v_a_2307_);
v_typeAnalysis_2310_ = lean_ctor_get(v___x_2309_, 1);
v_caches_2311_ = lean_ctor_get(v___x_2309_, 0);
v_target_2312_ = lean_ctor_get(v___x_2309_, 2);
v_hypotheses_2313_ = lean_ctor_get(v___x_2309_, 3);
v_didChange_2314_ = lean_ctor_get_uint8(v___x_2309_, sizeof(void*)*4);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2316_ = v___x_2309_;
v_isShared_2317_ = v_isSharedCheck_2338_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_hypotheses_2313_);
lean_inc(v_target_2312_);
lean_inc(v_typeAnalysis_2310_);
lean_inc(v_caches_2311_);
lean_dec(v___x_2309_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2338_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_interestingStructures_2318_; lean_object* v_interestingEnums_2319_; lean_object* v_interestingMatchers_2320_; lean_object* v_uninteresting_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2337_; 
v_interestingStructures_2318_ = lean_ctor_get(v_typeAnalysis_2310_, 0);
v_interestingEnums_2319_ = lean_ctor_get(v_typeAnalysis_2310_, 1);
v_interestingMatchers_2320_ = lean_ctor_get(v_typeAnalysis_2310_, 2);
v_uninteresting_2321_ = lean_ctor_get(v_typeAnalysis_2310_, 3);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_typeAnalysis_2310_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2323_ = v_typeAnalysis_2310_;
v_isShared_2324_ = v_isSharedCheck_2337_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_uninteresting_2321_);
lean_inc(v_interestingMatchers_2320_);
lean_inc(v_interestingEnums_2319_);
lean_inc(v_interestingStructures_2318_);
lean_dec(v_typeAnalysis_2310_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2337_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2325_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2326_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2327_ = lean_box(0);
v___x_2328_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2325_, v___x_2326_, v_uninteresting_2321_, v_n_2306_, v___x_2327_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 3, v___x_2328_);
v___x_2330_ = v___x_2323_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_interestingStructures_2318_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_interestingEnums_2319_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_interestingMatchers_2320_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 1, v___x_2330_);
v___x_2332_ = v___x_2316_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_caches_2311_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_target_2312_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_hypotheses_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*4, v_didChange_2314_);
v___x_2332_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_st_ref_put(v_a_2307_, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2327_);
return v___x_2334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_2339_, v_a_2340_);
lean_dec(v_a_2340_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v_typeAnalysis_2357_; lean_object* v_caches_2358_; lean_object* v_target_2359_; lean_object* v_hypotheses_2360_; uint8_t v_didChange_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2385_; 
v___x_2356_ = lean_st_ref_take(v_a_2345_);
v_typeAnalysis_2357_ = lean_ctor_get(v___x_2356_, 1);
v_caches_2358_ = lean_ctor_get(v___x_2356_, 0);
v_target_2359_ = lean_ctor_get(v___x_2356_, 2);
v_hypotheses_2360_ = lean_ctor_get(v___x_2356_, 3);
v_didChange_2361_ = lean_ctor_get_uint8(v___x_2356_, sizeof(void*)*4);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2363_ = v___x_2356_;
v_isShared_2364_ = v_isSharedCheck_2385_;
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
v_isShared_2364_ = v_isSharedCheck_2385_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v_interestingStructures_2365_; lean_object* v_interestingEnums_2366_; lean_object* v_interestingMatchers_2367_; lean_object* v_uninteresting_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2384_; 
v_interestingStructures_2365_ = lean_ctor_get(v_typeAnalysis_2357_, 0);
v_interestingEnums_2366_ = lean_ctor_get(v_typeAnalysis_2357_, 1);
v_interestingMatchers_2367_ = lean_ctor_get(v_typeAnalysis_2357_, 2);
v_uninteresting_2368_ = lean_ctor_get(v_typeAnalysis_2357_, 3);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_typeAnalysis_2357_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2370_ = v_typeAnalysis_2357_;
v_isShared_2371_ = v_isSharedCheck_2384_;
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
v_isShared_2371_ = v_isSharedCheck_2384_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2372_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2373_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2374_ = lean_box(0);
v___x_2375_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2372_, v___x_2373_, v_uninteresting_2368_, v_n_2343_, v___x_2374_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 3, v___x_2375_);
v___x_2377_ = v___x_2370_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_interestingStructures_2365_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_interestingEnums_2366_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v_interestingMatchers_2367_);
lean_ctor_set(v_reuseFailAlloc_2383_, 3, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v___x_2377_);
v___x_2379_ = v___x_2363_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_caches_2358_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_target_2359_);
lean_ctor_set(v_reuseFailAlloc_2382_, 3, v_hypotheses_2360_);
lean_ctor_set_uint8(v_reuseFailAlloc_2382_, sizeof(void*)*4, v_didChange_2361_);
v___x_2379_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_st_ref_put(v_a_2345_, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2374_);
return v___x_2381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = lean_box(0);
v___x_2401_ = lean_unsigned_to_nat(16u);
v___x_2402_ = lean_mk_array(v___x_2401_, v___x_2400_);
return v___x_2402_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v___x_2403_);
return v___x_2405_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_2407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
lean_ctor_set(v___x_2407_, 2, v___x_2406_);
lean_ctor_set(v___x_2407_, 3, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_ctx_2410_, lean_object* v_target_2411_, lean_object* v_x_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2423_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2424_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2425_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2426_ = 0;
v___x_2427_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2427_, 0, v___x_2423_);
lean_ctor_set(v___x_2427_, 1, v___x_2424_);
lean_ctor_set(v___x_2427_, 2, v_target_2411_);
lean_ctor_set(v___x_2427_, 3, v___x_2425_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*4, v___x_2426_);
v___x_2428_ = lean_st_mk_ref(v___x_2427_);
lean_inc(v_a_2421_);
lean_inc_ref(v_a_2420_);
lean_inc(v_a_2419_);
lean_inc_ref(v_a_2418_);
lean_inc(v_a_2417_);
lean_inc_ref(v_a_2416_);
lean_inc(v_a_2415_);
lean_inc_ref(v_a_2414_);
lean_inc(v_a_2413_);
lean_inc(v___x_2428_);
v___x_2429_ = lean_apply_12(v_x_2412_, v_ctx_2410_, v___x_2428_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, lean_box(0));
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2439_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2439_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2439_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2434_ = lean_st_ref_get(v___x_2428_);
lean_dec(v___x_2428_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_a_2430_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2435_);
v___x_2437_ = v___x_2432_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v___x_2428_);
v_a_2440_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2429_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2429_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_ctx_2448_, lean_object* v_target_2449_, lean_object* v_x_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_ctx_2448_, v_target_2449_, v_x_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_2462_, lean_object* v_ctx_2463_, lean_object* v_target_2464_, lean_object* v_x_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2476_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2477_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2478_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2479_ = 0;
v___x_2480_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2480_, 0, v___x_2476_);
lean_ctor_set(v___x_2480_, 1, v___x_2477_);
lean_ctor_set(v___x_2480_, 2, v_target_2464_);
lean_ctor_set(v___x_2480_, 3, v___x_2478_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*4, v___x_2479_);
v___x_2481_ = lean_st_mk_ref(v___x_2480_);
lean_inc(v_a_2474_);
lean_inc_ref(v_a_2473_);
lean_inc(v_a_2472_);
lean_inc_ref(v_a_2471_);
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
lean_inc(v_a_2468_);
lean_inc_ref(v_a_2467_);
lean_inc(v_a_2466_);
lean_inc(v___x_2481_);
v___x_2482_ = lean_apply_12(v_x_2465_, v_ctx_2463_, v___x_2481_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, lean_box(0));
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2492_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2487_ = lean_st_ref_get(v___x_2481_);
lean_dec(v___x_2481_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_a_2483_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2488_);
v___x_2490_ = v___x_2485_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v___x_2481_);
v_a_2493_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2482_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2482_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_2501_, lean_object* v_ctx_2502_, lean_object* v_target_2503_, lean_object* v_x_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_2501_, v_ctx_2502_, v_target_2503_, v_x_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_ctx_2516_, lean_object* v_target_2517_, lean_object* v_x_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2529_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2530_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2531_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2532_ = 0;
v___x_2533_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2533_, 0, v___x_2529_);
lean_ctor_set(v___x_2533_, 1, v___x_2530_);
lean_ctor_set(v___x_2533_, 2, v_target_2517_);
lean_ctor_set(v___x_2533_, 3, v___x_2531_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*4, v___x_2532_);
v___x_2534_ = lean_st_mk_ref(v___x_2533_);
lean_inc(v_a_2527_);
lean_inc_ref(v_a_2526_);
lean_inc(v_a_2525_);
lean_inc_ref(v_a_2524_);
lean_inc(v_a_2523_);
lean_inc_ref(v_a_2522_);
lean_inc(v_a_2521_);
lean_inc_ref(v_a_2520_);
lean_inc(v_a_2519_);
lean_inc(v___x_2534_);
v___x_2535_ = lean_apply_12(v_x_2518_, v_ctx_2516_, v___x_2534_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, lean_box(0));
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2540_ = lean_st_ref_get(v___x_2534_);
lean_dec(v___x_2534_);
lean_dec(v___x_2540_);
if (v_isShared_2539_ == 0)
{
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2536_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
lean_dec(v___x_2534_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_ctx_2545_, lean_object* v_target_2546_, lean_object* v_x_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_ctx_2545_, v_target_2546_, v_x_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_2559_, lean_object* v_ctx_2560_, lean_object* v_target_2561_, lean_object* v_x_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
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
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2588_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2588_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2588_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_st_ref_get(v___x_2578_);
lean_dec(v___x_2578_);
lean_dec(v___x_2584_);
if (v_isShared_2583_ == 0)
{
v___x_2586_ = v___x_2582_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2580_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
else
{
lean_dec(v___x_2578_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_2589_, lean_object* v_ctx_2590_, lean_object* v_target_2591_, lean_object* v_x_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_2589_, v_ctx_2590_, v_target_2591_, v_x_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
return v_res_2603_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2607_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2608_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___f_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2);
v___f_2610_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2611_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2610_, v___x_2609_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3);
v___x_2613_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2614_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2613_, v___x_2612_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4);
v___f_2616_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2617_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2616_, v___x_2615_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5);
v___x_2619_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2620_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6);
v___f_2622_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2623_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2622_, v___x_2621_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; 
v___x_2624_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7);
v___f_2625_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2626_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2625_, v___x_2624_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___x_2628_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2629_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2628_, v___x_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; 
v___x_2630_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___f_2631_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2632_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2631_, v___x_2630_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2635_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2636_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2638_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2637_, v___x_2636_, v___x_2635_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___x_2642_; 
v___x_2639_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___f_2640_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2641_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2642_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2641_, v___f_2640_, v___x_2639_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2643_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14);
v___x_2644_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2645_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2646_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2645_, v___x_2644_, v___x_2643_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; 
v___x_2647_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15);
v___f_2648_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2649_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2650_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2649_, v___f_2648_, v___x_2647_);
return v___x_2650_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2651_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16);
v___x_2652_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2653_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2654_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2653_, v___x_2652_, v___x_2651_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___f_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; 
v___x_2655_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___f_2656_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2657_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2658_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2657_, v___f_2656_, v___x_2655_);
return v___x_2658_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___f_2660_; lean_object* v___f_2661_; lean_object* v___x_2662_; 
v___x_2659_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18);
v___f_2660_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2662_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2661_, v___f_2660_, v___x_2659_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2663_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19);
v___x_2664_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2665_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2666_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2665_, v___x_2664_, v___x_2663_);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___f_2668_; lean_object* v___f_2669_; lean_object* v___x_2670_; 
v___x_2667_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___f_2668_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2669_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2670_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2669_, v___f_2668_, v___x_2667_);
return v___x_2670_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v_cls_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_cls_2681_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2682_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_2683_ = l_Lean_Name_append(v___x_2682_, v_cls_2681_);
return v___x_2683_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___f_2686_; 
v___x_2684_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2685_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2686_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2686_, 0, v___x_2685_);
lean_closure_set(v___f_2686_, 1, v___x_2684_);
return v___f_2686_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___f_2687_; lean_object* v___f_2688_; lean_object* v___f_2689_; 
v___f_2687_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2688_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___f_2689_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2689_, 0, v___f_2688_);
lean_closure_set(v___f_2689_, 1, v___f_2687_);
return v___f_2689_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; 
v___x_2690_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2691_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_2692_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2692_, 0, v___f_2691_);
lean_closure_set(v___f_2692_, 1, v___x_2690_);
return v___f_2692_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; 
v___f_2693_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2694_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2695_, 0, v___f_2694_);
lean_closure_set(v___f_2695_, 1, v___f_2693_);
return v___f_2695_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33(void){
_start:
{
lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___f_2698_; 
v___f_2696_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2697_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___f_2698_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2698_, 0, v___f_2697_);
lean_closure_set(v___f_2698_, 1, v___f_2696_);
return v___f_2698_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___f_2700_; lean_object* v___f_2701_; 
v___x_2699_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2700_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33);
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2701_, 0, v___f_2700_);
lean_closure_set(v___f_2701_, 1, v___x_2699_);
return v___f_2701_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35(void){
_start:
{
lean_object* v___f_2702_; lean_object* v___f_2703_; lean_object* v___f_2704_; 
v___f_2702_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2703_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v___f_2704_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2704_, 0, v___f_2703_);
lean_closure_set(v___f_2704_, 1, v___f_2702_);
return v___f_2704_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36));
v___x_2707_ = l_Lean_stringToMessageData(v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v___y_2722_; lean_object* v___x_2740_; lean_object* v_toApplicative_2741_; lean_object* v_toFunctor_2742_; lean_object* v_toSeq_2743_; lean_object* v_toSeqLeft_2744_; lean_object* v_toSeqRight_2745_; lean_object* v___f_2746_; lean_object* v___f_2747_; lean_object* v___f_2748_; lean_object* v___f_2749_; lean_object* v___x_2750_; lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v_toApplicative_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2808_; 
v___x_2740_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2741_ = lean_ctor_get(v___x_2740_, 0);
v_toFunctor_2742_ = lean_ctor_get(v_toApplicative_2741_, 0);
v_toSeq_2743_ = lean_ctor_get(v_toApplicative_2741_, 2);
v_toSeqLeft_2744_ = lean_ctor_get(v_toApplicative_2741_, 3);
v_toSeqRight_2745_ = lean_ctor_get(v_toApplicative_2741_, 4);
v___f_2746_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2747_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2742_, 2);
v___f_2748_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2748_, 0, v_toFunctor_2742_);
v___f_2749_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2749_, 0, v_toFunctor_2742_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___f_2748_);
lean_ctor_set(v___x_2750_, 1, v___f_2749_);
lean_inc(v_toSeqRight_2745_);
v___f_2751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2751_, 0, v_toSeqRight_2745_);
lean_inc(v_toSeqLeft_2744_);
v___f_2752_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2752_, 0, v_toSeqLeft_2744_);
lean_inc(v_toSeq_2743_);
v___f_2753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2753_, 0, v_toSeq_2743_);
v___x_2754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2750_);
lean_ctor_set(v___x_2754_, 1, v___f_2746_);
lean_ctor_set(v___x_2754_, 2, v___f_2753_);
lean_ctor_set(v___x_2754_, 3, v___f_2752_);
lean_ctor_set(v___x_2754_, 4, v___f_2751_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v___f_2747_);
v___x_2756_ = l_StateRefT_x27_instMonad___redArg(v___x_2755_);
v_toApplicative_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v___x_2756_, 1);
lean_dec(v_unused_2809_);
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2808_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_toApplicative_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2808_;
goto v_resetjp_2758_;
}
v___jp_2721_:
{
lean_object* v___x_2723_; lean_object* v_caches_2724_; lean_object* v_typeAnalysis_2725_; lean_object* v_target_2726_; lean_object* v_hypotheses_2727_; uint8_t v_didChange_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2739_; 
v___x_2723_ = lean_st_ref_take(v___y_2722_);
v_caches_2724_ = lean_ctor_get(v___x_2723_, 0);
v_typeAnalysis_2725_ = lean_ctor_get(v___x_2723_, 1);
v_target_2726_ = lean_ctor_get(v___x_2723_, 2);
v_hypotheses_2727_ = lean_ctor_get(v___x_2723_, 3);
v_didChange_2728_ = lean_ctor_get_uint8(v___x_2723_, sizeof(void*)*4);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2730_ = v___x_2723_;
v_isShared_2731_ = v_isSharedCheck_2739_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_hypotheses_2727_);
lean_inc(v_target_2726_);
lean_inc(v_typeAnalysis_2725_);
lean_inc(v_caches_2724_);
lean_dec(v___x_2723_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2739_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = lean_array_push(v_hypotheses_2727_, v_hyp_2708_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 3, v___x_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_caches_2724_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_typeAnalysis_2725_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_target_2726_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v___x_2732_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, sizeof(void*)*4, v_didChange_2728_);
v___x_2734_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = lean_st_ref_put(v___y_2722_, v___x_2734_);
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
}
}
v_resetjp_2758_:
{
lean_object* v_toFunctor_2761_; lean_object* v_toSeq_2762_; lean_object* v_toSeqLeft_2763_; lean_object* v_toSeqRight_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2806_; 
v_toFunctor_2761_ = lean_ctor_get(v_toApplicative_2757_, 0);
v_toSeq_2762_ = lean_ctor_get(v_toApplicative_2757_, 2);
v_toSeqLeft_2763_ = lean_ctor_get(v_toApplicative_2757_, 3);
v_toSeqRight_2764_ = lean_ctor_get(v_toApplicative_2757_, 4);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_toApplicative_2757_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v_toApplicative_2757_, 1);
lean_dec(v_unused_2807_);
v___x_2766_ = v_toApplicative_2757_;
v_isShared_2767_ = v_isSharedCheck_2806_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_toSeqRight_2764_);
lean_inc(v_toSeqLeft_2763_);
lean_inc(v_toSeq_2762_);
lean_inc(v_toFunctor_2761_);
lean_dec(v_toApplicative_2757_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2806_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___f_2770_; lean_object* v___f_2771_; lean_object* v___x_2772_; lean_object* v___f_2773_; lean_object* v___f_2774_; lean_object* v___f_2775_; lean_object* v___x_2777_; 
v___f_2768_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2769_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2761_);
v___f_2770_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2770_, 0, v_toFunctor_2761_);
v___f_2771_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2771_, 0, v_toFunctor_2761_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___f_2770_);
lean_ctor_set(v___x_2772_, 1, v___f_2771_);
v___f_2773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2773_, 0, v_toSeqRight_2764_);
v___f_2774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2774_, 0, v_toSeqLeft_2763_);
v___f_2775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2775_, 0, v_toSeq_2762_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v___f_2773_);
lean_ctor_set(v___x_2766_, 3, v___f_2774_);
lean_ctor_set(v___x_2766_, 2, v___f_2775_);
lean_ctor_set(v___x_2766_, 1, v___f_2768_);
lean_ctor_set(v___x_2766_, 0, v___x_2772_);
v___x_2777_ = v___x_2766_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___f_2768_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v___f_2775_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v___f_2774_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v___f_2773_);
v___x_2777_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2779_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v___f_2769_);
lean_ctor_set(v___x_2759_, 0, v___x_2777_);
v___x_2779_ = v___x_2759_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___f_2769_);
v___x_2779_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v_options_2789_; uint8_t v_hasTrace_2790_; 
v___x_2780_ = l_StateRefT_x27_instMonad___redArg(v___x_2779_);
v___x_2781_ = l_ReaderT_instMonad___redArg(v___x_2780_);
v___x_2782_ = l_StateRefT_x27_instMonad___redArg(v___x_2781_);
v___x_2783_ = l_ReaderT_instMonad___redArg(v___x_2782_);
v___x_2784_ = l_ReaderT_instMonad___redArg(v___x_2783_);
v___x_2785_ = l_StateRefT_x27_instMonad___redArg(v___x_2784_);
v___x_2786_ = l_ReaderT_instMonad___redArg(v___x_2785_);
v___x_2787_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2788_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_options_2789_ = lean_ctor_get(v_a_2718_, 1);
v_hasTrace_2790_ = lean_ctor_get_uint8(v_options_2789_, sizeof(void*)*1);
if (v_hasTrace_2790_ == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_object* v_toCold_2791_; lean_object* v_toMonadRef_2792_; lean_object* v_inheritedTraceOptions_2793_; lean_object* v_cls_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v_toCold_2791_ = lean_ctor_get(v_a_2718_, 0);
v_toMonadRef_2792_ = lean_ctor_get(v___x_2788_, 0);
v_inheritedTraceOptions_2793_ = lean_ctor_get(v_toCold_2791_, 4);
v_cls_2794_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2795_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2793_, v_options_2789_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_object* v_type_2797_; lean_object* v___f_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_5268__overap_2802_; lean_object* v___x_2803_; 
v_type_2797_ = lean_ctor_get(v_hyp_2708_, 1);
v___f_2798_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_2799_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_2797_);
v___x_2800_ = l_Lean_MessageData_ofExpr(v_type_2797_);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
lean_inc_ref(v_toMonadRef_2792_);
v___x_5268__overap_2802_ = l_Lean_addTrace___redArg(v___x_2786_, v___x_2787_, v_toMonadRef_2792_, v___f_2798_, v_cls_2794_, v___x_2801_);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
lean_inc(v_a_2715_);
lean_inc_ref(v_a_2714_);
lean_inc(v_a_2713_);
lean_inc_ref(v_a_2712_);
lean_inc(v_a_2711_);
lean_inc(v_a_2710_);
lean_inc_ref(v_a_2709_);
v___x_2803_ = lean_apply_12(v___x_5268__overap_2802_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, lean_box(0));
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_dec_ref_known(v___x_2803_, 1);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_dec_ref(v_hyp_2708_);
return v___x_2803_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v_toMonadRef_2826_, lean_object* v___f_2827_, lean_object* v_x_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_options_2845_; uint8_t v_hasTrace_2846_; 
v_options_2845_ = lean_ctor_get(v___y_2839_, 1);
v_hasTrace_2846_ = lean_ctor_get_uint8(v_options_2845_, sizeof(void*)*1);
if (v_hasTrace_2846_ == 0)
{
lean_dec_ref(v___y_2829_);
lean_dec(v___f_2827_);
lean_dec_ref(v_toMonadRef_2826_);
lean_dec_ref(v___x_2825_);
lean_dec_ref(v___x_2824_);
goto v___jp_2842_;
}
else
{
lean_object* v_toCold_2847_; lean_object* v_inheritedTraceOptions_2848_; lean_object* v_cls_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_toCold_2847_ = lean_ctor_get(v___y_2839_, 0);
v_inheritedTraceOptions_2848_ = lean_ctor_get(v_toCold_2847_, 4);
v_cls_2849_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2850_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2851_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2848_, v_options_2845_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_dec_ref(v___y_2829_);
lean_dec(v___f_2827_);
lean_dec_ref(v_toMonadRef_2826_);
lean_dec_ref(v___x_2825_);
lean_dec_ref(v___x_2824_);
goto v___jp_2842_;
}
else
{
lean_object* v_type_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_6309__overap_2856_; lean_object* v___x_2857_; 
v_type_2852_ = lean_ctor_get(v___y_2829_, 1);
lean_inc_ref(v_type_2852_);
lean_dec_ref(v___y_2829_);
v___x_2853_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2854_ = l_Lean_MessageData_ofExpr(v_type_2852_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_6309__overap_2856_ = l_Lean_addTrace___redArg(v___x_2824_, v___x_2825_, v_toMonadRef_2826_, v___f_2827_, v_cls_2849_, v___x_2855_);
lean_inc(v___y_2840_);
lean_inc_ref(v___y_2839_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc(v___y_2834_);
lean_inc_ref(v___y_2833_);
lean_inc(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
v___x_2857_ = lean_apply_12(v___x_6309__overap_2856_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, lean_box(0));
return v___x_2857_;
}
}
v___jp_2842_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2858_ = _args[0];
lean_object* v___x_2859_ = _args[1];
lean_object* v_toMonadRef_2860_ = _args[2];
lean_object* v___f_2861_ = _args[3];
lean_object* v_x_2862_ = _args[4];
lean_object* v___y_2863_ = _args[5];
lean_object* v___y_2864_ = _args[6];
lean_object* v___y_2865_ = _args[7];
lean_object* v___y_2866_ = _args[8];
lean_object* v___y_2867_ = _args[9];
lean_object* v___y_2868_ = _args[10];
lean_object* v___y_2869_ = _args[11];
lean_object* v___y_2870_ = _args[12];
lean_object* v___y_2871_ = _args[13];
lean_object* v___y_2872_ = _args[14];
lean_object* v___y_2873_ = _args[15];
lean_object* v___y_2874_ = _args[16];
lean_object* v___y_2875_ = _args[17];
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2858_, v___x_2859_, v_toMonadRef_2860_, v___f_2861_, v_x_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___y_2909_; lean_object* v___x_2910_; lean_object* v_toApplicative_2911_; lean_object* v_toFunctor_2912_; lean_object* v_toSeq_2913_; lean_object* v_toSeqLeft_2914_; lean_object* v_toSeqRight_2915_; lean_object* v___f_2916_; lean_object* v___f_2917_; lean_object* v___f_2918_; lean_object* v___f_2919_; lean_object* v___x_2920_; lean_object* v___f_2921_; lean_object* v___f_2922_; lean_object* v___f_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v_toApplicative_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2979_; 
v___x_2910_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2911_ = lean_ctor_get(v___x_2910_, 0);
v_toFunctor_2912_ = lean_ctor_get(v_toApplicative_2911_, 0);
v_toSeq_2913_ = lean_ctor_get(v_toApplicative_2911_, 2);
v_toSeqLeft_2914_ = lean_ctor_get(v_toApplicative_2911_, 3);
v_toSeqRight_2915_ = lean_ctor_get(v_toApplicative_2911_, 4);
v___f_2916_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2917_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2912_, 2);
v___f_2918_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2918_, 0, v_toFunctor_2912_);
v___f_2919_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2919_, 0, v_toFunctor_2912_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___f_2918_);
lean_ctor_set(v___x_2920_, 1, v___f_2919_);
lean_inc(v_toSeqRight_2915_);
v___f_2921_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2921_, 0, v_toSeqRight_2915_);
lean_inc(v_toSeqLeft_2914_);
v___f_2922_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2922_, 0, v_toSeqLeft_2914_);
lean_inc(v_toSeq_2913_);
v___f_2923_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2923_, 0, v_toSeq_2913_);
v___x_2924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2920_);
lean_ctor_set(v___x_2924_, 1, v___f_2916_);
lean_ctor_set(v___x_2924_, 2, v___f_2923_);
lean_ctor_set(v___x_2924_, 3, v___f_2922_);
lean_ctor_set(v___x_2924_, 4, v___f_2921_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v___f_2917_);
v___x_2926_ = l_StateRefT_x27_instMonad___redArg(v___x_2925_);
v_toApplicative_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v___x_2926_, 1);
lean_dec(v_unused_2980_);
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2979_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_toApplicative_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2979_;
goto v_resetjp_2928_;
}
v___jp_2890_:
{
lean_object* v___x_2891_; lean_object* v_caches_2892_; lean_object* v_typeAnalysis_2893_; lean_object* v_target_2894_; lean_object* v_hypotheses_2895_; uint8_t v_didChange_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2907_; 
v___x_2891_ = lean_st_ref_take(v_a_2879_);
v_caches_2892_ = lean_ctor_get(v___x_2891_, 0);
v_typeAnalysis_2893_ = lean_ctor_get(v___x_2891_, 1);
v_target_2894_ = lean_ctor_get(v___x_2891_, 2);
v_hypotheses_2895_ = lean_ctor_get(v___x_2891_, 3);
v_didChange_2896_ = lean_ctor_get_uint8(v___x_2891_, sizeof(void*)*4);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2898_ = v___x_2891_;
v_isShared_2899_ = v_isSharedCheck_2907_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_hypotheses_2895_);
lean_inc(v_target_2894_);
lean_inc(v_typeAnalysis_2893_);
lean_inc(v_caches_2892_);
lean_dec(v___x_2891_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2907_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = l_Array_append___redArg(v_hypotheses_2895_, v_hyps_2877_);
lean_dec_ref(v_hyps_2877_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 3, v___x_2900_);
v___x_2902_ = v___x_2898_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_caches_2892_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_typeAnalysis_2893_);
lean_ctor_set(v_reuseFailAlloc_2906_, 2, v_target_2894_);
lean_ctor_set(v_reuseFailAlloc_2906_, 3, v___x_2900_);
lean_ctor_set_uint8(v_reuseFailAlloc_2906_, sizeof(void*)*4, v_didChange_2896_);
v___x_2902_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_st_ref_put(v_a_2879_, v___x_2902_);
v___x_2904_ = lean_box(0);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
return v___x_2905_;
}
}
}
v___jp_2908_:
{
if (lean_obj_tag(v___y_2909_) == 0)
{
lean_dec_ref_known(v___y_2909_, 1);
goto v___jp_2890_;
}
else
{
lean_dec_ref(v_hyps_2877_);
return v___y_2909_;
}
}
v_resetjp_2928_:
{
lean_object* v_toFunctor_2931_; lean_object* v_toSeq_2932_; lean_object* v_toSeqLeft_2933_; lean_object* v_toSeqRight_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2977_; 
v_toFunctor_2931_ = lean_ctor_get(v_toApplicative_2927_, 0);
v_toSeq_2932_ = lean_ctor_get(v_toApplicative_2927_, 2);
v_toSeqLeft_2933_ = lean_ctor_get(v_toApplicative_2927_, 3);
v_toSeqRight_2934_ = lean_ctor_get(v_toApplicative_2927_, 4);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_toApplicative_2927_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v_toApplicative_2927_, 1);
lean_dec(v_unused_2978_);
v___x_2936_ = v_toApplicative_2927_;
v_isShared_2937_ = v_isSharedCheck_2977_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_toSeqRight_2934_);
lean_inc(v_toSeqLeft_2933_);
lean_inc(v_toSeq_2932_);
lean_inc(v_toFunctor_2931_);
lean_dec(v_toApplicative_2927_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2977_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___f_2938_; lean_object* v___f_2939_; lean_object* v___f_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___f_2945_; lean_object* v___x_2947_; 
v___f_2938_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2939_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2931_);
v___f_2940_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2940_, 0, v_toFunctor_2931_);
v___f_2941_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2941_, 0, v_toFunctor_2931_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___f_2940_);
lean_ctor_set(v___x_2942_, 1, v___f_2941_);
v___f_2943_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2943_, 0, v_toSeqRight_2934_);
v___f_2944_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2944_, 0, v_toSeqLeft_2933_);
v___f_2945_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2945_, 0, v_toSeq_2932_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 4, v___f_2943_);
lean_ctor_set(v___x_2936_, 3, v___f_2944_);
lean_ctor_set(v___x_2936_, 2, v___f_2945_);
lean_ctor_set(v___x_2936_, 1, v___f_2938_);
lean_ctor_set(v___x_2936_, 0, v___x_2942_);
v___x_2947_ = v___x_2936_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___f_2938_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v___f_2945_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v___f_2944_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v___f_2943_);
v___x_2947_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2949_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___f_2939_);
lean_ctor_set(v___x_2929_, 0, v___x_2947_);
v___x_2949_ = v___x_2929_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___f_2939_);
v___x_2949_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v_toMonadRef_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2950_ = l_StateRefT_x27_instMonad___redArg(v___x_2949_);
v___x_2951_ = l_ReaderT_instMonad___redArg(v___x_2950_);
v___x_2952_ = l_StateRefT_x27_instMonad___redArg(v___x_2951_);
v___x_2953_ = l_ReaderT_instMonad___redArg(v___x_2952_);
v___x_2954_ = l_ReaderT_instMonad___redArg(v___x_2953_);
v___x_2955_ = l_StateRefT_x27_instMonad___redArg(v___x_2954_);
v___x_2956_ = l_ReaderT_instMonad___redArg(v___x_2955_);
v___x_2957_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2958_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_2959_ = lean_ctor_get(v___x_2958_, 0);
v___x_2960_ = lean_unsigned_to_nat(0u);
v___x_2961_ = lean_array_get_size(v_hyps_2877_);
v___x_2962_ = lean_nat_dec_lt(v___x_2960_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v___x_2956_);
goto v___jp_2890_;
}
else
{
lean_object* v___f_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___f_2963_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
lean_inc_ref(v_toMonadRef_2959_);
lean_inc_ref(v___x_2956_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 18, 4);
lean_closure_set(v___f_2964_, 0, v___x_2956_);
lean_closure_set(v___f_2964_, 1, v___x_2957_);
lean_closure_set(v___f_2964_, 2, v_toMonadRef_2959_);
lean_closure_set(v___f_2964_, 3, v___f_2963_);
v___x_2965_ = lean_box(0);
v___x_2966_ = lean_nat_dec_le(v___x_2961_, v___x_2961_);
if (v___x_2966_ == 0)
{
if (v___x_2962_ == 0)
{
lean_dec_ref(v___f_2964_);
lean_dec_ref(v___x_2956_);
goto v___jp_2890_;
}
else
{
size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_5991__overap_2969_; lean_object* v___x_2970_; 
v___x_2967_ = ((size_t)0ULL);
v___x_2968_ = lean_usize_of_nat(v___x_2961_);
lean_inc_ref(v_hyps_2877_);
v___x_5991__overap_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2956_, v___f_2964_, v_hyps_2877_, v___x_2967_, v___x_2968_, v___x_2965_);
lean_inc(v_a_2888_);
lean_inc_ref(v_a_2887_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc_ref(v_a_2883_);
lean_inc(v_a_2882_);
lean_inc_ref(v_a_2881_);
lean_inc(v_a_2880_);
lean_inc(v_a_2879_);
lean_inc_ref(v_a_2878_);
v___x_2970_ = lean_apply_12(v___x_5991__overap_2969_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, lean_box(0));
v___y_2909_ = v___x_2970_;
goto v___jp_2908_;
}
}
else
{
size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_5994__overap_2973_; lean_object* v___x_2974_; 
v___x_2971_ = ((size_t)0ULL);
v___x_2972_ = lean_usize_of_nat(v___x_2961_);
lean_inc_ref(v_hyps_2877_);
v___x_5994__overap_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2956_, v___f_2964_, v_hyps_2877_, v___x_2971_, v___x_2972_, v___x_2965_);
lean_inc(v_a_2888_);
lean_inc_ref(v_a_2887_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc_ref(v_a_2883_);
lean_inc(v_a_2882_);
lean_inc_ref(v_a_2881_);
lean_inc(v_a_2880_);
lean_inc(v_a_2879_);
lean_inc_ref(v_a_2878_);
v___x_2974_ = lean_apply_12(v___x_5994__overap_2973_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, lean_box(0));
v___y_2909_ = v___x_2974_;
goto v___jp_2908_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_2995_){
_start:
{
lean_object* v___x_2997_; lean_object* v_hypotheses_2998_; lean_object* v___x_2999_; 
v___x_2997_ = lean_st_ref_get(v_a_2995_);
v_hypotheses_2998_ = lean_ctor_get(v___x_2997_, 3);
lean_inc_ref(v_hypotheses_2998_);
lean_dec(v___x_2997_);
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_hypotheses_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_3000_);
lean_dec(v_a_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v___x_3015_; lean_object* v_hypotheses_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_st_ref_get(v_a_3004_);
v_hypotheses_3016_ = lean_ctor_get(v___x_3015_, 3);
lean_inc_ref(v_hypotheses_3016_);
lean_dec(v___x_3015_);
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_hypotheses_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; lean_object* v_caches_3045_; lean_object* v_typeAnalysis_3046_; lean_object* v_target_3047_; uint8_t v_didChange_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3058_; 
v___x_3044_ = lean_st_ref_take(v___y_3033_);
v_caches_3045_ = lean_ctor_get(v___x_3044_, 0);
v_typeAnalysis_3046_ = lean_ctor_get(v___x_3044_, 1);
v_target_3047_ = lean_ctor_get(v___x_3044_, 2);
v_didChange_3048_ = lean_ctor_get_uint8(v___x_3044_, sizeof(void*)*4);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; 
v_unused_3059_ = lean_ctor_get(v___x_3044_, 3);
lean_dec(v_unused_3059_);
v___x_3050_ = v___x_3044_;
v_isShared_3051_ = v_isSharedCheck_3058_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_target_3047_);
lean_inc(v_typeAnalysis_3046_);
lean_inc(v_caches_3045_);
lean_dec(v___x_3044_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3058_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 3, v_hyps_3031_);
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_caches_3045_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_typeAnalysis_3046_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v_target_3047_);
lean_ctor_set(v_reuseFailAlloc_3057_, 3, v_hyps_3031_);
lean_ctor_set_uint8(v_reuseFailAlloc_3057_, sizeof(void*)*4, v_didChange_3048_);
v___x_3053_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = lean_st_ref_put(v___y_3033_, v___x_3053_);
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3074_, lean_object* v_hyps_3075_){
_start:
{
lean_object* v___f_3076_; lean_object* v___x_3077_; 
v___f_3076_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3076_, 0, v_hyps_3075_);
v___x_3077_ = lean_apply_2(v_inst_3074_, lean_box(0), v___f_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; lean_object* v_caches_3091_; lean_object* v_typeAnalysis_3092_; lean_object* v_target_3093_; uint8_t v_didChange_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3105_; 
v___x_3090_ = lean_st_ref_take(v___y_3079_);
v_caches_3091_ = lean_ctor_get(v___x_3090_, 0);
v_typeAnalysis_3092_ = lean_ctor_get(v___x_3090_, 1);
v_target_3093_ = lean_ctor_get(v___x_3090_, 2);
v_didChange_3094_ = lean_ctor_get_uint8(v___x_3090_, sizeof(void*)*4);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3105_ == 0)
{
lean_object* v_unused_3106_; 
v_unused_3106_ = lean_ctor_get(v___x_3090_, 3);
lean_dec(v_unused_3106_);
v___x_3096_ = v___x_3090_;
v_isShared_3097_ = v_isSharedCheck_3105_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_target_3093_);
lean_inc(v_typeAnalysis_3092_);
lean_inc(v_caches_3091_);
lean_dec(v___x_3090_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3105_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3098_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 3, v___x_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_caches_3091_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_typeAnalysis_3092_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_target_3093_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v___x_3098_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*4, v_didChange_3094_);
v___x_3100_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_st_ref_put(v___y_3079_, v___x_3100_);
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3120_, lean_object* v_cls_3121_, lean_object* v_____do__lift_3122_, lean_object* v_____do__lift_3123_){
_start:
{
uint8_t v_hasTrace_3124_; 
v_hasTrace_3124_ = lean_ctor_get_uint8(v_____do__lift_3123_, sizeof(void*)*1);
if (v_hasTrace_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec(v_cls_3121_);
v___x_3125_ = lean_box(v_hasTrace_3124_);
v___x_3126_ = lean_apply_2(v_toPure_3120_, lean_box(0), v___x_3125_);
return v___x_3126_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3127_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3128_ = l_Lean_Name_append(v___x_3127_, v_cls_3121_);
v___x_3129_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3122_, v_____do__lift_3123_, v___x_3128_);
lean_dec(v___x_3128_);
v___x_3130_ = lean_box(v___x_3129_);
v___x_3131_ = lean_apply_2(v_toPure_3120_, lean_box(0), v___x_3130_);
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3132_, lean_object* v_cls_3133_, lean_object* v_____do__lift_3134_, lean_object* v_____do__lift_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3132_, v_cls_3133_, v_____do__lift_3134_, v_____do__lift_3135_);
lean_dec_ref(v_____do__lift_3135_);
lean_dec_ref(v_____do__lift_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_toPure_3137_, lean_object* v_cls_3138_, lean_object* v_toBind_3139_, lean_object* v_inst_3140_, lean_object* v_____do__lift_3141_){
_start:
{
lean_object* v___f_3142_; lean_object* v___x_3143_; 
v___f_3142_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3142_, 0, v_toPure_3137_);
lean_closure_set(v___f_3142_, 1, v_cls_3138_);
lean_closure_set(v___f_3142_, 2, v_____do__lift_3141_);
v___x_3143_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v_inst_3140_, v___f_3142_);
return v___x_3143_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3146_ = l_Lean_stringToMessageData(v___x_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3147_, lean_object* v_a_3148_, lean_object* v___y_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_cls_3154_, uint8_t v_____do__lift_3155_){
_start:
{
if (v_____do__lift_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec(v_cls_3154_);
lean_dec(v_inst_3153_);
lean_dec_ref(v_inst_3152_);
lean_dec_ref(v_inst_3151_);
lean_dec_ref(v_inst_3150_);
lean_dec_ref(v___y_3149_);
lean_dec_ref(v_a_3148_);
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_apply_2(v_toPure_3147_, lean_box(0), v___x_3156_);
return v___x_3157_;
}
else
{
lean_object* v_type_3158_; lean_object* v_type_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v_toPure_3147_);
v_type_3158_ = lean_ctor_get(v_a_3148_, 1);
lean_inc_ref(v_type_3158_);
lean_dec_ref(v_a_3148_);
v_type_3159_ = lean_ctor_get(v___y_3149_, 1);
lean_inc_ref(v_type_3159_);
lean_dec_ref(v___y_3149_);
v___x_3160_ = l_Lean_MessageData_ofExpr(v_type_3158_);
v___x_3161_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = l_Lean_MessageData_ofExpr(v_type_3159_);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = l_Lean_addTrace___redArg(v_inst_3150_, v_inst_3151_, v_inst_3152_, v_inst_3153_, v_cls_3154_, v___x_3164_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3166_, lean_object* v_a_3167_, lean_object* v___y_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_cls_3173_, lean_object* v_____do__lift_3174_){
_start:
{
uint8_t v_____do__lift_3036__boxed_3175_; lean_object* v_res_3176_; 
v_____do__lift_3036__boxed_3175_ = lean_unbox(v_____do__lift_3174_);
v_res_3176_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3166_, v_a_3167_, v___y_3168_, v_inst_3169_, v_inst_3170_, v_inst_3171_, v_inst_3172_, v_cls_3173_, v_____do__lift_3036__boxed_3175_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3177_, lean_object* v_toPure_3178_, lean_object* v_toBind_3179_, lean_object* v_inst_3180_, lean_object* v_a_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_x_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_getInheritedTraceOptions_3187_; lean_object* v_cls_3188_; lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_getInheritedTraceOptions_3187_ = lean_ctor_get(v_inst_3177_, 2);
lean_inc(v_getInheritedTraceOptions_3187_);
v_cls_3188_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3179_, 2);
lean_inc(v_toPure_3178_);
v___f_3189_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3189_, 0, v_toPure_3178_);
lean_closure_set(v___f_3189_, 1, v_cls_3188_);
lean_closure_set(v___f_3189_, 2, v_toBind_3179_);
lean_closure_set(v___f_3189_, 3, v_inst_3180_);
v___f_3190_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3190_, 0, v_toPure_3178_);
lean_closure_set(v___f_3190_, 1, v_a_3181_);
lean_closure_set(v___f_3190_, 2, v___y_3186_);
lean_closure_set(v___f_3190_, 3, v_inst_3182_);
lean_closure_set(v___f_3190_, 4, v_inst_3177_);
lean_closure_set(v___f_3190_, 5, v_inst_3183_);
lean_closure_set(v___f_3190_, 6, v_inst_3184_);
lean_closure_set(v___f_3190_, 7, v_cls_3188_);
v___x_3191_ = lean_apply_4(v_toBind_3179_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3187_, v___f_3189_);
v___x_3192_ = lean_apply_4(v_toBind_3179_, lean_box(0), lean_box(0), v___x_3191_, v___f_3190_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3193_, lean_object* v_res_3194_, lean_object* v_____r_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_apply_2(v_toPure_3193_, lean_box(0), v_res_3194_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3197_, lean_object* v_toBind_3198_, lean_object* v___f_3199_, lean_object* v_____r_3200_){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3202_ = lean_apply_2(v_inst_3197_, lean_box(0), v___x_3201_);
v___x_3203_ = lean_apply_4(v_toBind_3198_, lean_box(0), lean_box(0), v___x_3202_, v___f_3199_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3204_, lean_object* v_____r_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_apply_1(v___f_3204_, v_____r_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3207_, lean_object* v_type_3208_, lean_object* v_type_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_cls_3214_, lean_object* v_toBind_3215_, lean_object* v___f_3216_, uint8_t v_____do__lift_3217_){
_start:
{
if (v_____do__lift_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec(v___f_3216_);
lean_dec(v_toBind_3215_);
lean_dec(v_cls_3214_);
lean_dec(v_inst_3213_);
lean_dec_ref(v_inst_3212_);
lean_dec_ref(v_inst_3211_);
lean_dec_ref(v_inst_3210_);
lean_dec_ref(v_type_3209_);
lean_dec_ref(v_type_3208_);
v___x_3218_ = lean_box(0);
v___x_3219_ = lean_apply_1(v___f_3207_, v___x_3218_);
return v___x_3219_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_dec(v___f_3207_);
v___x_3220_ = l_Lean_MessageData_ofExpr(v_type_3208_);
v___x_3221_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = l_Lean_MessageData_ofExpr(v_type_3209_);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l_Lean_addTrace___redArg(v_inst_3210_, v_inst_3211_, v_inst_3212_, v_inst_3213_, v_cls_3214_, v___x_3224_);
v___x_3226_ = lean_apply_4(v_toBind_3215_, lean_box(0), lean_box(0), v___x_3225_, v___f_3216_);
return v___x_3226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3227_, lean_object* v_type_3228_, lean_object* v_type_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_cls_3234_, lean_object* v_toBind_3235_, lean_object* v___f_3236_, lean_object* v_____do__lift_3237_){
_start:
{
uint8_t v_____do__lift_3136__boxed_3238_; lean_object* v_res_3239_; 
v_____do__lift_3136__boxed_3238_ = lean_unbox(v_____do__lift_3237_);
v_res_3239_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3227_, v_type_3228_, v_type_3229_, v_inst_3230_, v_inst_3231_, v_inst_3232_, v_inst_3233_, v_cls_3234_, v_toBind_3235_, v___f_3236_, v_____do__lift_3136__boxed_3238_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3240_, lean_object* v_inst_3241_, lean_object* v_toBind_3242_, lean_object* v_inst_3243_, lean_object* v___f_3244_, lean_object* v_a_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v___f_3250_, lean_object* v_res_3251_){
_start:
{
lean_object* v___x_3252_; lean_object* v_zero_3253_; uint8_t v_isZero_3254_; 
v___x_3252_ = lean_array_get_size(v_res_3251_);
v_zero_3253_ = lean_unsigned_to_nat(0u);
v_isZero_3254_ = lean_nat_dec_eq(v___x_3252_, v_zero_3253_);
if (v_isZero_3254_ == 1)
{
lean_object* v___f_3255_; lean_object* v___f_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
lean_dec(v___f_3250_);
lean_dec(v_inst_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec(v_inst_3247_);
lean_dec_ref(v_inst_3246_);
lean_dec_ref(v_a_3245_);
lean_inc_ref(v_res_3251_);
lean_inc(v_toPure_3240_);
v___f_3255_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3255_, 0, v_toPure_3240_);
lean_closure_set(v___f_3255_, 1, v_res_3251_);
lean_inc(v_toBind_3242_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3256_, 0, v_inst_3241_);
lean_closure_set(v___f_3256_, 1, v_toBind_3242_);
lean_closure_set(v___f_3256_, 2, v___f_3255_);
v___x_3257_ = lean_box(0);
v___x_3258_ = lean_nat_dec_lt(v_zero_3253_, v___x_3252_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec_ref(v_res_3251_);
lean_dec(v___f_3244_);
lean_dec_ref(v_inst_3243_);
v___x_3259_ = lean_apply_2(v_toPure_3240_, lean_box(0), v___x_3257_);
v___x_3260_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3259_, v___f_3256_);
return v___x_3260_;
}
else
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_nat_dec_le(v___x_3252_, v___x_3252_);
if (v___x_3261_ == 0)
{
if (v___x_3258_ == 0)
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
lean_dec_ref(v_res_3251_);
lean_dec(v___f_3244_);
lean_dec_ref(v_inst_3243_);
v___x_3262_ = lean_apply_2(v_toPure_3240_, lean_box(0), v___x_3257_);
v___x_3263_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3262_, v___f_3256_);
return v___x_3263_;
}
else
{
size_t v___x_3264_; size_t v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_dec(v_toPure_3240_);
v___x_3264_ = ((size_t)0ULL);
v___x_3265_ = lean_usize_of_nat(v___x_3252_);
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3243_, v___f_3244_, v_res_3251_, v___x_3264_, v___x_3265_, v___x_3257_);
v___x_3267_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3266_, v___f_3256_);
return v___x_3267_;
}
}
else
{
size_t v___x_3268_; size_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec(v_toPure_3240_);
v___x_3268_ = ((size_t)0ULL);
v___x_3269_ = lean_usize_of_nat(v___x_3252_);
v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3243_, v___f_3244_, v_res_3251_, v___x_3268_, v___x_3269_, v___x_3257_);
v___x_3271_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3270_, v___f_3256_);
return v___x_3271_;
}
}
}
else
{
lean_object* v_one_3272_; lean_object* v_n_3273_; uint8_t v_isZero_3274_; 
lean_dec(v___f_3244_);
v_one_3272_ = lean_unsigned_to_nat(1u);
v_n_3273_ = lean_nat_sub(v___x_3252_, v_one_3272_);
v_isZero_3274_ = lean_nat_dec_eq(v_n_3273_, v_zero_3253_);
lean_dec(v_n_3273_);
if (v_isZero_3274_ == 1)
{
lean_object* v_newHyp_3275_; lean_object* v_type_3276_; lean_object* v_type_3277_; uint8_t v___x_3278_; 
lean_dec(v___f_3250_);
v_newHyp_3275_ = lean_array_fget_borrowed(v_res_3251_, v_zero_3253_);
v_type_3276_ = lean_ctor_get(v_newHyp_3275_, 1);
v_type_3277_ = lean_ctor_get(v_a_3245_, 1);
lean_inc_ref(v_type_3277_);
lean_dec_ref(v_a_3245_);
v___x_3278_ = lean_expr_eqv(v_type_3276_, v_type_3277_);
if (v___x_3278_ == 0)
{
lean_object* v_getInheritedTraceOptions_3279_; lean_object* v___f_3280_; lean_object* v___f_3281_; lean_object* v___f_3282_; lean_object* v_cls_3283_; lean_object* v___f_3284_; lean_object* v___f_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_inc_ref(v_type_3276_);
v_getInheritedTraceOptions_3279_ = lean_ctor_get(v_inst_3246_, 2);
lean_inc(v_getInheritedTraceOptions_3279_);
lean_inc(v_toPure_3240_);
v___f_3280_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3280_, 0, v_toPure_3240_);
lean_closure_set(v___f_3280_, 1, v_res_3251_);
lean_inc_n(v_toBind_3242_, 4);
v___f_3281_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3281_, 0, v_inst_3241_);
lean_closure_set(v___f_3281_, 1, v_toBind_3242_);
lean_closure_set(v___f_3281_, 2, v___f_3280_);
lean_inc_ref(v___f_3281_);
v___f_3282_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3282_, 0, v___f_3281_);
v_cls_3283_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3284_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3284_, 0, v_toPure_3240_);
lean_closure_set(v___f_3284_, 1, v_cls_3283_);
lean_closure_set(v___f_3284_, 2, v_toBind_3242_);
lean_closure_set(v___f_3284_, 3, v_inst_3247_);
v___f_3285_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3285_, 0, v___f_3281_);
lean_closure_set(v___f_3285_, 1, v_type_3277_);
lean_closure_set(v___f_3285_, 2, v_type_3276_);
lean_closure_set(v___f_3285_, 3, v_inst_3243_);
lean_closure_set(v___f_3285_, 4, v_inst_3246_);
lean_closure_set(v___f_3285_, 5, v_inst_3248_);
lean_closure_set(v___f_3285_, 6, v_inst_3249_);
lean_closure_set(v___f_3285_, 7, v_cls_3283_);
lean_closure_set(v___f_3285_, 8, v_toBind_3242_);
lean_closure_set(v___f_3285_, 9, v___f_3282_);
v___x_3286_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3279_, v___f_3284_);
v___x_3287_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3286_, v___f_3285_);
return v___x_3287_;
}
else
{
lean_object* v___x_3288_; 
lean_dec_ref(v_type_3277_);
lean_dec(v_inst_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec(v_inst_3247_);
lean_dec_ref(v_inst_3246_);
lean_dec_ref(v_inst_3243_);
lean_dec(v_toBind_3242_);
lean_dec(v_inst_3241_);
v___x_3288_ = lean_apply_2(v_toPure_3240_, lean_box(0), v_res_3251_);
return v___x_3288_;
}
}
else
{
lean_object* v___f_3289_; lean_object* v___f_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
lean_dec(v_inst_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec(v_inst_3247_);
lean_dec_ref(v_inst_3246_);
lean_dec_ref(v_a_3245_);
lean_inc_ref(v_res_3251_);
lean_inc(v_toPure_3240_);
v___f_3289_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3289_, 0, v_toPure_3240_);
lean_closure_set(v___f_3289_, 1, v_res_3251_);
lean_inc(v_toBind_3242_);
v___f_3290_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3290_, 0, v_inst_3241_);
lean_closure_set(v___f_3290_, 1, v_toBind_3242_);
lean_closure_set(v___f_3290_, 2, v___f_3289_);
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_nat_dec_lt(v_zero_3253_, v___x_3252_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec_ref(v_res_3251_);
lean_dec(v___f_3250_);
lean_dec_ref(v_inst_3243_);
v___x_3293_ = lean_apply_2(v_toPure_3240_, lean_box(0), v___x_3291_);
v___x_3294_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3293_, v___f_3290_);
return v___x_3294_;
}
else
{
uint8_t v___x_3295_; 
v___x_3295_ = lean_nat_dec_le(v___x_3252_, v___x_3252_);
if (v___x_3295_ == 0)
{
if (v___x_3292_ == 0)
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_dec_ref(v_res_3251_);
lean_dec(v___f_3250_);
lean_dec_ref(v_inst_3243_);
v___x_3296_ = lean_apply_2(v_toPure_3240_, lean_box(0), v___x_3291_);
v___x_3297_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3296_, v___f_3290_);
return v___x_3297_;
}
else
{
size_t v___x_3298_; size_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec(v_toPure_3240_);
v___x_3298_ = ((size_t)0ULL);
v___x_3299_ = lean_usize_of_nat(v___x_3252_);
v___x_3300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3243_, v___f_3250_, v_res_3251_, v___x_3298_, v___x_3299_, v___x_3291_);
v___x_3301_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3300_, v___f_3290_);
return v___x_3301_;
}
}
else
{
size_t v___x_3302_; size_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec(v_toPure_3240_);
v___x_3302_ = ((size_t)0ULL);
v___x_3303_ = lean_usize_of_nat(v___x_3252_);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3243_, v___f_3250_, v_res_3251_, v___x_3302_, v___x_3303_, v___x_3291_);
v___x_3305_ = lean_apply_4(v_toBind_3242_, lean_box(0), lean_box(0), v___x_3304_, v___f_3290_);
return v___x_3305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3306_, lean_object* v_toPure_3307_, lean_object* v_____do__lift_3308_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = l_Array_append___redArg(v_bs_3306_, v_____do__lift_3308_);
v___x_3310_ = lean_apply_2(v_toPure_3307_, lean_box(0), v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3311_, lean_object* v_toPure_3312_, lean_object* v_____do__lift_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3311_, v_toPure_3312_, v_____do__lift_3313_);
lean_dec_ref(v_____do__lift_3313_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3315_, lean_object* v_toPure_3316_, lean_object* v_toBind_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_f_3323_, lean_object* v_bs_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___f_3326_; lean_object* v___f_3327_; lean_object* v___f_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_inc(v_inst_3321_);
lean_inc_ref(v_inst_3320_);
lean_inc_ref(v_inst_3319_);
lean_inc_ref_n(v_a_3325_, 2);
lean_inc(v_inst_3318_);
lean_inc_n(v_toBind_3317_, 3);
lean_inc_n(v_toPure_3316_, 2);
lean_inc_ref(v_inst_3315_);
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3326_, 0, v_inst_3315_);
lean_closure_set(v___f_3326_, 1, v_toPure_3316_);
lean_closure_set(v___f_3326_, 2, v_toBind_3317_);
lean_closure_set(v___f_3326_, 3, v_inst_3318_);
lean_closure_set(v___f_3326_, 4, v_a_3325_);
lean_closure_set(v___f_3326_, 5, v_inst_3319_);
lean_closure_set(v___f_3326_, 6, v_inst_3320_);
lean_closure_set(v___f_3326_, 7, v_inst_3321_);
lean_inc_ref(v___f_3326_);
v___f_3327_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3327_, 0, v_toPure_3316_);
lean_closure_set(v___f_3327_, 1, v_inst_3322_);
lean_closure_set(v___f_3327_, 2, v_toBind_3317_);
lean_closure_set(v___f_3327_, 3, v_inst_3319_);
lean_closure_set(v___f_3327_, 4, v___f_3326_);
lean_closure_set(v___f_3327_, 5, v_a_3325_);
lean_closure_set(v___f_3327_, 6, v_inst_3315_);
lean_closure_set(v___f_3327_, 7, v_inst_3318_);
lean_closure_set(v___f_3327_, 8, v_inst_3320_);
lean_closure_set(v___f_3327_, 9, v_inst_3321_);
lean_closure_set(v___f_3327_, 10, v___f_3326_);
v___f_3328_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3328_, 0, v_bs_3324_);
lean_closure_set(v___f_3328_, 1, v_toPure_3316_);
v___x_3329_ = lean_apply_1(v_f_3323_, v_a_3325_);
v___x_3330_ = lean_apply_4(v_toBind_3317_, lean_box(0), lean_box(0), v___x_3329_, v___f_3327_);
v___x_3331_ = lean_apply_4(v_toBind_3317_, lean_box(0), lean_box(0), v___x_3330_, v___f_3328_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3334_, lean_object* v_toPure_3335_, lean_object* v_toBind_3336_, lean_object* v___f_3337_, lean_object* v_inst_3338_, lean_object* v___f_3339_, lean_object* v_____r_3340_){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v___x_3341_ = lean_unsigned_to_nat(0u);
v___x_3342_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3343_ = lean_array_get_size(v_hyps_3334_);
v___x_3344_ = lean_nat_dec_lt(v___x_3341_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec(v___f_3339_);
lean_dec_ref(v_inst_3338_);
lean_dec_ref(v_hyps_3334_);
v___x_3345_ = lean_apply_2(v_toPure_3335_, lean_box(0), v___x_3342_);
v___x_3346_ = lean_apply_4(v_toBind_3336_, lean_box(0), lean_box(0), v___x_3345_, v___f_3337_);
return v___x_3346_;
}
else
{
size_t v___x_3347_; size_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec(v_toPure_3335_);
v___x_3347_ = ((size_t)0ULL);
v___x_3348_ = lean_usize_of_nat(v___x_3343_);
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3338_, v___f_3339_, v_hyps_3334_, v___x_3347_, v___x_3348_, v___x_3342_);
v___x_3350_ = lean_apply_4(v_toBind_3336_, lean_box(0), lean_box(0), v___x_3349_, v___f_3337_);
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3351_, lean_object* v_toBind_3352_, lean_object* v___f_3353_, lean_object* v_inst_3354_, lean_object* v___f_3355_, lean_object* v_inst_3356_, lean_object* v___f_3357_, lean_object* v_hyps_3358_){
_start:
{
lean_object* v___f_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_inc(v_toBind_3352_);
v___f_3359_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3359_, 0, v_hyps_3358_);
lean_closure_set(v___f_3359_, 1, v_toPure_3351_);
lean_closure_set(v___f_3359_, 2, v_toBind_3352_);
lean_closure_set(v___f_3359_, 3, v___f_3353_);
lean_closure_set(v___f_3359_, 4, v_inst_3354_);
lean_closure_set(v___f_3359_, 5, v___f_3355_);
v___x_3360_ = lean_apply_2(v_inst_3356_, lean_box(0), v___f_3357_);
v___x_3361_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3360_, v___f_3359_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_inst_3365_, lean_object* v_inst_3366_, lean_object* v_inst_3367_, lean_object* v_inst_3368_, lean_object* v_f_3369_){
_start:
{
lean_object* v_toApplicative_3370_; lean_object* v_toBind_3371_; lean_object* v_toPure_3372_; lean_object* v___f_3373_; lean_object* v___f_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___f_3377_; lean_object* v___f_3378_; lean_object* v___x_3379_; 
v_toApplicative_3370_ = lean_ctor_get(v_inst_3363_, 0);
v_toBind_3371_ = lean_ctor_get(v_inst_3363_, 1);
lean_inc_n(v_toBind_3371_, 3);
v_toPure_3372_ = lean_ctor_get(v_toApplicative_3370_, 1);
lean_inc_n(v_toPure_3372_, 2);
lean_inc_n(v_inst_3368_, 3);
v___f_3373_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3373_, 0, v_inst_3368_);
v___f_3374_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3375_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3376_ = lean_apply_2(v_inst_3368_, lean_box(0), v___x_3375_);
lean_inc_ref(v_inst_3363_);
v___f_3377_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3377_, 0, v_inst_3364_);
lean_closure_set(v___f_3377_, 1, v_toPure_3372_);
lean_closure_set(v___f_3377_, 2, v_toBind_3371_);
lean_closure_set(v___f_3377_, 3, v_inst_3365_);
lean_closure_set(v___f_3377_, 4, v_inst_3363_);
lean_closure_set(v___f_3377_, 5, v_inst_3367_);
lean_closure_set(v___f_3377_, 6, v_inst_3366_);
lean_closure_set(v___f_3377_, 7, v_inst_3368_);
lean_closure_set(v___f_3377_, 8, v_f_3369_);
v___f_3378_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3378_, 0, v_toPure_3372_);
lean_closure_set(v___f_3378_, 1, v_toBind_3371_);
lean_closure_set(v___f_3378_, 2, v___f_3373_);
lean_closure_set(v___f_3378_, 3, v_inst_3363_);
lean_closure_set(v___f_3378_, 4, v___f_3377_);
lean_closure_set(v___f_3378_, 5, v_inst_3368_);
lean_closure_set(v___f_3378_, 6, v___f_3374_);
v___x_3379_ = lean_apply_4(v_toBind_3371_, lean_box(0), lean_box(0), v___x_3376_, v___f_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_inst_3383_, lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_f_3387_){
_start:
{
lean_object* v_toApplicative_3388_; lean_object* v_toBind_3389_; lean_object* v_toPure_3390_; lean_object* v___f_3391_; lean_object* v___f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___f_3395_; lean_object* v___f_3396_; lean_object* v___x_3397_; 
v_toApplicative_3388_ = lean_ctor_get(v_inst_3381_, 0);
v_toBind_3389_ = lean_ctor_get(v_inst_3381_, 1);
lean_inc_n(v_toBind_3389_, 3);
v_toPure_3390_ = lean_ctor_get(v_toApplicative_3388_, 1);
lean_inc_n(v_toPure_3390_, 2);
lean_inc_n(v_inst_3386_, 3);
v___f_3391_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3391_, 0, v_inst_3386_);
v___f_3392_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3393_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3394_ = lean_apply_2(v_inst_3386_, lean_box(0), v___x_3393_);
lean_inc_ref(v_inst_3381_);
v___f_3395_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3395_, 0, v_inst_3382_);
lean_closure_set(v___f_3395_, 1, v_toPure_3390_);
lean_closure_set(v___f_3395_, 2, v_toBind_3389_);
lean_closure_set(v___f_3395_, 3, v_inst_3383_);
lean_closure_set(v___f_3395_, 4, v_inst_3381_);
lean_closure_set(v___f_3395_, 5, v_inst_3385_);
lean_closure_set(v___f_3395_, 6, v_inst_3384_);
lean_closure_set(v___f_3395_, 7, v_inst_3386_);
lean_closure_set(v___f_3395_, 8, v_f_3387_);
v___f_3396_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3396_, 0, v_toPure_3390_);
lean_closure_set(v___f_3396_, 1, v_toBind_3389_);
lean_closure_set(v___f_3396_, 2, v___f_3391_);
lean_closure_set(v___f_3396_, 3, v_inst_3381_);
lean_closure_set(v___f_3396_, 4, v___f_3395_);
lean_closure_set(v___f_3396_, 5, v_inst_3386_);
lean_closure_set(v___f_3396_, 6, v___f_3392_);
v___x_3397_ = lean_apply_4(v_toBind_3389_, lean_box(0), lean_box(0), v___x_3394_, v___f_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3398_, lean_object* v_____r_3399_){
_start:
{
uint8_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = 0;
v___x_3401_ = lean_box(v___x_3400_);
v___x_3402_ = lean_apply_2(v_toPure_3398_, lean_box(0), v___x_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_snd_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v___x_3416_; lean_object* v_caches_3417_; lean_object* v_typeAnalysis_3418_; lean_object* v_target_3419_; uint8_t v_didChange_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3430_; 
v___x_3416_ = lean_st_ref_take(v___y_3405_);
v_caches_3417_ = lean_ctor_get(v___x_3416_, 0);
v_typeAnalysis_3418_ = lean_ctor_get(v___x_3416_, 1);
v_target_3419_ = lean_ctor_get(v___x_3416_, 2);
v_didChange_3420_ = lean_ctor_get_uint8(v___x_3416_, sizeof(void*)*4);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3430_ == 0)
{
lean_object* v_unused_3431_; 
v_unused_3431_ = lean_ctor_get(v___x_3416_, 3);
lean_dec(v_unused_3431_);
v___x_3422_ = v___x_3416_;
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_target_3419_);
lean_inc(v_typeAnalysis_3418_);
lean_inc(v_caches_3417_);
lean_dec(v___x_3416_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 3, v_snd_3403_);
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_caches_3417_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v_typeAnalysis_3418_);
lean_ctor_set(v_reuseFailAlloc_3429_, 2, v_target_3419_);
lean_ctor_set(v_reuseFailAlloc_3429_, 3, v_snd_3403_);
lean_ctor_set_uint8(v_reuseFailAlloc_3429_, sizeof(void*)*4, v_didChange_3420_);
v___x_3425_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3426_ = lean_st_ref_put(v___y_3405_, v___x_3425_);
v___x_3427_ = lean_box(0);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
return v___x_3428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed(lean_object* v_snd_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(v_snd_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_inst_3446_, lean_object* v_toBind_3447_, lean_object* v___f_3448_, lean_object* v_toPure_3449_, lean_object* v_____s_3450_){
_start:
{
lean_object* v_fst_3451_; 
v_fst_3451_ = lean_ctor_get(v_____s_3450_, 0);
if (lean_obj_tag(v_fst_3451_) == 0)
{
lean_object* v_snd_3452_; lean_object* v___f_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec(v_toPure_3449_);
v_snd_3452_ = lean_ctor_get(v_____s_3450_, 1);
lean_inc(v_snd_3452_);
lean_dec_ref(v_____s_3450_);
v___f_3453_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_3453_, 0, v_snd_3452_);
v___x_3454_ = lean_apply_2(v_inst_3446_, lean_box(0), v___f_3453_);
v___x_3455_ = lean_apply_4(v_toBind_3447_, lean_box(0), lean_box(0), v___x_3454_, v___f_3448_);
return v___x_3455_;
}
else
{
lean_object* v_val_3456_; lean_object* v___x_3457_; 
lean_inc_ref(v_fst_3451_);
lean_dec_ref(v_____s_3450_);
lean_dec(v___f_3448_);
lean_dec(v_toBind_3447_);
lean_dec(v_inst_3446_);
v_val_3456_ = lean_ctor_get(v_fst_3451_, 0);
lean_inc(v_val_3456_);
lean_dec_ref_known(v_fst_3451_, 1);
v___x_3457_ = lean_apply_2(v_toPure_3449_, lean_box(0), v_val_3456_);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_toPure_3458_, lean_object* v_____do__lift_3459_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_apply_2(v_toPure_3458_, lean_box(0), v_____do__lift_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3461_, lean_object* v_next_3462_, lean_object* v_G_3463_, lean_object* v_____do__lift_3464_){
_start:
{
if (lean_obj_tag(v_____do__lift_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3466_; 
lean_dec(v_G_3463_);
v_a_3465_ = lean_ctor_get(v_____do__lift_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v_____do__lift_3464_, 1);
v___x_3466_ = lean_apply_2(v_toPure_3461_, lean_box(0), v_a_3465_);
return v___x_3466_;
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec(v_toPure_3461_);
v_a_3467_ = lean_ctor_get(v_____do__lift_3464_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v_____do__lift_3464_, 1);
v___x_3468_ = lean_unsigned_to_nat(1u);
v___x_3469_ = lean_nat_add(v_next_3462_, v___x_3468_);
v___x_3470_ = lean_apply_4(v_G_3463_, v___x_3469_, v_a_3467_, lean_box(0), lean_box(0));
return v___x_3470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3471_, lean_object* v_next_3472_, lean_object* v_G_3473_, lean_object* v_____do__lift_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3471_, v_next_3472_, v_G_3473_, v_____do__lift_3474_);
lean_dec(v_next_3472_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(uint8_t v___x_3476_, lean_object* v_snd_3477_, lean_object* v_toPure_3478_, lean_object* v_____r_3479_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3480_ = lean_box(v___x_3476_);
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v_snd_3477_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
v___x_3484_ = lean_apply_2(v_toPure_3478_, lean_box(0), v___x_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed(lean_object* v___x_3485_, lean_object* v_snd_3486_, lean_object* v_toPure_3487_, lean_object* v_____r_3488_){
_start:
{
uint8_t v___x_1673__boxed_3489_; lean_object* v_res_3490_; 
v___x_1673__boxed_3489_ = lean_unbox(v___x_3485_);
v_res_3490_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_1673__boxed_3489_, v_snd_3486_, v_toPure_3487_, v_____r_3488_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_snd_3491_, lean_object* v_newHyp_3492_, lean_object* v___x_3493_, lean_object* v_toPure_3494_, lean_object* v_____r_3495_){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3496_ = lean_array_push(v_snd_3491_, v_newHyp_3492_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3493_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
v___x_3499_ = lean_apply_2(v_toPure_3494_, lean_box(0), v___x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_toPure_3500_, lean_object* v___x_3501_, lean_object* v_____do__lift_3502_, lean_object* v_____do__lift_3503_){
_start:
{
uint8_t v_hasTrace_3504_; 
v_hasTrace_3504_ = lean_ctor_get_uint8(v_____do__lift_3503_, sizeof(void*)*1);
if (v_hasTrace_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_dec(v___x_3501_);
v___x_3505_ = lean_box(v_hasTrace_3504_);
v___x_3506_ = lean_apply_2(v_toPure_3500_, lean_box(0), v___x_3505_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3507_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3508_ = l_Lean_Name_append(v___x_3507_, v___x_3501_);
v___x_3509_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3502_, v_____do__lift_3503_, v___x_3508_);
lean_dec(v___x_3508_);
v___x_3510_ = lean_box(v___x_3509_);
v___x_3511_ = lean_apply_2(v_toPure_3500_, lean_box(0), v___x_3510_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed(lean_object* v_toPure_3512_, lean_object* v___x_3513_, lean_object* v_____do__lift_3514_, lean_object* v_____do__lift_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(v_toPure_3512_, v___x_3513_, v_____do__lift_3514_, v_____do__lift_3515_);
lean_dec_ref(v_____do__lift_3515_);
lean_dec_ref(v_____do__lift_3514_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v_toPure_3517_, lean_object* v___x_3518_, lean_object* v_toBind_3519_, lean_object* v_inst_3520_, lean_object* v_____do__lift_3521_){
_start:
{
lean_object* v___f_3522_; lean_object* v___x_3523_; 
v___f_3522_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_3522_, 0, v_toPure_3517_);
lean_closure_set(v___f_3522_, 1, v___x_3518_);
lean_closure_set(v___f_3522_, 2, v_____do__lift_3521_);
v___x_3523_ = lean_apply_4(v_toBind_3519_, lean_box(0), lean_box(0), v_inst_3520_, v___f_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object* v___f_3524_, lean_object* v___x_3525_, lean_object* v_type_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_toMonadRef_3529_, lean_object* v_inst_3530_, lean_object* v___x_3531_, lean_object* v_toBind_3532_, lean_object* v___f_3533_, uint8_t v_____do__lift_3534_){
_start:
{
if (v_____do__lift_3534_ == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
lean_dec(v___f_3533_);
lean_dec(v_toBind_3532_);
lean_dec(v___x_3531_);
lean_dec(v_inst_3530_);
lean_dec_ref(v_toMonadRef_3529_);
lean_dec_ref(v_inst_3528_);
lean_dec_ref(v_inst_3527_);
lean_dec_ref(v_type_3526_);
lean_dec_ref(v___x_3525_);
v___x_3535_ = lean_box(0);
v___x_3536_ = lean_apply_1(v___f_3524_, v___x_3535_);
return v___x_3536_;
}
else
{
lean_object* v_type_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v___f_3524_);
v_type_3537_ = lean_ctor_get(v___x_3525_, 1);
lean_inc_ref(v_type_3537_);
lean_dec_ref(v___x_3525_);
v___x_3538_ = l_Lean_MessageData_ofExpr(v_type_3537_);
v___x_3539_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3538_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = l_Lean_MessageData_ofExpr(v_type_3526_);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = l_Lean_addTrace___redArg(v_inst_3527_, v_inst_3528_, v_toMonadRef_3529_, v_inst_3530_, v___x_3531_, v___x_3542_);
v___x_3544_ = lean_apply_4(v_toBind_3532_, lean_box(0), lean_box(0), v___x_3543_, v___f_3533_);
return v___x_3544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___f_3545_, lean_object* v___x_3546_, lean_object* v_type_3547_, lean_object* v_inst_3548_, lean_object* v_inst_3549_, lean_object* v_toMonadRef_3550_, lean_object* v_inst_3551_, lean_object* v___x_3552_, lean_object* v_toBind_3553_, lean_object* v___f_3554_, lean_object* v_____do__lift_3555_){
_start:
{
uint8_t v_____do__lift_1748__boxed_3556_; lean_object* v_res_3557_; 
v_____do__lift_1748__boxed_3556_ = lean_unbox(v_____do__lift_3555_);
v_res_3557_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3545_, v___x_3546_, v_type_3547_, v_inst_3548_, v_inst_3549_, v_toMonadRef_3550_, v_inst_3551_, v___x_3552_, v_toBind_3553_, v___f_3554_, v_____do__lift_1748__boxed_3556_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v___x_3558_, lean_object* v_snd_3559_, lean_object* v___x_3560_, lean_object* v_toPure_3561_, lean_object* v_inst_3562_, lean_object* v_toBind_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_inst_3566_, lean_object* v_toMonadRef_3567_, lean_object* v_inst_3568_, lean_object* v___f_3569_, lean_object* v_newHyp_3570_){
_start:
{
lean_object* v_type_3571_; lean_object* v_value_3572_; uint8_t v___x_3573_; 
v_type_3571_ = lean_ctor_get(v_newHyp_3570_, 1);
v_value_3572_ = lean_ctor_get(v_newHyp_3570_, 2);
lean_inc_ref(v_type_3571_);
v___x_3573_ = l_Lean_Expr_isFalse(v_type_3571_);
if (v___x_3573_ == 0)
{
lean_object* v_type_3574_; lean_object* v___f_3575_; lean_object* v___f_3576_; lean_object* v___f_3577_; lean_object* v___f_3578_; uint8_t v___x_3586_; 
lean_dec(v___f_3569_);
v_type_3574_ = lean_ctor_get(v___x_3558_, 1);
lean_inc(v_toPure_3561_);
lean_inc(v___x_3560_);
lean_inc_ref(v_newHyp_3570_);
lean_inc(v_snd_3559_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3575_, 0, v_snd_3559_);
lean_closure_set(v___f_3575_, 1, v_newHyp_3570_);
lean_closure_set(v___f_3575_, 2, v___x_3560_);
lean_closure_set(v___f_3575_, 3, v_toPure_3561_);
v___f_3576_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3576_, 0, v___f_3575_);
lean_inc(v_toBind_3563_);
v___f_3577_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3577_, 0, v_inst_3562_);
lean_closure_set(v___f_3577_, 1, v_toBind_3563_);
lean_closure_set(v___f_3577_, 2, v___f_3576_);
lean_inc_ref(v___f_3577_);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3578_, 0, v___f_3577_);
v___x_3586_ = lean_expr_eqv(v_type_3574_, v_type_3571_);
if (v___x_3586_ == 0)
{
lean_inc_ref(v_type_3571_);
lean_dec_ref(v_newHyp_3570_);
lean_dec(v___x_3560_);
lean_dec(v_snd_3559_);
goto v___jp_3579_;
}
else
{
if (v___x_3573_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec_ref(v___f_3578_);
lean_dec_ref(v___f_3577_);
lean_dec(v_inst_3568_);
lean_dec_ref(v_toMonadRef_3567_);
lean_dec_ref(v_inst_3566_);
lean_dec(v_inst_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec(v_toBind_3563_);
lean_dec_ref(v___x_3558_);
v___x_3587_ = lean_box(0);
v___x_3588_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3559_, v_newHyp_3570_, v___x_3560_, v_toPure_3561_, v___x_3587_);
return v___x_3588_;
}
else
{
lean_inc_ref(v_type_3571_);
lean_dec_ref(v_newHyp_3570_);
lean_dec(v___x_3560_);
lean_dec(v_snd_3559_);
goto v___jp_3579_;
}
}
v___jp_3579_:
{
lean_object* v_getInheritedTraceOptions_3580_; lean_object* v___x_3581_; lean_object* v___f_3582_; lean_object* v___f_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_getInheritedTraceOptions_3580_ = lean_ctor_get(v_inst_3564_, 2);
lean_inc(v_getInheritedTraceOptions_3580_);
v___x_3581_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3563_, 3);
v___f_3582_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3582_, 0, v_toPure_3561_);
lean_closure_set(v___f_3582_, 1, v___x_3581_);
lean_closure_set(v___f_3582_, 2, v_toBind_3563_);
lean_closure_set(v___f_3582_, 3, v_inst_3565_);
v___f_3583_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3583_, 0, v___f_3577_);
lean_closure_set(v___f_3583_, 1, v___x_3558_);
lean_closure_set(v___f_3583_, 2, v_type_3571_);
lean_closure_set(v___f_3583_, 3, v_inst_3566_);
lean_closure_set(v___f_3583_, 4, v_inst_3564_);
lean_closure_set(v___f_3583_, 5, v_toMonadRef_3567_);
lean_closure_set(v___f_3583_, 6, v_inst_3568_);
lean_closure_set(v___f_3583_, 7, v___x_3581_);
lean_closure_set(v___f_3583_, 8, v_toBind_3563_);
lean_closure_set(v___f_3583_, 9, v___f_3578_);
v___x_3584_ = lean_apply_4(v_toBind_3563_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3580_, v___f_3582_);
v___x_3585_ = lean_apply_4(v_toBind_3563_, lean_box(0), lean_box(0), v___x_3584_, v___f_3583_);
return v___x_3585_;
}
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
lean_inc_ref(v_value_3572_);
lean_dec_ref(v_newHyp_3570_);
lean_dec(v_inst_3568_);
lean_dec_ref(v_toMonadRef_3567_);
lean_dec_ref(v_inst_3566_);
lean_dec(v_inst_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec(v_toPure_3561_);
lean_dec(v___x_3560_);
lean_dec(v_snd_3559_);
lean_dec_ref(v___x_3558_);
v___x_3589_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3589_, 0, v_value_3572_);
v___x_3590_ = lean_apply_2(v_inst_3562_, lean_box(0), v___x_3589_);
v___x_3591_ = lean_apply_4(v_toBind_3563_, lean_box(0), lean_box(0), v___x_3590_, v___f_3569_);
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3592_, lean_object* v_toPure_3593_, lean_object* v_hyps_3594_, lean_object* v___x_3595_, lean_object* v_inst_3596_, lean_object* v_toBind_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_toMonadRef_3601_, lean_object* v_inst_3602_, lean_object* v_f_3603_, lean_object* v___f_3604_, lean_object* v_next_3605_, lean_object* v_acc_3606_, lean_object* v_h_3607_, lean_object* v_G_3608_){
_start:
{
uint8_t v___x_3609_; 
v___x_3609_ = lean_nat_dec_lt(v_next_3605_, v___x_3592_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec(v_G_3608_);
lean_dec(v_next_3605_);
lean_dec(v___f_3604_);
lean_dec(v_f_3603_);
lean_dec(v_inst_3602_);
lean_dec_ref(v_toMonadRef_3601_);
lean_dec_ref(v_inst_3600_);
lean_dec(v_inst_3599_);
lean_dec_ref(v_inst_3598_);
lean_dec(v_toBind_3597_);
lean_dec(v_inst_3596_);
lean_dec(v___x_3595_);
v___x_3610_ = lean_apply_2(v_toPure_3593_, lean_box(0), v_acc_3606_);
return v___x_3610_;
}
else
{
lean_object* v_snd_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; lean_object* v___f_3614_; lean_object* v___x_3615_; lean_object* v___f_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_snd_3611_ = lean_ctor_get(v_acc_3606_, 1);
lean_inc_n(v_snd_3611_, 2);
lean_dec_ref(v_acc_3606_);
lean_inc(v_next_3605_);
lean_inc_n(v_toPure_3593_, 2);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3612_, 0, v_toPure_3593_);
lean_closure_set(v___f_3612_, 1, v_next_3605_);
lean_closure_set(v___f_3612_, 2, v_G_3608_);
v___x_3613_ = lean_box(v___x_3609_);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3614_, 0, v___x_3613_);
lean_closure_set(v___f_3614_, 1, v_snd_3611_);
lean_closure_set(v___f_3614_, 2, v_toPure_3593_);
v___x_3615_ = lean_array_fget_borrowed(v_hyps_3594_, v_next_3605_);
lean_inc_n(v_toBind_3597_, 3);
lean_inc_n(v___x_3615_, 2);
v___f_3616_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9), 13, 12);
lean_closure_set(v___f_3616_, 0, v___x_3615_);
lean_closure_set(v___f_3616_, 1, v_snd_3611_);
lean_closure_set(v___f_3616_, 2, v___x_3595_);
lean_closure_set(v___f_3616_, 3, v_toPure_3593_);
lean_closure_set(v___f_3616_, 4, v_inst_3596_);
lean_closure_set(v___f_3616_, 5, v_toBind_3597_);
lean_closure_set(v___f_3616_, 6, v_inst_3598_);
lean_closure_set(v___f_3616_, 7, v_inst_3599_);
lean_closure_set(v___f_3616_, 8, v_inst_3600_);
lean_closure_set(v___f_3616_, 9, v_toMonadRef_3601_);
lean_closure_set(v___f_3616_, 10, v_inst_3602_);
lean_closure_set(v___f_3616_, 11, v___f_3614_);
v___x_3617_ = lean_apply_2(v_f_3603_, v_next_3605_, v___x_3615_);
v___x_3618_ = lean_apply_4(v_toBind_3597_, lean_box(0), lean_box(0), v___x_3617_, v___f_3616_);
v___x_3619_ = lean_apply_4(v_toBind_3597_, lean_box(0), lean_box(0), v___x_3618_, v___f_3604_);
v___x_3620_ = lean_apply_4(v_toBind_3597_, lean_box(0), lean_box(0), v___x_3619_, v___f_3612_);
return v___x_3620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3621_ = _args[0];
lean_object* v_toPure_3622_ = _args[1];
lean_object* v_hyps_3623_ = _args[2];
lean_object* v___x_3624_ = _args[3];
lean_object* v_inst_3625_ = _args[4];
lean_object* v_toBind_3626_ = _args[5];
lean_object* v_inst_3627_ = _args[6];
lean_object* v_inst_3628_ = _args[7];
lean_object* v_inst_3629_ = _args[8];
lean_object* v_toMonadRef_3630_ = _args[9];
lean_object* v_inst_3631_ = _args[10];
lean_object* v_f_3632_ = _args[11];
lean_object* v___f_3633_ = _args[12];
lean_object* v_next_3634_ = _args[13];
lean_object* v_acc_3635_ = _args[14];
lean_object* v_h_3636_ = _args[15];
lean_object* v_G_3637_ = _args[16];
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3621_, v_toPure_3622_, v_hyps_3623_, v___x_3624_, v_inst_3625_, v_toBind_3626_, v_inst_3627_, v_inst_3628_, v_inst_3629_, v_toMonadRef_3630_, v_inst_3631_, v_f_3632_, v___f_3633_, v_next_3634_, v_acc_3635_, v_h_3636_, v_G_3637_);
lean_dec_ref(v_hyps_3623_);
lean_dec(v___x_3621_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3639_, lean_object* v_inst_3640_, lean_object* v_toBind_3641_, lean_object* v_inst_3642_, lean_object* v_inst_3643_, lean_object* v_inst_3644_, lean_object* v_toMonadRef_3645_, lean_object* v_inst_3646_, lean_object* v_f_3647_, lean_object* v___f_3648_, lean_object* v___f_3649_, lean_object* v_hyps_3650_){
_start:
{
lean_object* v___x_3651_; lean_object* v_newHyps_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___f_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3651_ = lean_array_get_size(v_hyps_3650_);
v_newHyps_3652_ = lean_mk_empty_array_with_capacity(v___x_3651_);
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = lean_box(0);
lean_inc(v_toBind_3641_);
v___f_3655_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3655_, 0, v___x_3651_);
lean_closure_set(v___f_3655_, 1, v_toPure_3639_);
lean_closure_set(v___f_3655_, 2, v_hyps_3650_);
lean_closure_set(v___f_3655_, 3, v___x_3654_);
lean_closure_set(v___f_3655_, 4, v_inst_3640_);
lean_closure_set(v___f_3655_, 5, v_toBind_3641_);
lean_closure_set(v___f_3655_, 6, v_inst_3642_);
lean_closure_set(v___f_3655_, 7, v_inst_3643_);
lean_closure_set(v___f_3655_, 8, v_inst_3644_);
lean_closure_set(v___f_3655_, 9, v_toMonadRef_3645_);
lean_closure_set(v___f_3655_, 10, v_inst_3646_);
lean_closure_set(v___f_3655_, 11, v_f_3647_);
lean_closure_set(v___f_3655_, 12, v___f_3648_);
v___x_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v_newHyps_3652_);
v___x_3657_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3655_, v___x_3653_, v___x_3656_, lean_box(0));
v___x_3658_ = lean_apply_4(v_toBind_3641_, lean_box(0), lean_box(0), v___x_3657_, v___f_3649_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3659_, lean_object* v_inst_3660_, lean_object* v_inst_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_inst_3664_, lean_object* v_f_3665_){
_start:
{
lean_object* v_toApplicative_3666_; lean_object* v_toBind_3667_; lean_object* v_toPure_3668_; lean_object* v_toMonadRef_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___f_3672_; lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___x_3676_; 
v_toApplicative_3666_ = lean_ctor_get(v_inst_3659_, 0);
v_toBind_3667_ = lean_ctor_get(v_inst_3659_, 1);
lean_inc_n(v_toBind_3667_, 3);
v_toPure_3668_ = lean_ctor_get(v_toApplicative_3666_, 1);
lean_inc_n(v_toPure_3668_, 4);
v_toMonadRef_3669_ = lean_ctor_get(v_inst_3661_, 1);
lean_inc_ref(v_toMonadRef_3669_);
lean_dec_ref(v_inst_3661_);
v___x_3670_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3660_, 2);
v___x_3671_ = lean_apply_2(v_inst_3660_, lean_box(0), v___x_3670_);
v___f_3672_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3672_, 0, v_toPure_3668_);
v___f_3673_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3673_, 0, v_inst_3660_);
lean_closure_set(v___f_3673_, 1, v_toBind_3667_);
lean_closure_set(v___f_3673_, 2, v___f_3672_);
lean_closure_set(v___f_3673_, 3, v_toPure_3668_);
v___f_3674_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3674_, 0, v_toPure_3668_);
v___f_3675_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3675_, 0, v_toPure_3668_);
lean_closure_set(v___f_3675_, 1, v_inst_3660_);
lean_closure_set(v___f_3675_, 2, v_toBind_3667_);
lean_closure_set(v___f_3675_, 3, v_inst_3662_);
lean_closure_set(v___f_3675_, 4, v_inst_3663_);
lean_closure_set(v___f_3675_, 5, v_inst_3659_);
lean_closure_set(v___f_3675_, 6, v_toMonadRef_3669_);
lean_closure_set(v___f_3675_, 7, v_inst_3664_);
lean_closure_set(v___f_3675_, 8, v_f_3665_);
lean_closure_set(v___f_3675_, 9, v___f_3674_);
lean_closure_set(v___f_3675_, 10, v___f_3673_);
v___x_3676_ = lean_apply_4(v_toBind_3667_, lean_box(0), lean_box(0), v___x_3671_, v___f_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3677_, lean_object* v_inst_3678_, lean_object* v_inst_3679_, lean_object* v_inst_3680_, lean_object* v_inst_3681_, lean_object* v_inst_3682_, lean_object* v_inst_3683_, lean_object* v_inst_3684_, lean_object* v_inst_3685_, lean_object* v_f_3686_){
_start:
{
lean_object* v_toApplicative_3687_; lean_object* v_toBind_3688_; lean_object* v_toPure_3689_; lean_object* v_toMonadRef_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___x_3697_; 
v_toApplicative_3687_ = lean_ctor_get(v_inst_3678_, 0);
v_toBind_3688_ = lean_ctor_get(v_inst_3678_, 1);
lean_inc_n(v_toBind_3688_, 3);
v_toPure_3689_ = lean_ctor_get(v_toApplicative_3687_, 1);
lean_inc_n(v_toPure_3689_, 4);
v_toMonadRef_3690_ = lean_ctor_get(v_inst_3680_, 1);
lean_inc_ref(v_toMonadRef_3690_);
lean_dec_ref(v_inst_3680_);
v___x_3691_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3679_, 2);
v___x_3692_ = lean_apply_2(v_inst_3679_, lean_box(0), v___x_3691_);
v___f_3693_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3693_, 0, v_toPure_3689_);
v___f_3694_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3694_, 0, v_inst_3679_);
lean_closure_set(v___f_3694_, 1, v_toBind_3688_);
lean_closure_set(v___f_3694_, 2, v___f_3693_);
lean_closure_set(v___f_3694_, 3, v_toPure_3689_);
v___f_3695_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3695_, 0, v_toPure_3689_);
v___f_3696_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3696_, 0, v_toPure_3689_);
lean_closure_set(v___f_3696_, 1, v_inst_3679_);
lean_closure_set(v___f_3696_, 2, v_toBind_3688_);
lean_closure_set(v___f_3696_, 3, v_inst_3682_);
lean_closure_set(v___f_3696_, 4, v_inst_3683_);
lean_closure_set(v___f_3696_, 5, v_inst_3678_);
lean_closure_set(v___f_3696_, 6, v_toMonadRef_3690_);
lean_closure_set(v___f_3696_, 7, v_inst_3684_);
lean_closure_set(v___f_3696_, 8, v_f_3686_);
lean_closure_set(v___f_3696_, 9, v___f_3695_);
lean_closure_set(v___f_3696_, 10, v___f_3694_);
v___x_3697_ = lean_apply_4(v_toBind_3688_, lean_box(0), lean_box(0), v___x_3692_, v___f_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3698_, lean_object* v_inst_3699_, lean_object* v_inst_3700_, lean_object* v_inst_3701_, lean_object* v_inst_3702_, lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_inst_3705_, lean_object* v_inst_3706_, lean_object* v_f_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3698_, v_inst_3699_, v_inst_3700_, v_inst_3701_, v_inst_3702_, v_inst_3703_, v_inst_3704_, v_inst_3705_, v_inst_3706_, v_f_3707_);
lean_dec_ref(v_inst_3706_);
lean_dec_ref(v_inst_3702_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3709_, lean_object* v_snd_3710_, lean_object* v___x_3711_, lean_object* v_toPure_3712_, lean_object* v_inst_3713_, lean_object* v_toBind_3714_, lean_object* v_inst_3715_, lean_object* v_inst_3716_, lean_object* v_toMonadRef_3717_, lean_object* v_inst_3718_, lean_object* v_inst_3719_, lean_object* v___f_3720_, lean_object* v_newHyp_3721_){
_start:
{
lean_object* v_type_3722_; lean_object* v_value_3723_; uint8_t v___x_3724_; 
v_type_3722_ = lean_ctor_get(v_newHyp_3721_, 1);
v_value_3723_ = lean_ctor_get(v_newHyp_3721_, 2);
lean_inc_ref(v_type_3722_);
v___x_3724_ = l_Lean_Expr_isFalse(v_type_3722_);
if (v___x_3724_ == 0)
{
lean_object* v_type_3725_; lean_object* v___f_3726_; lean_object* v___f_3727_; lean_object* v___f_3728_; lean_object* v___f_3729_; uint8_t v___x_3737_; 
lean_dec(v___f_3720_);
v_type_3725_ = lean_ctor_get(v___x_3709_, 1);
lean_inc(v_toPure_3712_);
lean_inc(v___x_3711_);
lean_inc_ref(v_newHyp_3721_);
lean_inc(v_snd_3710_);
v___f_3726_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3726_, 0, v_snd_3710_);
lean_closure_set(v___f_3726_, 1, v_newHyp_3721_);
lean_closure_set(v___f_3726_, 2, v___x_3711_);
lean_closure_set(v___f_3726_, 3, v_toPure_3712_);
v___f_3727_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3727_, 0, v___f_3726_);
lean_inc(v_toBind_3714_);
v___f_3728_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3728_, 0, v_inst_3713_);
lean_closure_set(v___f_3728_, 1, v_toBind_3714_);
lean_closure_set(v___f_3728_, 2, v___f_3727_);
lean_inc_ref(v___f_3728_);
v___f_3729_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3729_, 0, v___f_3728_);
v___x_3737_ = lean_expr_eqv(v_type_3725_, v_type_3722_);
if (v___x_3737_ == 0)
{
lean_inc_ref(v_type_3722_);
lean_dec_ref(v_newHyp_3721_);
lean_dec(v___x_3711_);
lean_dec(v_snd_3710_);
goto v___jp_3730_;
}
else
{
if (v___x_3724_ == 0)
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_dec_ref(v___f_3729_);
lean_dec_ref(v___f_3728_);
lean_dec(v_inst_3719_);
lean_dec(v_inst_3718_);
lean_dec_ref(v_toMonadRef_3717_);
lean_dec_ref(v_inst_3716_);
lean_dec_ref(v_inst_3715_);
lean_dec(v_toBind_3714_);
lean_dec_ref(v___x_3709_);
v___x_3738_ = lean_box(0);
v___x_3739_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3710_, v_newHyp_3721_, v___x_3711_, v_toPure_3712_, v___x_3738_);
return v___x_3739_;
}
else
{
lean_inc_ref(v_type_3722_);
lean_dec_ref(v_newHyp_3721_);
lean_dec(v___x_3711_);
lean_dec(v_snd_3710_);
goto v___jp_3730_;
}
}
v___jp_3730_:
{
lean_object* v_getInheritedTraceOptions_3731_; lean_object* v___x_3732_; lean_object* v___f_3733_; lean_object* v___f_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_getInheritedTraceOptions_3731_ = lean_ctor_get(v_inst_3715_, 2);
lean_inc(v_getInheritedTraceOptions_3731_);
v___x_3732_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3714_, 3);
v___f_3733_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3733_, 0, v___f_3728_);
lean_closure_set(v___f_3733_, 1, v___x_3709_);
lean_closure_set(v___f_3733_, 2, v_type_3722_);
lean_closure_set(v___f_3733_, 3, v_inst_3716_);
lean_closure_set(v___f_3733_, 4, v_inst_3715_);
lean_closure_set(v___f_3733_, 5, v_toMonadRef_3717_);
lean_closure_set(v___f_3733_, 6, v_inst_3718_);
lean_closure_set(v___f_3733_, 7, v___x_3732_);
lean_closure_set(v___f_3733_, 8, v_toBind_3714_);
lean_closure_set(v___f_3733_, 9, v___f_3729_);
v___f_3734_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3734_, 0, v_toPure_3712_);
lean_closure_set(v___f_3734_, 1, v___x_3732_);
lean_closure_set(v___f_3734_, 2, v_toBind_3714_);
lean_closure_set(v___f_3734_, 3, v_inst_3719_);
v___x_3735_ = lean_apply_4(v_toBind_3714_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3731_, v___f_3734_);
v___x_3736_ = lean_apply_4(v_toBind_3714_, lean_box(0), lean_box(0), v___x_3735_, v___f_3733_);
return v___x_3736_;
}
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_inc_ref(v_value_3723_);
lean_dec_ref(v_newHyp_3721_);
lean_dec(v_inst_3719_);
lean_dec(v_inst_3718_);
lean_dec_ref(v_toMonadRef_3717_);
lean_dec_ref(v_inst_3716_);
lean_dec_ref(v_inst_3715_);
lean_dec(v_toPure_3712_);
lean_dec(v___x_3711_);
lean_dec(v_snd_3710_);
lean_dec_ref(v___x_3709_);
v___x_3740_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3740_, 0, v_value_3723_);
v___x_3741_ = lean_apply_2(v_inst_3713_, lean_box(0), v___x_3740_);
v___x_3742_ = lean_apply_4(v_toBind_3714_, lean_box(0), lean_box(0), v___x_3741_, v___f_3720_);
return v___x_3742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3743_, lean_object* v_toPure_3744_, lean_object* v_hyps_3745_, lean_object* v___x_3746_, lean_object* v_inst_3747_, lean_object* v_toBind_3748_, lean_object* v_inst_3749_, lean_object* v_inst_3750_, lean_object* v_toMonadRef_3751_, lean_object* v_inst_3752_, lean_object* v_inst_3753_, lean_object* v_f_3754_, lean_object* v___f_3755_, lean_object* v_next_3756_, lean_object* v_acc_3757_, lean_object* v_h_3758_, lean_object* v_G_3759_){
_start:
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_nat_dec_lt(v_next_3756_, v___x_3743_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; 
lean_dec(v_G_3759_);
lean_dec(v_next_3756_);
lean_dec(v___f_3755_);
lean_dec(v_f_3754_);
lean_dec(v_inst_3753_);
lean_dec(v_inst_3752_);
lean_dec_ref(v_toMonadRef_3751_);
lean_dec_ref(v_inst_3750_);
lean_dec_ref(v_inst_3749_);
lean_dec(v_toBind_3748_);
lean_dec(v_inst_3747_);
lean_dec(v___x_3746_);
v___x_3761_ = lean_apply_2(v_toPure_3744_, lean_box(0), v_acc_3757_);
return v___x_3761_;
}
else
{
lean_object* v_snd_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; lean_object* v___f_3765_; lean_object* v___x_3766_; lean_object* v___f_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_snd_3762_ = lean_ctor_get(v_acc_3757_, 1);
lean_inc_n(v_snd_3762_, 2);
lean_dec_ref(v_acc_3757_);
lean_inc(v_next_3756_);
lean_inc_n(v_toPure_3744_, 2);
v___f_3763_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3763_, 0, v_toPure_3744_);
lean_closure_set(v___f_3763_, 1, v_next_3756_);
lean_closure_set(v___f_3763_, 2, v_G_3759_);
v___x_3764_ = lean_box(v___x_3760_);
v___f_3765_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3765_, 0, v___x_3764_);
lean_closure_set(v___f_3765_, 1, v_snd_3762_);
lean_closure_set(v___f_3765_, 2, v_toPure_3744_);
v___x_3766_ = lean_array_fget_borrowed(v_hyps_3745_, v_next_3756_);
lean_dec(v_next_3756_);
lean_inc_n(v_toBind_3748_, 3);
lean_inc_n(v___x_3766_, 2);
v___f_3767_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3767_, 0, v___x_3766_);
lean_closure_set(v___f_3767_, 1, v_snd_3762_);
lean_closure_set(v___f_3767_, 2, v___x_3746_);
lean_closure_set(v___f_3767_, 3, v_toPure_3744_);
lean_closure_set(v___f_3767_, 4, v_inst_3747_);
lean_closure_set(v___f_3767_, 5, v_toBind_3748_);
lean_closure_set(v___f_3767_, 6, v_inst_3749_);
lean_closure_set(v___f_3767_, 7, v_inst_3750_);
lean_closure_set(v___f_3767_, 8, v_toMonadRef_3751_);
lean_closure_set(v___f_3767_, 9, v_inst_3752_);
lean_closure_set(v___f_3767_, 10, v_inst_3753_);
lean_closure_set(v___f_3767_, 11, v___f_3765_);
v___x_3768_ = lean_apply_1(v_f_3754_, v___x_3766_);
v___x_3769_ = lean_apply_4(v_toBind_3748_, lean_box(0), lean_box(0), v___x_3768_, v___f_3767_);
v___x_3770_ = lean_apply_4(v_toBind_3748_, lean_box(0), lean_box(0), v___x_3769_, v___f_3755_);
v___x_3771_ = lean_apply_4(v_toBind_3748_, lean_box(0), lean_box(0), v___x_3770_, v___f_3763_);
return v___x_3771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3772_ = _args[0];
lean_object* v_toPure_3773_ = _args[1];
lean_object* v_hyps_3774_ = _args[2];
lean_object* v___x_3775_ = _args[3];
lean_object* v_inst_3776_ = _args[4];
lean_object* v_toBind_3777_ = _args[5];
lean_object* v_inst_3778_ = _args[6];
lean_object* v_inst_3779_ = _args[7];
lean_object* v_toMonadRef_3780_ = _args[8];
lean_object* v_inst_3781_ = _args[9];
lean_object* v_inst_3782_ = _args[10];
lean_object* v_f_3783_ = _args[11];
lean_object* v___f_3784_ = _args[12];
lean_object* v_next_3785_ = _args[13];
lean_object* v_acc_3786_ = _args[14];
lean_object* v_h_3787_ = _args[15];
lean_object* v_G_3788_ = _args[16];
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3772_, v_toPure_3773_, v_hyps_3774_, v___x_3775_, v_inst_3776_, v_toBind_3777_, v_inst_3778_, v_inst_3779_, v_toMonadRef_3780_, v_inst_3781_, v_inst_3782_, v_f_3783_, v___f_3784_, v_next_3785_, v_acc_3786_, v_h_3787_, v_G_3788_);
lean_dec_ref(v_hyps_3774_);
lean_dec(v___x_3772_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3790_, lean_object* v_inst_3791_, lean_object* v_toBind_3792_, lean_object* v_inst_3793_, lean_object* v_inst_3794_, lean_object* v_toMonadRef_3795_, lean_object* v_inst_3796_, lean_object* v_inst_3797_, lean_object* v_f_3798_, lean_object* v___f_3799_, lean_object* v___f_3800_, lean_object* v_hyps_3801_){
_start:
{
lean_object* v___x_3802_; lean_object* v_newHyps_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___f_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3802_ = lean_array_get_size(v_hyps_3801_);
v_newHyps_3803_ = lean_mk_empty_array_with_capacity(v___x_3802_);
v___x_3804_ = lean_unsigned_to_nat(0u);
v___x_3805_ = lean_box(0);
lean_inc(v_toBind_3792_);
v___f_3806_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3806_, 0, v___x_3802_);
lean_closure_set(v___f_3806_, 1, v_toPure_3790_);
lean_closure_set(v___f_3806_, 2, v_hyps_3801_);
lean_closure_set(v___f_3806_, 3, v___x_3805_);
lean_closure_set(v___f_3806_, 4, v_inst_3791_);
lean_closure_set(v___f_3806_, 5, v_toBind_3792_);
lean_closure_set(v___f_3806_, 6, v_inst_3793_);
lean_closure_set(v___f_3806_, 7, v_inst_3794_);
lean_closure_set(v___f_3806_, 8, v_toMonadRef_3795_);
lean_closure_set(v___f_3806_, 9, v_inst_3796_);
lean_closure_set(v___f_3806_, 10, v_inst_3797_);
lean_closure_set(v___f_3806_, 11, v_f_3798_);
lean_closure_set(v___f_3806_, 12, v___f_3799_);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v_newHyps_3803_);
v___x_3808_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3806_, v___x_3804_, v___x_3807_, lean_box(0));
v___x_3809_ = lean_apply_4(v_toBind_3792_, lean_box(0), lean_box(0), v___x_3808_, v___f_3800_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3810_, lean_object* v_inst_3811_, lean_object* v_inst_3812_, lean_object* v_inst_3813_, lean_object* v_inst_3814_, lean_object* v_inst_3815_, lean_object* v_f_3816_){
_start:
{
lean_object* v_toApplicative_3817_; lean_object* v_toBind_3818_; lean_object* v_toPure_3819_; lean_object* v_toMonadRef_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v___f_3825_; lean_object* v___f_3826_; lean_object* v___x_3827_; 
v_toApplicative_3817_ = lean_ctor_get(v_inst_3810_, 0);
v_toBind_3818_ = lean_ctor_get(v_inst_3810_, 1);
lean_inc_n(v_toBind_3818_, 3);
v_toPure_3819_ = lean_ctor_get(v_toApplicative_3817_, 1);
lean_inc_n(v_toPure_3819_, 4);
v_toMonadRef_3820_ = lean_ctor_get(v_inst_3812_, 1);
lean_inc_ref(v_toMonadRef_3820_);
lean_dec_ref(v_inst_3812_);
v___x_3821_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3811_, 2);
v___x_3822_ = lean_apply_2(v_inst_3811_, lean_box(0), v___x_3821_);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3823_, 0, v_toPure_3819_);
v___f_3824_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3824_, 0, v_inst_3811_);
lean_closure_set(v___f_3824_, 1, v_toBind_3818_);
lean_closure_set(v___f_3824_, 2, v___f_3823_);
lean_closure_set(v___f_3824_, 3, v_toPure_3819_);
v___f_3825_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3825_, 0, v_toPure_3819_);
v___f_3826_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3826_, 0, v_toPure_3819_);
lean_closure_set(v___f_3826_, 1, v_inst_3811_);
lean_closure_set(v___f_3826_, 2, v_toBind_3818_);
lean_closure_set(v___f_3826_, 3, v_inst_3813_);
lean_closure_set(v___f_3826_, 4, v_inst_3810_);
lean_closure_set(v___f_3826_, 5, v_toMonadRef_3820_);
lean_closure_set(v___f_3826_, 6, v_inst_3815_);
lean_closure_set(v___f_3826_, 7, v_inst_3814_);
lean_closure_set(v___f_3826_, 8, v_f_3816_);
lean_closure_set(v___f_3826_, 9, v___f_3825_);
lean_closure_set(v___f_3826_, 10, v___f_3824_);
v___x_3827_ = lean_apply_4(v_toBind_3818_, lean_box(0), lean_box(0), v___x_3822_, v___f_3826_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3828_, lean_object* v_inst_3829_, lean_object* v_inst_3830_, lean_object* v_inst_3831_, lean_object* v_inst_3832_, lean_object* v_inst_3833_, lean_object* v_inst_3834_, lean_object* v_inst_3835_, lean_object* v_inst_3836_, lean_object* v_f_3837_){
_start:
{
lean_object* v_toApplicative_3838_; lean_object* v_toBind_3839_; lean_object* v_toPure_3840_; lean_object* v_toMonadRef_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___f_3844_; lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; 
v_toApplicative_3838_ = lean_ctor_get(v_inst_3829_, 0);
v_toBind_3839_ = lean_ctor_get(v_inst_3829_, 1);
lean_inc_n(v_toBind_3839_, 3);
v_toPure_3840_ = lean_ctor_get(v_toApplicative_3838_, 1);
lean_inc_n(v_toPure_3840_, 4);
v_toMonadRef_3841_ = lean_ctor_get(v_inst_3831_, 1);
lean_inc_ref(v_toMonadRef_3841_);
lean_dec_ref(v_inst_3831_);
v___x_3842_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3830_, 2);
v___x_3843_ = lean_apply_2(v_inst_3830_, lean_box(0), v___x_3842_);
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3844_, 0, v_toPure_3840_);
v___f_3845_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3845_, 0, v_inst_3830_);
lean_closure_set(v___f_3845_, 1, v_toBind_3839_);
lean_closure_set(v___f_3845_, 2, v___f_3844_);
lean_closure_set(v___f_3845_, 3, v_toPure_3840_);
v___f_3846_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3846_, 0, v_toPure_3840_);
v___f_3847_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3847_, 0, v_toPure_3840_);
lean_closure_set(v___f_3847_, 1, v_inst_3830_);
lean_closure_set(v___f_3847_, 2, v_toBind_3839_);
lean_closure_set(v___f_3847_, 3, v_inst_3833_);
lean_closure_set(v___f_3847_, 4, v_inst_3829_);
lean_closure_set(v___f_3847_, 5, v_toMonadRef_3841_);
lean_closure_set(v___f_3847_, 6, v_inst_3835_);
lean_closure_set(v___f_3847_, 7, v_inst_3834_);
lean_closure_set(v___f_3847_, 8, v_f_3837_);
lean_closure_set(v___f_3847_, 9, v___f_3846_);
lean_closure_set(v___f_3847_, 10, v___f_3845_);
v___x_3848_ = lean_apply_4(v_toBind_3839_, lean_box(0), lean_box(0), v___x_3843_, v___f_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3849_, lean_object* v_inst_3850_, lean_object* v_inst_3851_, lean_object* v_inst_3852_, lean_object* v_inst_3853_, lean_object* v_inst_3854_, lean_object* v_inst_3855_, lean_object* v_inst_3856_, lean_object* v_inst_3857_, lean_object* v_f_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3849_, v_inst_3850_, v_inst_3851_, v_inst_3852_, v_inst_3853_, v_inst_3854_, v_inst_3855_, v_inst_3856_, v_inst_3857_, v_f_3858_);
lean_dec_ref(v_inst_3857_);
lean_dec_ref(v_inst_3853_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3860_, lean_object* v_x_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_apply_1(v_f_3860_, v___y_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3864_, lean_object* v_inst_3865_, lean_object* v___f_3866_, lean_object* v_hyps_3867_){
_start:
{
lean_object* v_toPure_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v_toPure_3868_ = lean_ctor_get(v_toApplicative_3864_, 1);
lean_inc(v_toPure_3868_);
lean_dec_ref(v_toApplicative_3864_);
v___x_3869_ = lean_unsigned_to_nat(0u);
v___x_3870_ = lean_array_get_size(v_hyps_3867_);
v___x_3871_ = lean_box(0);
v___x_3872_ = lean_nat_dec_lt(v___x_3869_, v___x_3870_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; 
lean_dec_ref(v_hyps_3867_);
lean_dec(v___f_3866_);
lean_dec_ref(v_inst_3865_);
v___x_3873_ = lean_apply_2(v_toPure_3868_, lean_box(0), v___x_3871_);
return v___x_3873_;
}
else
{
uint8_t v___x_3874_; 
v___x_3874_ = lean_nat_dec_le(v___x_3870_, v___x_3870_);
if (v___x_3874_ == 0)
{
if (v___x_3872_ == 0)
{
lean_object* v___x_3875_; 
lean_dec_ref(v_hyps_3867_);
lean_dec(v___f_3866_);
lean_dec_ref(v_inst_3865_);
v___x_3875_ = lean_apply_2(v_toPure_3868_, lean_box(0), v___x_3871_);
return v___x_3875_;
}
else
{
size_t v___x_3876_; size_t v___x_3877_; lean_object* v___x_3878_; 
lean_dec(v_toPure_3868_);
v___x_3876_ = ((size_t)0ULL);
v___x_3877_ = lean_usize_of_nat(v___x_3870_);
v___x_3878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3865_, v___f_3866_, v_hyps_3867_, v___x_3876_, v___x_3877_, v___x_3871_);
return v___x_3878_;
}
}
else
{
size_t v___x_3879_; size_t v___x_3880_; lean_object* v___x_3881_; 
lean_dec(v_toPure_3868_);
v___x_3879_ = ((size_t)0ULL);
v___x_3880_ = lean_usize_of_nat(v___x_3870_);
v___x_3881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3865_, v___f_3866_, v_hyps_3867_, v___x_3879_, v___x_3880_, v___x_3871_);
return v___x_3881_;
}
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
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3910_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_3913_, lean_object* v_methods_3914_, lean_object* v_config_3915_, lean_object* v_hyp_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v___x_3925_; lean_object* v_caches_3926_; lean_object* v___x_3927_; lean_object* v_typeAnalysis_3928_; lean_object* v_target_3929_; lean_object* v_hypotheses_3930_; uint8_t v_didChange_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3977_; 
v___x_3925_ = lean_st_ref_get(v_a_3917_);
v_caches_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc_ref(v_caches_3926_);
lean_dec(v___x_3925_);
v___x_3927_ = lean_st_ref_take(v_a_3917_);
v_typeAnalysis_3928_ = lean_ctor_get(v___x_3927_, 1);
v_target_3929_ = lean_ctor_get(v___x_3927_, 2);
v_hypotheses_3930_ = lean_ctor_get(v___x_3927_, 3);
v_didChange_3931_ = lean_ctor_get_uint8(v___x_3927_, sizeof(void*)*4);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3977_ == 0)
{
lean_object* v_unused_3978_; 
v_unused_3978_ = lean_ctor_get(v___x_3927_, 0);
lean_dec(v_unused_3978_);
v___x_3933_ = v___x_3927_;
v_isShared_3934_ = v_isSharedCheck_3977_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_hypotheses_3930_);
lean_inc(v_target_3929_);
lean_inc(v_typeAnalysis_3928_);
lean_dec(v___x_3927_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3977_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3935_ = lean_unsigned_to_nat(0u);
v___x_3936_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_3913_, v_caches_3926_);
v___x_3937_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_3938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3935_);
lean_ctor_set(v___x_3938_, 1, v___x_3936_);
lean_ctor_set(v___x_3938_, 2, v___x_3937_);
lean_ctor_set(v___x_3938_, 3, v___x_3937_);
v___x_3939_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3913_, v___x_3937_, v_caches_3926_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3939_);
v___x_3941_ = v___x_3933_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v_typeAnalysis_3928_);
lean_ctor_set(v_reuseFailAlloc_3976_, 2, v_target_3929_);
lean_ctor_set(v_reuseFailAlloc_3976_, 3, v_hypotheses_3930_);
lean_ctor_set_uint8(v_reuseFailAlloc_3976_, sizeof(void*)*4, v_didChange_3931_);
v___x_3941_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v_type_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3942_ = lean_st_ref_put(v_a_3917_, v___x_3941_);
v_type_3943_ = lean_ctor_get(v_hyp_3916_, 1);
lean_inc_ref(v_type_3943_);
v___x_3944_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3944_, 0, v_type_3943_);
v___x_3945_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3944_, v_methods_3914_, v_config_3915_, v___x_3938_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v_fst_3947_; lean_object* v_snd_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v_caches_3951_; lean_object* v_persistentCache_3952_; lean_object* v_typeAnalysis_3953_; lean_object* v_target_3954_; lean_object* v_hypotheses_3955_; uint8_t v_didChange_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3966_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v_fst_3947_ = lean_ctor_get(v_a_3946_, 0);
lean_inc(v_fst_3947_);
v_snd_3948_ = lean_ctor_get(v_a_3946_, 1);
lean_inc(v_snd_3948_);
lean_dec(v_a_3946_);
v___x_3949_ = lean_st_ref_get(v_a_3917_);
v___x_3950_ = lean_st_ref_take(v_a_3917_);
v_caches_3951_ = lean_ctor_get(v___x_3949_, 0);
lean_inc_ref(v_caches_3951_);
lean_dec(v___x_3949_);
v_persistentCache_3952_ = lean_ctor_get(v_snd_3948_, 1);
lean_inc_ref(v_persistentCache_3952_);
lean_dec(v_snd_3948_);
v_typeAnalysis_3953_ = lean_ctor_get(v___x_3950_, 1);
v_target_3954_ = lean_ctor_get(v___x_3950_, 2);
v_hypotheses_3955_ = lean_ctor_get(v___x_3950_, 3);
v_didChange_3956_ = lean_ctor_get_uint8(v___x_3950_, sizeof(void*)*4);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; 
v_unused_3967_ = lean_ctor_get(v___x_3950_, 0);
lean_dec(v_unused_3967_);
v___x_3958_ = v___x_3950_;
v_isShared_3959_ = v_isSharedCheck_3966_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_hypotheses_3955_);
lean_inc(v_target_3954_);
lean_inc(v_typeAnalysis_3953_);
lean_dec(v___x_3950_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3966_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3913_, v_persistentCache_3952_, v_caches_3951_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3960_);
v___x_3962_ = v___x_3958_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3960_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_typeAnalysis_3953_);
lean_ctor_set(v_reuseFailAlloc_3965_, 2, v_target_3954_);
lean_ctor_set(v_reuseFailAlloc_3965_, 3, v_hypotheses_3955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3965_, sizeof(void*)*4, v_didChange_3956_);
v___x_3962_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_st_ref_put(v_a_3917_, v___x_3962_);
v___x_3964_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_3916_, v_fst_3947_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_);
return v___x_3964_;
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec_ref(v_hyp_3916_);
v_a_3968_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3945_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3945_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_3979_, lean_object* v_methods_3980_, lean_object* v_config_3981_, lean_object* v_hyp_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
uint8_t v_cacheId_boxed_3991_; lean_object* v_res_3992_; 
v_cacheId_boxed_3991_ = lean_unbox(v_cacheId_3979_);
v_res_3992_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_3991_, v_methods_3980_, v_config_3981_, v_hyp_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_3993_, lean_object* v_methods_3994_, lean_object* v_config_3995_, lean_object* v_hyp_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_3993_, v_methods_3994_, v_config_3995_, v_hyp_3996_, v_a_3998_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4010_, lean_object* v_methods_4011_, lean_object* v_config_4012_, lean_object* v_hyp_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
uint8_t v_cacheId_boxed_4026_; lean_object* v_res_4027_; 
v_cacheId_boxed_4026_ = lean_unbox(v_cacheId_4010_);
v_res_4027_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4026_, v_methods_4011_, v_config_4012_, v_hyp_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
lean_dec(v_a_4024_);
lean_dec_ref(v_a_4023_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4028_, lean_object* v_methods_4029_, lean_object* v_config_4030_, lean_object* v_hyp_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v___x_4040_; lean_object* v_caches_4041_; lean_object* v___x_4042_; lean_object* v_typeAnalysis_4043_; lean_object* v_target_4044_; lean_object* v_hypotheses_4045_; uint8_t v_didChange_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4092_; 
v___x_4040_ = lean_st_ref_get(v_a_4032_);
v_caches_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc_ref(v_caches_4041_);
lean_dec(v___x_4040_);
v___x_4042_ = lean_st_ref_take(v_a_4032_);
v_typeAnalysis_4043_ = lean_ctor_get(v___x_4042_, 1);
v_target_4044_ = lean_ctor_get(v___x_4042_, 2);
v_hypotheses_4045_ = lean_ctor_get(v___x_4042_, 3);
v_didChange_4046_ = lean_ctor_get_uint8(v___x_4042_, sizeof(void*)*4);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v___x_4042_, 0);
lean_dec(v_unused_4093_);
v___x_4048_ = v___x_4042_;
v_isShared_4049_ = v_isSharedCheck_4092_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_hypotheses_4045_);
lean_inc(v_target_4044_);
lean_inc(v_typeAnalysis_4043_);
lean_dec(v___x_4042_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4092_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4054_; 
v___x_4050_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4028_, v_caches_4041_);
v___x_4051_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4052_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4028_, v___x_4051_, v_caches_4041_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4052_);
v___x_4054_ = v___x_4048_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4052_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_typeAnalysis_4043_);
lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_target_4044_);
lean_ctor_set(v_reuseFailAlloc_4091_, 3, v_hypotheses_4045_);
lean_ctor_set_uint8(v_reuseFailAlloc_4091_, sizeof(void*)*4, v_didChange_4046_);
v___x_4054_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; lean_object* v_type_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4055_ = lean_st_ref_put(v_a_4032_, v___x_4054_);
v_type_4056_ = lean_ctor_get(v_hyp_4031_, 1);
v___x_4057_ = lean_unsigned_to_nat(0u);
v___x_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
lean_ctor_set(v___x_4058_, 1, v___x_4050_);
lean_inc_ref(v_type_4056_);
v___x_4059_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4059_, 0, v_type_4056_);
v___x_4060_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4059_, v_methods_4029_, v_config_4030_, v___x_4058_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v_fst_4062_; lean_object* v_snd_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v_caches_4066_; lean_object* v_cache_4067_; lean_object* v_typeAnalysis_4068_; lean_object* v_target_4069_; lean_object* v_hypotheses_4070_; uint8_t v_didChange_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4081_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v_fst_4062_ = lean_ctor_get(v_a_4061_, 0);
lean_inc(v_fst_4062_);
v_snd_4063_ = lean_ctor_get(v_a_4061_, 1);
lean_inc(v_snd_4063_);
lean_dec(v_a_4061_);
v___x_4064_ = lean_st_ref_get(v_a_4032_);
v___x_4065_ = lean_st_ref_take(v_a_4032_);
v_caches_4066_ = lean_ctor_get(v___x_4064_, 0);
lean_inc_ref(v_caches_4066_);
lean_dec(v___x_4064_);
v_cache_4067_ = lean_ctor_get(v_snd_4063_, 1);
lean_inc_ref(v_cache_4067_);
lean_dec(v_snd_4063_);
v_typeAnalysis_4068_ = lean_ctor_get(v___x_4065_, 1);
v_target_4069_ = lean_ctor_get(v___x_4065_, 2);
v_hypotheses_4070_ = lean_ctor_get(v___x_4065_, 3);
v_didChange_4071_ = lean_ctor_get_uint8(v___x_4065_, sizeof(void*)*4);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v___x_4065_, 0);
lean_dec(v_unused_4082_);
v___x_4073_ = v___x_4065_;
v_isShared_4074_ = v_isSharedCheck_4081_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_hypotheses_4070_);
lean_inc(v_target_4069_);
lean_inc(v_typeAnalysis_4068_);
lean_dec(v___x_4065_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4081_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4075_; lean_object* v___x_4077_; 
v___x_4075_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4028_, v_cache_4067_, v_caches_4066_);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 0, v___x_4075_);
v___x_4077_ = v___x_4073_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4075_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_typeAnalysis_4068_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_target_4069_);
lean_ctor_set(v_reuseFailAlloc_4080_, 3, v_hypotheses_4070_);
lean_ctor_set_uint8(v_reuseFailAlloc_4080_, sizeof(void*)*4, v_didChange_4071_);
v___x_4077_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_st_ref_put(v_a_4032_, v___x_4077_);
v___x_4079_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4031_, v_fst_4062_);
lean_dec(v_fst_4062_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4094_, lean_object* v_methods_4095_, lean_object* v_config_4096_, lean_object* v_hyp_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_){
_start:
{
uint8_t v_cacheId_boxed_4106_; lean_object* v_res_4107_; 
v_cacheId_boxed_4106_ = lean_unbox(v_cacheId_4094_);
v_res_4107_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4106_, v_methods_4095_, v_config_4096_, v_hyp_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
lean_dec(v_a_4104_);
lean_dec_ref(v_a_4103_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4108_, lean_object* v_methods_4109_, lean_object* v_config_4110_, lean_object* v_hyp_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4108_, v_methods_4109_, v_config_4110_, v_hyp_4111_, v_a_4113_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4125_, lean_object* v_methods_4126_, lean_object* v_config_4127_, lean_object* v_hyp_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
uint8_t v_cacheId_boxed_4141_; lean_object* v_res_4142_; 
v_cacheId_boxed_4141_ = lean_unbox(v_cacheId_4125_);
v_res_4142_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4141_, v_methods_4126_, v_config_4127_, v_hyp_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec(v_a_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_a_4131_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4143_, lean_object* v_a_4144_, lean_object* v___x_4145_, lean_object* v_____r_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4159_ = lean_array_push(v_snd_4143_, v_a_4144_);
v___x_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4145_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4163_, lean_object* v_a_4164_, lean_object* v___x_4165_, lean_object* v_____r_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4163_, v_a_4164_, v___x_4165_, v_____r_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4180_, lean_object* v___f_4181_, lean_object* v_____r_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; lean_object* v_caches_4196_; lean_object* v_typeAnalysis_4197_; lean_object* v_target_4198_; lean_object* v_hypotheses_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4209_; 
v___x_4195_ = lean_st_ref_take(v___y_4184_);
v_caches_4196_ = lean_ctor_get(v___x_4195_, 0);
v_typeAnalysis_4197_ = lean_ctor_get(v___x_4195_, 1);
v_target_4198_ = lean_ctor_get(v___x_4195_, 2);
v_hypotheses_4199_ = lean_ctor_get(v___x_4195_, 3);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4201_ = v___x_4195_;
v_isShared_4202_ = v_isSharedCheck_4209_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_hypotheses_4199_);
lean_inc(v_target_4198_);
lean_inc(v_typeAnalysis_4197_);
lean_inc(v_caches_4196_);
lean_dec(v___x_4195_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4209_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_caches_4196_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_typeAnalysis_4197_);
lean_ctor_set(v_reuseFailAlloc_4208_, 2, v_target_4198_);
lean_ctor_set(v_reuseFailAlloc_4208_, 3, v_hypotheses_4199_);
v___x_4204_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_ctor_set_uint8(v___x_4204_, sizeof(void*)*4, v___x_4180_);
v___x_4205_ = lean_st_ref_put(v___y_4184_, v___x_4204_);
v___x_4206_ = lean_box(0);
lean_inc(v___y_4193_);
lean_inc_ref(v___y_4192_);
lean_inc(v___y_4191_);
lean_inc_ref(v___y_4190_);
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
lean_inc(v___y_4187_);
lean_inc_ref(v___y_4186_);
lean_inc(v___y_4185_);
lean_inc(v___y_4184_);
lean_inc_ref(v___y_4183_);
v___x_4207_ = lean_apply_13(v___f_4181_, v___x_4206_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, lean_box(0));
return v___x_4207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4210_, lean_object* v___f_4211_, lean_object* v_____r_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
uint8_t v___x_22141__boxed_4225_; lean_object* v_res_4226_; 
v___x_22141__boxed_4225_ = lean_unbox(v___x_4210_);
v_res_4226_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22141__boxed_4225_, v___f_4211_, v_____r_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4227_, lean_object* v_hypotheses_4228_, uint8_t v_cacheId_4229_, lean_object* v_methods_4230_, lean_object* v_config_4231_, lean_object* v___x_4232_, lean_object* v___x_4233_, lean_object* v___x_4234_, lean_object* v_toMonadRef_4235_, lean_object* v___f_4236_, lean_object* v_next_4237_, lean_object* v_acc_4238_, lean_object* v_h_4239_, lean_object* v_G_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___y_4254_; uint8_t v___x_4276_; 
v___x_4276_ = lean_nat_dec_lt(v_next_4237_, v___x_4227_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; 
lean_dec_ref(v_G_4240_);
lean_dec(v___f_4236_);
lean_dec_ref(v_toMonadRef_4235_);
lean_dec_ref(v___x_4234_);
lean_dec_ref(v___x_4233_);
lean_dec(v___x_4232_);
lean_dec_ref(v_config_4231_);
lean_dec_ref(v_methods_4230_);
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v_acc_4238_);
return v___x_4277_;
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4278_ = lean_array_fget_borrowed(v_hypotheses_4228_, v_next_4237_);
lean_inc(v___x_4278_);
v___x_4279_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4229_, v_methods_4230_, v_config_4231_, v___x_4278_, v___y_4242_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v_snd_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4344_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v_snd_4281_ = lean_ctor_get(v_acc_4238_, 1);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_acc_4238_);
if (v_isSharedCheck_4344_ == 0)
{
lean_object* v_unused_4345_; 
v_unused_4345_ = lean_ctor_get(v_acc_4238_, 0);
lean_dec(v_unused_4345_);
v___x_4283_ = v_acc_4238_;
v_isShared_4284_ = v_isSharedCheck_4344_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_snd_4281_);
lean_dec(v_acc_4238_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4344_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v_type_4285_; lean_object* v_value_4286_; uint8_t v___x_4287_; 
v_type_4285_ = lean_ctor_get(v_a_4280_, 1);
v_value_4286_ = lean_ctor_get(v_a_4280_, 2);
lean_inc_ref(v_type_4285_);
v___x_4287_ = l_Lean_Expr_isFalse(v_type_4285_);
if (v___x_4287_ == 0)
{
lean_object* v_type_4288_; lean_object* v___f_4289_; uint8_t v___x_4319_; 
lean_del_object(v___x_4283_);
v_type_4288_ = lean_ctor_get(v___x_4278_, 1);
lean_inc(v___x_4232_);
lean_inc(v_a_4280_);
lean_inc(v_snd_4281_);
v___f_4289_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4289_, 0, v_snd_4281_);
lean_closure_set(v___f_4289_, 1, v_a_4280_);
lean_closure_set(v___f_4289_, 2, v___x_4232_);
v___x_4319_ = lean_expr_eqv(v_type_4288_, v_type_4285_);
if (v___x_4319_ == 0)
{
lean_inc_ref(v_type_4285_);
lean_dec(v_snd_4281_);
lean_dec(v_a_4280_);
lean_dec(v___x_4232_);
goto v___jp_4293_;
}
else
{
if (v___x_4287_ == 0)
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_dec_ref(v___f_4289_);
lean_dec(v___f_4236_);
lean_dec_ref(v_toMonadRef_4235_);
lean_dec_ref(v___x_4234_);
lean_dec_ref(v___x_4233_);
v___x_4320_ = lean_box(0);
v___x_4321_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4281_, v_a_4280_, v___x_4232_, v___x_4320_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
v___y_4254_ = v___x_4321_;
goto v___jp_4253_;
}
else
{
lean_inc_ref(v_type_4285_);
lean_dec(v_snd_4281_);
lean_dec(v_a_4280_);
lean_dec(v___x_4232_);
goto v___jp_4293_;
}
}
v___jp_4290_:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = lean_box(0);
v___x_4292_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4276_, v___f_4289_, v___x_4291_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
v___y_4254_ = v___x_4292_;
goto v___jp_4253_;
}
v___jp_4293_:
{
lean_object* v_options_4294_; uint8_t v_hasTrace_4295_; 
v_options_4294_ = lean_ctor_get(v___y_4250_, 1);
v_hasTrace_4295_ = lean_ctor_get_uint8(v_options_4294_, sizeof(void*)*1);
if (v_hasTrace_4295_ == 0)
{
lean_dec_ref(v_type_4285_);
lean_dec(v___f_4236_);
lean_dec_ref(v_toMonadRef_4235_);
lean_dec_ref(v___x_4234_);
lean_dec_ref(v___x_4233_);
goto v___jp_4290_;
}
else
{
lean_object* v_toCold_4296_; lean_object* v_inheritedTraceOptions_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v_toCold_4296_ = lean_ctor_get(v___y_4250_, 0);
v_inheritedTraceOptions_4297_ = lean_ctor_get(v_toCold_4296_, 4);
v___x_4298_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4299_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4300_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4297_, v_options_4294_, v___x_4299_);
if (v___x_4300_ == 0)
{
lean_dec_ref(v_type_4285_);
lean_dec(v___f_4236_);
lean_dec_ref(v_toMonadRef_4235_);
lean_dec_ref(v___x_4234_);
lean_dec_ref(v___x_4233_);
goto v___jp_4290_;
}
else
{
lean_object* v_type_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_22066__overap_4307_; lean_object* v___x_4308_; 
v_type_4301_ = lean_ctor_get(v___x_4278_, 1);
lean_inc_ref(v_type_4301_);
v___x_4302_ = l_Lean_MessageData_ofExpr(v_type_4301_);
v___x_4303_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = l_Lean_MessageData_ofExpr(v_type_4285_);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_22066__overap_4307_ = l_Lean_addTrace___redArg(v___x_4233_, v___x_4234_, v_toMonadRef_4235_, v___f_4236_, v___x_4298_, v___x_4306_);
lean_inc(v___y_4251_);
lean_inc_ref(v___y_4250_);
lean_inc(v___y_4249_);
lean_inc_ref(v___y_4248_);
lean_inc(v___y_4247_);
lean_inc_ref(v___y_4246_);
lean_inc(v___y_4245_);
lean_inc_ref(v___y_4244_);
lean_inc(v___y_4243_);
lean_inc(v___y_4242_);
lean_inc_ref(v___y_4241_);
v___x_4308_ = lean_apply_12(v___x_22066__overap_4307_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, lean_box(0));
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4310_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4308_, 1);
v___x_4310_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4276_, v___f_4289_, v_a_4309_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
v___y_4254_ = v___x_4310_;
goto v___jp_4253_;
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_dec_ref(v___f_4289_);
lean_dec_ref(v_G_4240_);
v_a_4311_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4308_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4308_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4322_; 
lean_inc_ref(v_value_4286_);
lean_dec(v_a_4280_);
lean_dec_ref(v_G_4240_);
lean_dec(v___f_4236_);
lean_dec_ref(v_toMonadRef_4235_);
lean_dec_ref(v___x_4234_);
lean_dec_ref(v___x_4233_);
lean_dec(v___x_4232_);
v___x_4322_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4286_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4334_; 
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4334_ == 0)
{
lean_object* v_unused_4335_; 
v_unused_4335_ = lean_ctor_get(v___x_4322_, 0);
lean_dec(v_unused_4335_);
v___x_4324_ = v___x_4322_;
v_isShared_4325_ = v_isSharedCheck_4334_;
goto v_resetjp_4323_;
}
else
{
lean_dec(v___x_4322_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4334_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4329_; 
v___x_4326_ = lean_box(v___x_4276_);
v___x_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4327_);
v___x_4329_ = v___x_4283_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4333_, 1, v_snd_4281_);
v___x_4329_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4331_; 
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v___x_4329_);
v___x_4331_ = v___x_4324_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_del_object(v___x_4283_);
lean_dec(v_snd_4281_);
v_a_4336_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4322_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4322_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec_ref(v_G_4240_);
lean_dec_ref(v_acc_4238_);
lean_dec(v___f_4236_);
lean_dec_ref(v_toMonadRef_4235_);
lean_dec_ref(v___x_4234_);
lean_dec_ref(v___x_4233_);
lean_dec(v___x_4232_);
v_a_4346_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4279_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4279_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
v___jp_4253_:
{
if (lean_obj_tag(v___y_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4267_; 
v_a_4255_ = lean_ctor_get(v___y_4254_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___y_4254_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4257_ = v___y_4254_;
v_isShared_4258_ = v_isSharedCheck_4267_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___y_4254_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4267_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
if (lean_obj_tag(v_a_4255_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4261_; 
lean_dec_ref(v_G_4240_);
v_a_4259_ = lean_ctor_get(v_a_4255_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v_a_4255_, 1);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v_a_4259_);
v___x_4261_ = v___x_4257_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
lean_del_object(v___x_4257_);
v_a_4263_ = lean_ctor_get(v_a_4255_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v_a_4255_, 1);
v___x_4264_ = lean_unsigned_to_nat(1u);
v___x_4265_ = lean_nat_add(v_next_4237_, v___x_4264_);
lean_inc(v___y_4251_);
lean_inc_ref(v___y_4250_);
lean_inc(v___y_4249_);
lean_inc_ref(v___y_4248_);
lean_inc(v___y_4247_);
lean_inc_ref(v___y_4246_);
lean_inc(v___y_4245_);
lean_inc_ref(v___y_4244_);
lean_inc(v___y_4243_);
lean_inc(v___y_4242_);
lean_inc_ref(v___y_4241_);
v___x_4266_ = lean_apply_16(v_G_4240_, v___x_4265_, v_a_4263_, lean_box(0), lean_box(0), v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, lean_box(0));
return v___x_4266_;
}
}
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
lean_dec_ref(v_G_4240_);
v_a_4268_ = lean_ctor_get(v___y_4254_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___y_4254_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___y_4254_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___y_4254_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4354_ = _args[0];
lean_object* v_hypotheses_4355_ = _args[1];
lean_object* v_cacheId_4356_ = _args[2];
lean_object* v_methods_4357_ = _args[3];
lean_object* v_config_4358_ = _args[4];
lean_object* v___x_4359_ = _args[5];
lean_object* v___x_4360_ = _args[6];
lean_object* v___x_4361_ = _args[7];
lean_object* v_toMonadRef_4362_ = _args[8];
lean_object* v___f_4363_ = _args[9];
lean_object* v_next_4364_ = _args[10];
lean_object* v_acc_4365_ = _args[11];
lean_object* v_h_4366_ = _args[12];
lean_object* v_G_4367_ = _args[13];
lean_object* v___y_4368_ = _args[14];
lean_object* v___y_4369_ = _args[15];
lean_object* v___y_4370_ = _args[16];
lean_object* v___y_4371_ = _args[17];
lean_object* v___y_4372_ = _args[18];
lean_object* v___y_4373_ = _args[19];
lean_object* v___y_4374_ = _args[20];
lean_object* v___y_4375_ = _args[21];
lean_object* v___y_4376_ = _args[22];
lean_object* v___y_4377_ = _args[23];
lean_object* v___y_4378_ = _args[24];
lean_object* v___y_4379_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4380_; lean_object* v_res_4381_; 
v_cacheId_boxed_4380_ = lean_unbox(v_cacheId_4356_);
v_res_4381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4354_, v_hypotheses_4355_, v_cacheId_boxed_4380_, v_methods_4357_, v_config_4358_, v___x_4359_, v___x_4360_, v___x_4361_, v_toMonadRef_4362_, v___f_4363_, v_next_4364_, v_acc_4365_, v_h_4366_, v_G_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_next_4364_);
lean_dec_ref(v_hypotheses_4355_);
lean_dec(v___x_4354_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4382_, lean_object* v_methods_4383_, lean_object* v_config_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v___x_4397_; lean_object* v_toApplicative_4398_; lean_object* v_toFunctor_4399_; lean_object* v_toSeq_4400_; lean_object* v_toSeqLeft_4401_; lean_object* v_toSeqRight_4402_; lean_object* v___f_4403_; lean_object* v___f_4404_; lean_object* v___f_4405_; lean_object* v___f_4406_; lean_object* v___x_4407_; lean_object* v___f_4408_; lean_object* v___f_4409_; lean_object* v___f_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v_toApplicative_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4501_; 
v___x_4397_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4398_ = lean_ctor_get(v___x_4397_, 0);
v_toFunctor_4399_ = lean_ctor_get(v_toApplicative_4398_, 0);
v_toSeq_4400_ = lean_ctor_get(v_toApplicative_4398_, 2);
v_toSeqLeft_4401_ = lean_ctor_get(v_toApplicative_4398_, 3);
v_toSeqRight_4402_ = lean_ctor_get(v_toApplicative_4398_, 4);
v___f_4403_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4404_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4399_, 2);
v___f_4405_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4405_, 0, v_toFunctor_4399_);
v___f_4406_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4406_, 0, v_toFunctor_4399_);
v___x_4407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___f_4405_);
lean_ctor_set(v___x_4407_, 1, v___f_4406_);
lean_inc(v_toSeqRight_4402_);
v___f_4408_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4408_, 0, v_toSeqRight_4402_);
lean_inc(v_toSeqLeft_4401_);
v___f_4409_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4409_, 0, v_toSeqLeft_4401_);
lean_inc(v_toSeq_4400_);
v___f_4410_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4410_, 0, v_toSeq_4400_);
v___x_4411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4407_);
lean_ctor_set(v___x_4411_, 1, v___f_4403_);
lean_ctor_set(v___x_4411_, 2, v___f_4410_);
lean_ctor_set(v___x_4411_, 3, v___f_4409_);
lean_ctor_set(v___x_4411_, 4, v___f_4408_);
v___x_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
lean_ctor_set(v___x_4412_, 1, v___f_4404_);
v___x_4413_ = l_StateRefT_x27_instMonad___redArg(v___x_4412_);
v_toApplicative_4414_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v___x_4413_, 1);
lean_dec(v_unused_4502_);
v___x_4416_ = v___x_4413_;
v_isShared_4417_ = v_isSharedCheck_4501_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_toApplicative_4414_);
lean_dec(v___x_4413_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4501_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v_toFunctor_4418_; lean_object* v_toSeq_4419_; lean_object* v_toSeqLeft_4420_; lean_object* v_toSeqRight_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4499_; 
v_toFunctor_4418_ = lean_ctor_get(v_toApplicative_4414_, 0);
v_toSeq_4419_ = lean_ctor_get(v_toApplicative_4414_, 2);
v_toSeqLeft_4420_ = lean_ctor_get(v_toApplicative_4414_, 3);
v_toSeqRight_4421_ = lean_ctor_get(v_toApplicative_4414_, 4);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_toApplicative_4414_);
if (v_isSharedCheck_4499_ == 0)
{
lean_object* v_unused_4500_; 
v_unused_4500_ = lean_ctor_get(v_toApplicative_4414_, 1);
lean_dec(v_unused_4500_);
v___x_4423_ = v_toApplicative_4414_;
v_isShared_4424_ = v_isSharedCheck_4499_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_toSeqRight_4421_);
lean_inc(v_toSeqLeft_4420_);
lean_inc(v_toSeq_4419_);
lean_inc(v_toFunctor_4418_);
lean_dec(v_toApplicative_4414_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4499_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___f_4425_; lean_object* v___f_4426_; lean_object* v___f_4427_; lean_object* v___f_4428_; lean_object* v___x_4429_; lean_object* v___f_4430_; lean_object* v___f_4431_; lean_object* v___f_4432_; lean_object* v___x_4434_; 
v___f_4425_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4426_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4418_);
v___f_4427_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4427_, 0, v_toFunctor_4418_);
v___f_4428_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4428_, 0, v_toFunctor_4418_);
v___x_4429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___f_4427_);
lean_ctor_set(v___x_4429_, 1, v___f_4428_);
v___f_4430_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4430_, 0, v_toSeqRight_4421_);
v___f_4431_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4431_, 0, v_toSeqLeft_4420_);
v___f_4432_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4432_, 0, v_toSeq_4419_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 4, v___f_4430_);
lean_ctor_set(v___x_4423_, 3, v___f_4431_);
lean_ctor_set(v___x_4423_, 2, v___f_4432_);
lean_ctor_set(v___x_4423_, 1, v___f_4425_);
lean_ctor_set(v___x_4423_, 0, v___x_4429_);
v___x_4434_ = v___x_4423_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4429_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v___f_4425_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v___f_4432_);
lean_ctor_set(v_reuseFailAlloc_4498_, 3, v___f_4431_);
lean_ctor_set(v_reuseFailAlloc_4498_, 4, v___f_4430_);
v___x_4434_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4436_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 1, v___f_4426_);
lean_ctor_set(v___x_4416_, 0, v___x_4434_);
v___x_4436_ = v___x_4416_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4434_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v___f_4426_);
v___x_4436_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v_toMonadRef_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v_hypotheses_4448_; lean_object* v___f_4449_; lean_object* v___x_4450_; lean_object* v_newHyps_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___f_4455_; lean_object* v___x_4456_; lean_object* v___x_21848__overap_4457_; lean_object* v___x_4458_; 
v___x_4437_ = l_StateRefT_x27_instMonad___redArg(v___x_4436_);
v___x_4438_ = l_ReaderT_instMonad___redArg(v___x_4437_);
v___x_4439_ = l_StateRefT_x27_instMonad___redArg(v___x_4438_);
v___x_4440_ = l_ReaderT_instMonad___redArg(v___x_4439_);
v___x_4441_ = l_ReaderT_instMonad___redArg(v___x_4440_);
v___x_4442_ = l_StateRefT_x27_instMonad___redArg(v___x_4441_);
v___x_4443_ = l_ReaderT_instMonad___redArg(v___x_4442_);
v___x_4444_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4445_ = lean_ctor_get(v___x_4444_, 0);
v___x_4446_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4447_ = lean_st_ref_get(v_a_4386_);
v_hypotheses_4448_ = lean_ctor_get(v___x_4447_, 3);
lean_inc_ref(v_hypotheses_4448_);
lean_dec(v___x_4447_);
v___f_4449_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4450_ = lean_array_get_size(v_hypotheses_4448_);
v_newHyps_4451_ = lean_mk_empty_array_with_capacity(v___x_4450_);
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = lean_box(0);
v___x_4454_ = lean_box(v_cacheId_4382_);
lean_inc_ref(v_toMonadRef_4445_);
v___f_4455_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4455_, 0, v___x_4450_);
lean_closure_set(v___f_4455_, 1, v_hypotheses_4448_);
lean_closure_set(v___f_4455_, 2, v___x_4454_);
lean_closure_set(v___f_4455_, 3, v_methods_4383_);
lean_closure_set(v___f_4455_, 4, v_config_4384_);
lean_closure_set(v___f_4455_, 5, v___x_4453_);
lean_closure_set(v___f_4455_, 6, v___x_4443_);
lean_closure_set(v___f_4455_, 7, v___x_4446_);
lean_closure_set(v___f_4455_, 8, v_toMonadRef_4445_);
lean_closure_set(v___f_4455_, 9, v___f_4449_);
v___x_4456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4453_);
lean_ctor_set(v___x_4456_, 1, v_newHyps_4451_);
v___x_21848__overap_4457_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4455_, v___x_4452_, v___x_4456_, lean_box(0));
lean_inc(v_a_4395_);
lean_inc_ref(v_a_4394_);
lean_inc(v_a_4393_);
lean_inc_ref(v_a_4392_);
lean_inc(v_a_4391_);
lean_inc_ref(v_a_4390_);
lean_inc(v_a_4389_);
lean_inc_ref(v_a_4388_);
lean_inc(v_a_4387_);
lean_inc(v_a_4386_);
lean_inc_ref(v_a_4385_);
v___x_4458_ = lean_apply_12(v___x_21848__overap_4457_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, lean_box(0));
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4488_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4461_ = v___x_4458_;
v_isShared_4462_ = v_isSharedCheck_4488_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4458_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4488_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v_fst_4463_; 
v_fst_4463_ = lean_ctor_get(v_a_4459_, 0);
if (lean_obj_tag(v_fst_4463_) == 0)
{
lean_object* v_snd_4464_; lean_object* v___x_4465_; lean_object* v_caches_4466_; lean_object* v_typeAnalysis_4467_; lean_object* v_target_4468_; uint8_t v_didChange_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4482_; 
v_snd_4464_ = lean_ctor_get(v_a_4459_, 1);
lean_inc(v_snd_4464_);
lean_dec(v_a_4459_);
v___x_4465_ = lean_st_ref_take(v_a_4386_);
v_caches_4466_ = lean_ctor_get(v___x_4465_, 0);
v_typeAnalysis_4467_ = lean_ctor_get(v___x_4465_, 1);
v_target_4468_ = lean_ctor_get(v___x_4465_, 2);
v_didChange_4469_ = lean_ctor_get_uint8(v___x_4465_, sizeof(void*)*4);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4482_ == 0)
{
lean_object* v_unused_4483_; 
v_unused_4483_ = lean_ctor_get(v___x_4465_, 3);
lean_dec(v_unused_4483_);
v___x_4471_ = v___x_4465_;
v_isShared_4472_ = v_isSharedCheck_4482_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_target_4468_);
lean_inc(v_typeAnalysis_4467_);
lean_inc(v_caches_4466_);
lean_dec(v___x_4465_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4482_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 3, v_snd_4464_);
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_caches_4466_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_typeAnalysis_4467_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v_target_4468_);
lean_ctor_set(v_reuseFailAlloc_4481_, 3, v_snd_4464_);
lean_ctor_set_uint8(v_reuseFailAlloc_4481_, sizeof(void*)*4, v_didChange_4469_);
v___x_4474_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4475_; uint8_t v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4475_ = lean_st_ref_put(v_a_4386_, v___x_4474_);
v___x_4476_ = 0;
v___x_4477_ = lean_box(v___x_4476_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___x_4477_);
v___x_4479_ = v___x_4461_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
else
{
lean_object* v_val_4484_; lean_object* v___x_4486_; 
lean_inc_ref(v_fst_4463_);
lean_dec(v_a_4459_);
v_val_4484_ = lean_ctor_get(v_fst_4463_, 0);
lean_inc(v_val_4484_);
lean_dec_ref_known(v_fst_4463_, 1);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v_val_4484_);
v___x_4486_ = v___x_4461_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_val_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
v_a_4489_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4458_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4458_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_4503_, lean_object* v_methods_4504_, lean_object* v_config_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
uint8_t v_cacheId_boxed_4518_; lean_object* v_res_4519_; 
v_cacheId_boxed_4518_ = lean_unbox(v_cacheId_4503_);
v_res_4519_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_4518_, v_methods_4504_, v_config_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_4520_, lean_object* v_hypotheses_4521_, uint8_t v_cacheId_4522_, lean_object* v_methods_4523_, lean_object* v_config_4524_, lean_object* v___x_4525_, lean_object* v___x_4526_, lean_object* v___x_4527_, lean_object* v_toMonadRef_4528_, lean_object* v___f_4529_, lean_object* v_next_4530_, lean_object* v_acc_4531_, lean_object* v_h_4532_, lean_object* v_G_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v___y_4547_; uint8_t v___x_4569_; 
v___x_4569_ = lean_nat_dec_lt(v_next_4530_, v___x_4520_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; 
lean_dec_ref(v_G_4533_);
lean_dec(v___f_4529_);
lean_dec_ref(v_toMonadRef_4528_);
lean_dec_ref(v___x_4527_);
lean_dec_ref(v___x_4526_);
lean_dec(v___x_4525_);
lean_dec_ref(v_config_4524_);
lean_dec_ref(v_methods_4523_);
v___x_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4570_, 0, v_acc_4531_);
return v___x_4570_;
}
else
{
lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4571_ = lean_array_fget_borrowed(v_hypotheses_4521_, v_next_4530_);
lean_inc(v___x_4571_);
v___x_4572_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4522_, v_methods_4523_, v_config_4524_, v___x_4571_, v___y_4535_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v_snd_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4637_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4572_, 1);
v_snd_4574_ = lean_ctor_get(v_acc_4531_, 1);
v_isSharedCheck_4637_ = !lean_is_exclusive(v_acc_4531_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; 
v_unused_4638_ = lean_ctor_get(v_acc_4531_, 0);
lean_dec(v_unused_4638_);
v___x_4576_ = v_acc_4531_;
v_isShared_4577_ = v_isSharedCheck_4637_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_snd_4574_);
lean_dec(v_acc_4531_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4637_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_type_4578_; lean_object* v_value_4579_; uint8_t v___x_4580_; 
v_type_4578_ = lean_ctor_get(v_a_4573_, 1);
v_value_4579_ = lean_ctor_get(v_a_4573_, 2);
lean_inc_ref(v_type_4578_);
v___x_4580_ = l_Lean_Expr_isFalse(v_type_4578_);
if (v___x_4580_ == 0)
{
lean_object* v_type_4581_; lean_object* v___f_4582_; uint8_t v___x_4612_; 
lean_del_object(v___x_4576_);
v_type_4581_ = lean_ctor_get(v___x_4571_, 1);
lean_inc(v___x_4525_);
lean_inc(v_a_4573_);
lean_inc(v_snd_4574_);
v___f_4582_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4582_, 0, v_snd_4574_);
lean_closure_set(v___f_4582_, 1, v_a_4573_);
lean_closure_set(v___f_4582_, 2, v___x_4525_);
v___x_4612_ = lean_expr_eqv(v_type_4581_, v_type_4578_);
if (v___x_4612_ == 0)
{
lean_inc_ref(v_type_4578_);
lean_dec(v_snd_4574_);
lean_dec(v_a_4573_);
lean_dec(v___x_4525_);
goto v___jp_4586_;
}
else
{
if (v___x_4580_ == 0)
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
lean_dec_ref(v___f_4582_);
lean_dec(v___f_4529_);
lean_dec_ref(v_toMonadRef_4528_);
lean_dec_ref(v___x_4527_);
lean_dec_ref(v___x_4526_);
v___x_4613_ = lean_box(0);
v___x_4614_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4574_, v_a_4573_, v___x_4525_, v___x_4613_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
v___y_4547_ = v___x_4614_;
goto v___jp_4546_;
}
else
{
lean_inc_ref(v_type_4578_);
lean_dec(v_snd_4574_);
lean_dec(v_a_4573_);
lean_dec(v___x_4525_);
goto v___jp_4586_;
}
}
v___jp_4583_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4584_ = lean_box(0);
v___x_4585_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4569_, v___f_4582_, v___x_4584_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
v___y_4547_ = v___x_4585_;
goto v___jp_4546_;
}
v___jp_4586_:
{
lean_object* v_options_4587_; uint8_t v_hasTrace_4588_; 
v_options_4587_ = lean_ctor_get(v___y_4543_, 1);
v_hasTrace_4588_ = lean_ctor_get_uint8(v_options_4587_, sizeof(void*)*1);
if (v_hasTrace_4588_ == 0)
{
lean_dec_ref(v_type_4578_);
lean_dec(v___f_4529_);
lean_dec_ref(v_toMonadRef_4528_);
lean_dec_ref(v___x_4527_);
lean_dec_ref(v___x_4526_);
goto v___jp_4583_;
}
else
{
lean_object* v_toCold_4589_; lean_object* v_inheritedTraceOptions_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; uint8_t v___x_4593_; 
v_toCold_4589_ = lean_ctor_get(v___y_4543_, 0);
v_inheritedTraceOptions_4590_ = lean_ctor_get(v_toCold_4589_, 4);
v___x_4591_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4592_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4590_, v_options_4587_, v___x_4592_);
if (v___x_4593_ == 0)
{
lean_dec_ref(v_type_4578_);
lean_dec(v___f_4529_);
lean_dec_ref(v_toMonadRef_4528_);
lean_dec_ref(v___x_4527_);
lean_dec_ref(v___x_4526_);
goto v___jp_4583_;
}
else
{
lean_object* v_type_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_22066__overap_4600_; lean_object* v___x_4601_; 
v_type_4594_ = lean_ctor_get(v___x_4571_, 1);
lean_inc_ref(v_type_4594_);
v___x_4595_ = l_Lean_MessageData_ofExpr(v_type_4594_);
v___x_4596_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4595_);
lean_ctor_set(v___x_4597_, 1, v___x_4596_);
v___x_4598_ = l_Lean_MessageData_ofExpr(v_type_4578_);
v___x_4599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4597_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
v___x_22066__overap_4600_ = l_Lean_addTrace___redArg(v___x_4526_, v___x_4527_, v_toMonadRef_4528_, v___f_4529_, v___x_4591_, v___x_4599_);
lean_inc(v___y_4544_);
lean_inc_ref(v___y_4543_);
lean_inc(v___y_4542_);
lean_inc_ref(v___y_4541_);
lean_inc(v___y_4540_);
lean_inc_ref(v___y_4539_);
lean_inc(v___y_4538_);
lean_inc_ref(v___y_4537_);
lean_inc(v___y_4536_);
lean_inc(v___y_4535_);
lean_inc_ref(v___y_4534_);
v___x_4601_ = lean_apply_12(v___x_22066__overap_4600_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, lean_box(0));
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; lean_object* v___x_4603_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
lean_dec_ref_known(v___x_4601_, 1);
v___x_4603_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4569_, v___f_4582_, v_a_4602_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
v___y_4547_ = v___x_4603_;
goto v___jp_4546_;
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
lean_dec_ref(v___f_4582_);
lean_dec_ref(v_G_4533_);
v_a_4604_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4601_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4601_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4615_; 
lean_inc_ref(v_value_4579_);
lean_dec(v_a_4573_);
lean_dec_ref(v_G_4533_);
lean_dec(v___f_4529_);
lean_dec_ref(v_toMonadRef_4528_);
lean_dec_ref(v___x_4527_);
lean_dec_ref(v___x_4526_);
lean_dec(v___x_4525_);
v___x_4615_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4579_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4627_; 
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4627_ == 0)
{
lean_object* v_unused_4628_; 
v_unused_4628_ = lean_ctor_get(v___x_4615_, 0);
lean_dec(v_unused_4628_);
v___x_4617_ = v___x_4615_;
v_isShared_4618_ = v_isSharedCheck_4627_;
goto v_resetjp_4616_;
}
else
{
lean_dec(v___x_4615_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4627_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v___x_4619_ = lean_box(v___x_4569_);
v___x_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4620_);
v___x_4622_ = v___x_4576_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4620_);
lean_ctor_set(v_reuseFailAlloc_4626_, 1, v_snd_4574_);
v___x_4622_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4624_; 
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4622_);
v___x_4624_ = v___x_4617_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_del_object(v___x_4576_);
lean_dec(v_snd_4574_);
v_a_4629_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4615_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4615_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec_ref(v_G_4533_);
lean_dec_ref(v_acc_4531_);
lean_dec(v___f_4529_);
lean_dec_ref(v_toMonadRef_4528_);
lean_dec_ref(v___x_4527_);
lean_dec_ref(v___x_4526_);
lean_dec(v___x_4525_);
v_a_4639_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4572_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4572_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
v___jp_4546_:
{
if (lean_obj_tag(v___y_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4560_; 
v_a_4548_ = lean_ctor_get(v___y_4547_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___y_4547_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4550_ = v___y_4547_;
v_isShared_4551_ = v_isSharedCheck_4560_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___y_4547_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4560_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
if (lean_obj_tag(v_a_4548_) == 0)
{
lean_object* v_a_4552_; lean_object* v___x_4554_; 
lean_dec_ref(v_G_4533_);
v_a_4552_ = lean_ctor_get(v_a_4548_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v_a_4548_, 1);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v_a_4552_);
v___x_4554_ = v___x_4550_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4552_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
lean_del_object(v___x_4550_);
v_a_4556_ = lean_ctor_get(v_a_4548_, 0);
lean_inc(v_a_4556_);
lean_dec_ref_known(v_a_4548_, 1);
v___x_4557_ = lean_unsigned_to_nat(1u);
v___x_4558_ = lean_nat_add(v_next_4530_, v___x_4557_);
lean_inc(v___y_4544_);
lean_inc_ref(v___y_4543_);
lean_inc(v___y_4542_);
lean_inc_ref(v___y_4541_);
lean_inc(v___y_4540_);
lean_inc_ref(v___y_4539_);
lean_inc(v___y_4538_);
lean_inc_ref(v___y_4537_);
lean_inc(v___y_4536_);
lean_inc(v___y_4535_);
lean_inc_ref(v___y_4534_);
v___x_4559_ = lean_apply_16(v_G_4533_, v___x_4558_, v_a_4556_, lean_box(0), lean_box(0), v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, lean_box(0));
return v___x_4559_;
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec_ref(v_G_4533_);
v_a_4561_ = lean_ctor_get(v___y_4547_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___y_4547_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___y_4547_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___y_4547_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4647_ = _args[0];
lean_object* v_hypotheses_4648_ = _args[1];
lean_object* v_cacheId_4649_ = _args[2];
lean_object* v_methods_4650_ = _args[3];
lean_object* v_config_4651_ = _args[4];
lean_object* v___x_4652_ = _args[5];
lean_object* v___x_4653_ = _args[6];
lean_object* v___x_4654_ = _args[7];
lean_object* v_toMonadRef_4655_ = _args[8];
lean_object* v___f_4656_ = _args[9];
lean_object* v_next_4657_ = _args[10];
lean_object* v_acc_4658_ = _args[11];
lean_object* v_h_4659_ = _args[12];
lean_object* v_G_4660_ = _args[13];
lean_object* v___y_4661_ = _args[14];
lean_object* v___y_4662_ = _args[15];
lean_object* v___y_4663_ = _args[16];
lean_object* v___y_4664_ = _args[17];
lean_object* v___y_4665_ = _args[18];
lean_object* v___y_4666_ = _args[19];
lean_object* v___y_4667_ = _args[20];
lean_object* v___y_4668_ = _args[21];
lean_object* v___y_4669_ = _args[22];
lean_object* v___y_4670_ = _args[23];
lean_object* v___y_4671_ = _args[24];
lean_object* v___y_4672_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4673_; lean_object* v_res_4674_; 
v_cacheId_boxed_4673_ = lean_unbox(v_cacheId_4649_);
v_res_4674_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4647_, v_hypotheses_4648_, v_cacheId_boxed_4673_, v_methods_4650_, v_config_4651_, v___x_4652_, v___x_4653_, v___x_4654_, v_toMonadRef_4655_, v___f_4656_, v_next_4657_, v_acc_4658_, v_h_4659_, v_G_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v_next_4657_);
lean_dec_ref(v_hypotheses_4648_);
lean_dec(v___x_4647_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4675_, lean_object* v_methods_4676_, lean_object* v_config_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; lean_object* v_toApplicative_4691_; lean_object* v_toFunctor_4692_; lean_object* v_toSeq_4693_; lean_object* v_toSeqLeft_4694_; lean_object* v_toSeqRight_4695_; lean_object* v___f_4696_; lean_object* v___f_4697_; lean_object* v___f_4698_; lean_object* v___f_4699_; lean_object* v___x_4700_; lean_object* v___f_4701_; lean_object* v___f_4702_; lean_object* v___f_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v_toApplicative_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4794_; 
v___x_4690_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4691_ = lean_ctor_get(v___x_4690_, 0);
v_toFunctor_4692_ = lean_ctor_get(v_toApplicative_4691_, 0);
v_toSeq_4693_ = lean_ctor_get(v_toApplicative_4691_, 2);
v_toSeqLeft_4694_ = lean_ctor_get(v_toApplicative_4691_, 3);
v_toSeqRight_4695_ = lean_ctor_get(v_toApplicative_4691_, 4);
v___f_4696_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4697_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4692_, 2);
v___f_4698_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4698_, 0, v_toFunctor_4692_);
v___f_4699_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4699_, 0, v_toFunctor_4692_);
v___x_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___f_4698_);
lean_ctor_set(v___x_4700_, 1, v___f_4699_);
lean_inc(v_toSeqRight_4695_);
v___f_4701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4701_, 0, v_toSeqRight_4695_);
lean_inc(v_toSeqLeft_4694_);
v___f_4702_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4702_, 0, v_toSeqLeft_4694_);
lean_inc(v_toSeq_4693_);
v___f_4703_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4703_, 0, v_toSeq_4693_);
v___x_4704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4700_);
lean_ctor_set(v___x_4704_, 1, v___f_4696_);
lean_ctor_set(v___x_4704_, 2, v___f_4703_);
lean_ctor_set(v___x_4704_, 3, v___f_4702_);
lean_ctor_set(v___x_4704_, 4, v___f_4701_);
v___x_4705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4704_);
lean_ctor_set(v___x_4705_, 1, v___f_4697_);
v___x_4706_ = l_StateRefT_x27_instMonad___redArg(v___x_4705_);
v_toApplicative_4707_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4794_ == 0)
{
lean_object* v_unused_4795_; 
v_unused_4795_ = lean_ctor_get(v___x_4706_, 1);
lean_dec(v_unused_4795_);
v___x_4709_ = v___x_4706_;
v_isShared_4710_ = v_isSharedCheck_4794_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_toApplicative_4707_);
lean_dec(v___x_4706_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4794_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v_toFunctor_4711_; lean_object* v_toSeq_4712_; lean_object* v_toSeqLeft_4713_; lean_object* v_toSeqRight_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4792_; 
v_toFunctor_4711_ = lean_ctor_get(v_toApplicative_4707_, 0);
v_toSeq_4712_ = lean_ctor_get(v_toApplicative_4707_, 2);
v_toSeqLeft_4713_ = lean_ctor_get(v_toApplicative_4707_, 3);
v_toSeqRight_4714_ = lean_ctor_get(v_toApplicative_4707_, 4);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_toApplicative_4707_);
if (v_isSharedCheck_4792_ == 0)
{
lean_object* v_unused_4793_; 
v_unused_4793_ = lean_ctor_get(v_toApplicative_4707_, 1);
lean_dec(v_unused_4793_);
v___x_4716_ = v_toApplicative_4707_;
v_isShared_4717_ = v_isSharedCheck_4792_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_toSeqRight_4714_);
lean_inc(v_toSeqLeft_4713_);
lean_inc(v_toSeq_4712_);
lean_inc(v_toFunctor_4711_);
lean_dec(v_toApplicative_4707_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4792_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___f_4718_; lean_object* v___f_4719_; lean_object* v___f_4720_; lean_object* v___f_4721_; lean_object* v___x_4722_; lean_object* v___f_4723_; lean_object* v___f_4724_; lean_object* v___f_4725_; lean_object* v___x_4727_; 
v___f_4718_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4719_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4711_);
v___f_4720_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4720_, 0, v_toFunctor_4711_);
v___f_4721_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4721_, 0, v_toFunctor_4711_);
v___x_4722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___f_4720_);
lean_ctor_set(v___x_4722_, 1, v___f_4721_);
v___f_4723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4723_, 0, v_toSeqRight_4714_);
v___f_4724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4724_, 0, v_toSeqLeft_4713_);
v___f_4725_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4725_, 0, v_toSeq_4712_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 4, v___f_4723_);
lean_ctor_set(v___x_4716_, 3, v___f_4724_);
lean_ctor_set(v___x_4716_, 2, v___f_4725_);
lean_ctor_set(v___x_4716_, 1, v___f_4718_);
lean_ctor_set(v___x_4716_, 0, v___x_4722_);
v___x_4727_ = v___x_4716_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4791_, 1, v___f_4718_);
lean_ctor_set(v_reuseFailAlloc_4791_, 2, v___f_4725_);
lean_ctor_set(v_reuseFailAlloc_4791_, 3, v___f_4724_);
lean_ctor_set(v_reuseFailAlloc_4791_, 4, v___f_4723_);
v___x_4727_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4729_; 
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 1, v___f_4719_);
lean_ctor_set(v___x_4709_, 0, v___x_4727_);
v___x_4729_ = v___x_4709_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v___x_4727_);
lean_ctor_set(v_reuseFailAlloc_4790_, 1, v___f_4719_);
v___x_4729_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v_toMonadRef_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v_hypotheses_4741_; lean_object* v___f_4742_; lean_object* v___x_4743_; lean_object* v_newHyps_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___f_4748_; lean_object* v___x_4749_; lean_object* v___x_21848__overap_4750_; lean_object* v___x_4751_; 
v___x_4730_ = l_StateRefT_x27_instMonad___redArg(v___x_4729_);
v___x_4731_ = l_ReaderT_instMonad___redArg(v___x_4730_);
v___x_4732_ = l_StateRefT_x27_instMonad___redArg(v___x_4731_);
v___x_4733_ = l_ReaderT_instMonad___redArg(v___x_4732_);
v___x_4734_ = l_ReaderT_instMonad___redArg(v___x_4733_);
v___x_4735_ = l_StateRefT_x27_instMonad___redArg(v___x_4734_);
v___x_4736_ = l_ReaderT_instMonad___redArg(v___x_4735_);
v___x_4737_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4738_ = lean_ctor_get(v___x_4737_, 0);
v___x_4739_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4740_ = lean_st_ref_get(v_a_4679_);
v_hypotheses_4741_ = lean_ctor_get(v___x_4740_, 3);
lean_inc_ref(v_hypotheses_4741_);
lean_dec(v___x_4740_);
v___f_4742_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4743_ = lean_array_get_size(v_hypotheses_4741_);
v_newHyps_4744_ = lean_mk_empty_array_with_capacity(v___x_4743_);
v___x_4745_ = lean_unsigned_to_nat(0u);
v___x_4746_ = lean_box(0);
v___x_4747_ = lean_box(v_cacheId_4675_);
lean_inc_ref(v_toMonadRef_4738_);
v___f_4748_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4748_, 0, v___x_4743_);
lean_closure_set(v___f_4748_, 1, v_hypotheses_4741_);
lean_closure_set(v___f_4748_, 2, v___x_4747_);
lean_closure_set(v___f_4748_, 3, v_methods_4676_);
lean_closure_set(v___f_4748_, 4, v_config_4677_);
lean_closure_set(v___f_4748_, 5, v___x_4746_);
lean_closure_set(v___f_4748_, 6, v___x_4736_);
lean_closure_set(v___f_4748_, 7, v___x_4739_);
lean_closure_set(v___f_4748_, 8, v_toMonadRef_4738_);
lean_closure_set(v___f_4748_, 9, v___f_4742_);
v___x_4749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4746_);
lean_ctor_set(v___x_4749_, 1, v_newHyps_4744_);
v___x_21848__overap_4750_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4748_, v___x_4745_, v___x_4749_, lean_box(0));
lean_inc(v_a_4688_);
lean_inc_ref(v_a_4687_);
lean_inc(v_a_4686_);
lean_inc_ref(v_a_4685_);
lean_inc(v_a_4684_);
lean_inc_ref(v_a_4683_);
lean_inc(v_a_4682_);
lean_inc_ref(v_a_4681_);
lean_inc(v_a_4680_);
lean_inc(v_a_4679_);
lean_inc_ref(v_a_4678_);
v___x_4751_ = lean_apply_12(v___x_21848__overap_4750_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, lean_box(0));
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4781_; 
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4754_ = v___x_4751_;
v_isShared_4755_ = v_isSharedCheck_4781_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4751_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4781_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v_fst_4756_; 
v_fst_4756_ = lean_ctor_get(v_a_4752_, 0);
if (lean_obj_tag(v_fst_4756_) == 0)
{
lean_object* v_snd_4757_; lean_object* v___x_4758_; lean_object* v_caches_4759_; lean_object* v_typeAnalysis_4760_; lean_object* v_target_4761_; uint8_t v_didChange_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4775_; 
v_snd_4757_ = lean_ctor_get(v_a_4752_, 1);
lean_inc(v_snd_4757_);
lean_dec(v_a_4752_);
v___x_4758_ = lean_st_ref_take(v_a_4679_);
v_caches_4759_ = lean_ctor_get(v___x_4758_, 0);
v_typeAnalysis_4760_ = lean_ctor_get(v___x_4758_, 1);
v_target_4761_ = lean_ctor_get(v___x_4758_, 2);
v_didChange_4762_ = lean_ctor_get_uint8(v___x_4758_, sizeof(void*)*4);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4775_ == 0)
{
lean_object* v_unused_4776_; 
v_unused_4776_ = lean_ctor_get(v___x_4758_, 3);
lean_dec(v_unused_4776_);
v___x_4764_ = v___x_4758_;
v_isShared_4765_ = v_isSharedCheck_4775_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_target_4761_);
lean_inc(v_typeAnalysis_4760_);
lean_inc(v_caches_4759_);
lean_dec(v___x_4758_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4775_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 3, v_snd_4757_);
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_caches_4759_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_typeAnalysis_4760_);
lean_ctor_set(v_reuseFailAlloc_4774_, 2, v_target_4761_);
lean_ctor_set(v_reuseFailAlloc_4774_, 3, v_snd_4757_);
lean_ctor_set_uint8(v_reuseFailAlloc_4774_, sizeof(void*)*4, v_didChange_4762_);
v___x_4767_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
lean_object* v___x_4768_; uint8_t v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4772_; 
v___x_4768_ = lean_st_ref_put(v_a_4679_, v___x_4767_);
v___x_4769_ = 0;
v___x_4770_ = lean_box(v___x_4769_);
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 0, v___x_4770_);
v___x_4772_ = v___x_4754_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4770_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
else
{
lean_object* v_val_4777_; lean_object* v___x_4779_; 
lean_inc_ref(v_fst_4756_);
lean_dec(v_a_4752_);
v_val_4777_ = lean_ctor_get(v_fst_4756_, 0);
lean_inc(v_val_4777_);
lean_dec_ref_known(v_fst_4756_, 1);
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 0, v_val_4777_);
v___x_4779_ = v___x_4754_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_val_4777_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
v_a_4782_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4751_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4751_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4796_, lean_object* v_methods_4797_, lean_object* v_config_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_){
_start:
{
uint8_t v_cacheId_boxed_4811_; lean_object* v_res_4812_; 
v_cacheId_boxed_4811_ = lean_unbox(v_cacheId_4796_);
v_res_4812_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4811_, v_methods_4797_, v_config_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
lean_object* v___x_4819_; lean_object* v_env_4820_; lean_object* v___x_4821_; lean_object* v_mctx_4822_; lean_object* v_lctx_4823_; lean_object* v_options_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4819_ = lean_st_ref_get(v___y_4817_);
v_env_4820_ = lean_ctor_get(v___x_4819_, 0);
lean_inc_ref(v_env_4820_);
lean_dec(v___x_4819_);
v___x_4821_ = lean_st_ref_get(v___y_4815_);
v_mctx_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc_ref(v_mctx_4822_);
lean_dec(v___x_4821_);
v_lctx_4823_ = lean_ctor_get(v___y_4814_, 2);
v_options_4824_ = lean_ctor_get(v___y_4816_, 1);
lean_inc_ref(v_options_4824_);
lean_inc_ref(v_lctx_4823_);
v___x_4825_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4825_, 0, v_env_4820_);
lean_ctor_set(v___x_4825_, 1, v_mctx_4822_);
lean_ctor_set(v___x_4825_, 2, v_lctx_4823_);
lean_ctor_set(v___x_4825_, 3, v_options_4824_);
v___x_4826_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
lean_ctor_set(v___x_4826_, 1, v_msgData_4813_);
v___x_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
return v_res_4834_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4835_; double v___x_4836_; 
v___x_4835_ = lean_unsigned_to_nat(0u);
v___x_4836_ = lean_float_of_nat(v___x_4835_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4840_, lean_object* v_msg_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v_ref_4847_; lean_object* v___x_4848_; lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4893_; 
v_ref_4847_ = lean_ctor_get(v___y_4844_, 4);
v___x_4848_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4851_ = v___x_4848_;
v_isShared_4852_ = v_isSharedCheck_4893_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4848_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4893_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4853_; lean_object* v_traceState_4854_; lean_object* v_env_4855_; lean_object* v_nextMacroScope_4856_; lean_object* v_ngen_4857_; lean_object* v_auxDeclNGen_4858_; lean_object* v_cache_4859_; lean_object* v_messages_4860_; lean_object* v_infoState_4861_; lean_object* v_snapshotTasks_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4892_; 
v___x_4853_ = lean_st_ref_take(v___y_4845_);
v_traceState_4854_ = lean_ctor_get(v___x_4853_, 4);
v_env_4855_ = lean_ctor_get(v___x_4853_, 0);
v_nextMacroScope_4856_ = lean_ctor_get(v___x_4853_, 1);
v_ngen_4857_ = lean_ctor_get(v___x_4853_, 2);
v_auxDeclNGen_4858_ = lean_ctor_get(v___x_4853_, 3);
v_cache_4859_ = lean_ctor_get(v___x_4853_, 5);
v_messages_4860_ = lean_ctor_get(v___x_4853_, 6);
v_infoState_4861_ = lean_ctor_get(v___x_4853_, 7);
v_snapshotTasks_4862_ = lean_ctor_get(v___x_4853_, 8);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4864_ = v___x_4853_;
v_isShared_4865_ = v_isSharedCheck_4892_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_snapshotTasks_4862_);
lean_inc(v_infoState_4861_);
lean_inc(v_messages_4860_);
lean_inc(v_cache_4859_);
lean_inc(v_traceState_4854_);
lean_inc(v_auxDeclNGen_4858_);
lean_inc(v_ngen_4857_);
lean_inc(v_nextMacroScope_4856_);
lean_inc(v_env_4855_);
lean_dec(v___x_4853_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4892_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
uint64_t v_tid_4866_; lean_object* v_traces_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4891_; 
v_tid_4866_ = lean_ctor_get_uint64(v_traceState_4854_, sizeof(void*)*1);
v_traces_4867_ = lean_ctor_get(v_traceState_4854_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v_traceState_4854_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4869_ = v_traceState_4854_;
v_isShared_4870_ = v_isSharedCheck_4891_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_traces_4867_);
lean_dec(v_traceState_4854_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4891_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4871_; double v___x_4872_; uint8_t v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4871_ = lean_box(0);
v___x_4872_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4873_ = 0;
v___x_4874_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4875_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4875_, 0, v_cls_4840_);
lean_ctor_set(v___x_4875_, 1, v___x_4871_);
lean_ctor_set(v___x_4875_, 2, v___x_4874_);
lean_ctor_set_float(v___x_4875_, sizeof(void*)*3, v___x_4872_);
lean_ctor_set_float(v___x_4875_, sizeof(void*)*3 + 8, v___x_4872_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*3 + 16, v___x_4873_);
v___x_4876_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4877_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4875_);
lean_ctor_set(v___x_4877_, 1, v_a_4849_);
lean_ctor_set(v___x_4877_, 2, v___x_4876_);
lean_inc(v_ref_4847_);
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v_ref_4847_);
lean_ctor_set(v___x_4878_, 1, v___x_4877_);
v___x_4879_ = l_Lean_PersistentArray_push___redArg(v_traces_4867_, v___x_4878_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v___x_4879_);
v___x_4881_ = v___x_4869_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4879_);
lean_ctor_set_uint64(v_reuseFailAlloc_4890_, sizeof(void*)*1, v_tid_4866_);
v___x_4881_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
lean_object* v___x_4883_; 
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 4, v___x_4881_);
v___x_4883_ = v___x_4864_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_env_4855_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v_nextMacroScope_4856_);
lean_ctor_set(v_reuseFailAlloc_4889_, 2, v_ngen_4857_);
lean_ctor_set(v_reuseFailAlloc_4889_, 3, v_auxDeclNGen_4858_);
lean_ctor_set(v_reuseFailAlloc_4889_, 4, v___x_4881_);
lean_ctor_set(v_reuseFailAlloc_4889_, 5, v_cache_4859_);
lean_ctor_set(v_reuseFailAlloc_4889_, 6, v_messages_4860_);
lean_ctor_set(v_reuseFailAlloc_4889_, 7, v_infoState_4861_);
lean_ctor_set(v_reuseFailAlloc_4889_, 8, v_snapshotTasks_4862_);
v___x_4883_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4884_ = lean_st_ref_put(v___y_4845_, v___x_4883_);
v___x_4885_ = lean_box(0);
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 0, v___x_4885_);
v___x_4887_ = v___x_4851_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4885_);
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
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_caches_4919_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_typeAnalysis_4920_);
lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_target_4921_);
lean_ctor_set(v_reuseFailAlloc_4931_, 3, v_hypotheses_4922_);
v___x_4927_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
lean_ctor_set_uint8(v___x_4927_, sizeof(void*)*4, v___x_4902_);
v___x_4928_ = lean_st_ref_put(v___y_4907_, v___x_4927_);
v___x_4929_ = lean_box(0);
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
v___x_4930_ = lean_apply_14(v___f_4903_, v___x_4929_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, lean_box(0));
return v___x_4930_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_4933_, lean_object* v___f_4934_, lean_object* v_____r_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
uint8_t v___x_35701__boxed_4949_; lean_object* v_res_4950_; 
v___x_35701__boxed_4949_ = lean_unbox(v___x_4933_);
v_res_4950_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35701__boxed_4949_, v___f_4934_, v_____r_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
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
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v_type_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5034_ = lean_st_ref_take(v___y_4996_);
v___x_5035_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_5036_ = lean_st_ref_put(v___y_4996_, v___x_5035_);
v___x_5037_ = lean_array_fget_borrowed(v___x_4991_, v_a_4994_);
v_type_5038_ = lean_ctor_get(v___x_5037_, 1);
v___x_5039_ = lean_unsigned_to_nat(0u);
v___x_5040_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5039_);
lean_ctor_set(v___x_5040_, 1, v___x_5034_);
lean_ctor_set(v___x_5040_, 2, v___x_5035_);
lean_ctor_set(v___x_5040_, 3, v___x_5035_);
lean_inc_ref(v_type_5038_);
v___x_5041_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5041_, 0, v_type_5038_);
lean_inc_ref(v_config_4993_);
lean_inc_ref(v_methods_4992_);
v___x_5042_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5041_, v_methods_4992_, v_config_4993_, v___x_5040_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v_snd_5044_; lean_object* v_fst_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5126_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5042_, 1);
v_snd_5044_ = lean_ctor_get(v_a_5043_, 1);
v_fst_5045_ = lean_ctor_get(v_a_5043_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v_a_5043_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5047_ = v_a_5043_;
v_isShared_5048_ = v_isSharedCheck_5126_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_snd_5044_);
lean_inc(v_fst_5045_);
lean_dec(v_a_5043_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5126_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v_persistentCache_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v_persistentCache_5049_ = lean_ctor_get(v_snd_5044_, 1);
lean_inc_ref(v_persistentCache_5049_);
lean_dec(v_snd_5044_);
v___x_5050_ = lean_st_ref_swap(v___y_4996_, v_persistentCache_5049_);
lean_dec(v___x_5050_);
lean_inc(v___x_5037_);
v___x_5051_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5037_, v_fst_5045_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; lean_object* v_snd_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5116_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_a_5052_);
lean_dec_ref_known(v___x_5051_, 1);
v_snd_5053_ = lean_ctor_get(v_b_4995_, 1);
v_isSharedCheck_5116_ = !lean_is_exclusive(v_b_4995_);
if (v_isSharedCheck_5116_ == 0)
{
lean_object* v_unused_5117_; 
v_unused_5117_ = lean_ctor_get(v_b_4995_, 0);
lean_dec(v_unused_5117_);
v___x_5055_ = v_b_4995_;
v_isShared_5056_ = v_isSharedCheck_5116_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_snd_5053_);
lean_dec(v_b_4995_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5116_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v_type_5057_; lean_object* v_value_5058_; uint8_t v___x_5059_; 
v_type_5057_ = lean_ctor_get(v_a_5052_, 1);
v_value_5058_ = lean_ctor_get(v_a_5052_, 2);
lean_inc_ref(v_type_5057_);
v___x_5059_ = l_Lean_Expr_isFalse(v_type_5057_);
if (v___x_5059_ == 0)
{
lean_object* v___x_5060_; lean_object* v___f_5061_; uint8_t v___x_5091_; 
lean_del_object(v___x_5055_);
v___x_5060_ = lean_box(0);
lean_inc(v_a_5052_);
lean_inc(v_snd_5053_);
v___f_5061_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5061_, 0, v_snd_5053_);
lean_closure_set(v___f_5061_, 1, v_a_5052_);
lean_closure_set(v___f_5061_, 2, v___x_5060_);
v___x_5091_ = lean_expr_eqv(v_type_5038_, v_type_5057_);
if (v___x_5091_ == 0)
{
lean_inc_ref(v_type_5057_);
lean_dec(v_snd_5053_);
lean_dec(v_a_5052_);
goto v___jp_5065_;
}
else
{
if (v___x_5059_ == 0)
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_dec_ref(v___f_5061_);
lean_del_object(v___x_5047_);
v___x_5092_ = lean_box(0);
v___x_5093_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5053_, v_a_5052_, v___x_5060_, v___x_5092_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
v___y_5010_ = v___x_5093_;
goto v___jp_5009_;
}
else
{
lean_inc_ref(v_type_5057_);
lean_dec(v_snd_5053_);
lean_dec(v_a_5052_);
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
lean_object* v_options_5066_; uint8_t v_hasTrace_5067_; 
v_options_5066_ = lean_ctor_get(v___y_5006_, 1);
v_hasTrace_5067_ = lean_ctor_get_uint8(v_options_5066_, sizeof(void*)*1);
if (v_hasTrace_5067_ == 0)
{
lean_dec_ref(v_type_5057_);
lean_del_object(v___x_5047_);
goto v___jp_5062_;
}
else
{
lean_object* v_toCold_5068_; lean_object* v_inheritedTraceOptions_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; uint8_t v___x_5072_; 
v_toCold_5068_ = lean_ctor_get(v___y_5006_, 0);
v_inheritedTraceOptions_5069_ = lean_ctor_get(v_toCold_5068_, 4);
v___x_5070_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5071_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5069_, v_options_5066_, v___x_5071_);
if (v___x_5072_ == 0)
{
lean_dec_ref(v_type_5057_);
lean_del_object(v___x_5047_);
goto v___jp_5062_;
}
else
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; 
lean_inc_ref(v_type_5038_);
v___x_5073_ = l_Lean_MessageData_ofExpr(v_type_5038_);
v___x_5074_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5048_ == 0)
{
lean_ctor_set_tag(v___x_5047_, 7);
lean_ctor_set(v___x_5047_, 1, v___x_5074_);
lean_ctor_set(v___x_5047_, 0, v___x_5073_);
v___x_5076_ = v___x_5047_;
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
v___x_5077_ = l_Lean_MessageData_ofExpr(v_type_5057_);
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
lean_inc_ref(v_value_5058_);
lean_dec(v_a_5052_);
lean_del_object(v___x_5047_);
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v___x_5094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5058_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
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
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 0, v___x_5099_);
v___x_5101_ = v___x_5055_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v___x_5099_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v_snd_5053_);
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
lean_del_object(v___x_5055_);
lean_dec(v_snd_5053_);
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
}
else
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5125_; 
lean_del_object(v___x_5047_);
lean_dec_ref(v_b_4995_);
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v_a_5118_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5051_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5051_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5123_; 
if (v_isShared_5121_ == 0)
{
v___x_5123_ = v___x_5120_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
}
}
else
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
lean_dec_ref(v_b_4995_);
lean_dec(v_a_4994_);
lean_dec_ref(v_config_4993_);
lean_dec_ref(v_methods_4992_);
v_a_5127_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5129_ = v___x_5042_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5042_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
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
v___x_5324_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
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
lean_object* v_ref_5358_; lean_object* v___x_5359_; lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5404_; 
v_ref_5358_ = lean_ctor_get(v___y_5355_, 4);
v___x_5359_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_);
v_a_5360_ = lean_ctor_get(v___x_5359_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5362_ = v___x_5359_;
v_isShared_5363_ = v_isSharedCheck_5404_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5359_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5404_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5364_; lean_object* v_traceState_5365_; lean_object* v_env_5366_; lean_object* v_nextMacroScope_5367_; lean_object* v_ngen_5368_; lean_object* v_auxDeclNGen_5369_; lean_object* v_cache_5370_; lean_object* v_messages_5371_; lean_object* v_infoState_5372_; lean_object* v_snapshotTasks_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5403_; 
v___x_5364_ = lean_st_ref_take(v___y_5356_);
v_traceState_5365_ = lean_ctor_get(v___x_5364_, 4);
v_env_5366_ = lean_ctor_get(v___x_5364_, 0);
v_nextMacroScope_5367_ = lean_ctor_get(v___x_5364_, 1);
v_ngen_5368_ = lean_ctor_get(v___x_5364_, 2);
v_auxDeclNGen_5369_ = lean_ctor_get(v___x_5364_, 3);
v_cache_5370_ = lean_ctor_get(v___x_5364_, 5);
v_messages_5371_ = lean_ctor_get(v___x_5364_, 6);
v_infoState_5372_ = lean_ctor_get(v___x_5364_, 7);
v_snapshotTasks_5373_ = lean_ctor_get(v___x_5364_, 8);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5375_ = v___x_5364_;
v_isShared_5376_ = v_isSharedCheck_5403_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_snapshotTasks_5373_);
lean_inc(v_infoState_5372_);
lean_inc(v_messages_5371_);
lean_inc(v_cache_5370_);
lean_inc(v_traceState_5365_);
lean_inc(v_auxDeclNGen_5369_);
lean_inc(v_ngen_5368_);
lean_inc(v_nextMacroScope_5367_);
lean_inc(v_env_5366_);
lean_dec(v___x_5364_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5403_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
uint64_t v_tid_5377_; lean_object* v_traces_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5402_; 
v_tid_5377_ = lean_ctor_get_uint64(v_traceState_5365_, sizeof(void*)*1);
v_traces_5378_ = lean_ctor_get(v_traceState_5365_, 0);
v_isSharedCheck_5402_ = !lean_is_exclusive(v_traceState_5365_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5380_ = v_traceState_5365_;
v_isShared_5381_ = v_isSharedCheck_5402_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_traces_5378_);
lean_dec(v_traceState_5365_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5402_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5382_; double v___x_5383_; uint8_t v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5392_; 
v___x_5382_ = lean_box(0);
v___x_5383_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5384_ = 0;
v___x_5385_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5386_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5386_, 0, v_cls_5351_);
lean_ctor_set(v___x_5386_, 1, v___x_5382_);
lean_ctor_set(v___x_5386_, 2, v___x_5385_);
lean_ctor_set_float(v___x_5386_, sizeof(void*)*3, v___x_5383_);
lean_ctor_set_float(v___x_5386_, sizeof(void*)*3 + 8, v___x_5383_);
lean_ctor_set_uint8(v___x_5386_, sizeof(void*)*3 + 16, v___x_5384_);
v___x_5387_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5388_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5386_);
lean_ctor_set(v___x_5388_, 1, v_a_5360_);
lean_ctor_set(v___x_5388_, 2, v___x_5387_);
lean_inc(v_ref_5358_);
v___x_5389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5389_, 0, v_ref_5358_);
lean_ctor_set(v___x_5389_, 1, v___x_5388_);
v___x_5390_ = l_Lean_PersistentArray_push___redArg(v_traces_5378_, v___x_5389_);
if (v_isShared_5381_ == 0)
{
lean_ctor_set(v___x_5380_, 0, v___x_5390_);
v___x_5392_ = v___x_5380_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5390_);
lean_ctor_set_uint64(v_reuseFailAlloc_5401_, sizeof(void*)*1, v_tid_5377_);
v___x_5392_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
lean_object* v___x_5394_; 
if (v_isShared_5376_ == 0)
{
lean_ctor_set(v___x_5375_, 4, v___x_5392_);
v___x_5394_ = v___x_5375_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_env_5366_);
lean_ctor_set(v_reuseFailAlloc_5400_, 1, v_nextMacroScope_5367_);
lean_ctor_set(v_reuseFailAlloc_5400_, 2, v_ngen_5368_);
lean_ctor_set(v_reuseFailAlloc_5400_, 3, v_auxDeclNGen_5369_);
lean_ctor_set(v_reuseFailAlloc_5400_, 4, v___x_5392_);
lean_ctor_set(v_reuseFailAlloc_5400_, 5, v_cache_5370_);
lean_ctor_set(v_reuseFailAlloc_5400_, 6, v_messages_5371_);
lean_ctor_set(v_reuseFailAlloc_5400_, 7, v_infoState_5372_);
lean_ctor_set(v_reuseFailAlloc_5400_, 8, v_snapshotTasks_5373_);
v___x_5394_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5398_; 
v___x_5395_ = lean_st_ref_put(v___y_5356_, v___x_5394_);
v___x_5396_ = lean_box(0);
if (v_isShared_5363_ == 0)
{
lean_ctor_set(v___x_5362_, 0, v___x_5396_);
v___x_5398_ = v___x_5362_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v___x_5396_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5405_, lean_object* v_msg_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5405_, v_msg_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5413_, lean_object* v___x_5414_, lean_object* v_methods_5415_, lean_object* v_config_5416_, lean_object* v_a_5417_, lean_object* v_b_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
lean_object* v___y_5433_; uint8_t v___x_5455_; 
v___x_5455_ = lean_nat_dec_lt(v_a_5417_, v_upperBound_5413_);
if (v___x_5455_ == 0)
{
lean_object* v___x_5456_; 
lean_dec(v_a_5417_);
lean_dec_ref(v_config_5416_);
lean_dec_ref(v_methods_5415_);
v___x_5456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5456_, 0, v_b_5418_);
return v___x_5456_;
}
else
{
lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v_type_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5457_ = lean_st_ref_take(v___y_5419_);
v___x_5458_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5459_ = lean_st_ref_put(v___y_5419_, v___x_5458_);
v___x_5460_ = lean_array_fget_borrowed(v___x_5414_, v_a_5417_);
v_type_5461_ = lean_ctor_get(v___x_5460_, 1);
v___x_5462_ = lean_unsigned_to_nat(0u);
v___x_5463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5463_, 0, v___x_5462_);
lean_ctor_set(v___x_5463_, 1, v___x_5457_);
lean_inc_ref(v_type_5461_);
v___x_5464_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5464_, 0, v_type_5461_);
lean_inc_ref(v_config_5416_);
lean_inc_ref(v_methods_5415_);
v___x_5465_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5464_, v_methods_5415_, v_config_5416_, v___x_5463_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v_a_5466_; lean_object* v_snd_5467_; lean_object* v_fst_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5556_; 
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
lean_inc(v_a_5466_);
lean_dec_ref_known(v___x_5465_, 1);
v_snd_5467_ = lean_ctor_get(v_a_5466_, 1);
v_fst_5468_ = lean_ctor_get(v_a_5466_, 0);
v_isSharedCheck_5556_ = !lean_is_exclusive(v_a_5466_);
if (v_isSharedCheck_5556_ == 0)
{
v___x_5470_ = v_a_5466_;
v_isShared_5471_ = v_isSharedCheck_5556_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_snd_5467_);
lean_inc(v_fst_5468_);
lean_dec(v_a_5466_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5556_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v_cache_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5554_; 
v_cache_5472_ = lean_ctor_get(v_snd_5467_, 1);
v_isSharedCheck_5554_ = !lean_is_exclusive(v_snd_5467_);
if (v_isSharedCheck_5554_ == 0)
{
lean_object* v_unused_5555_; 
v_unused_5555_ = lean_ctor_get(v_snd_5467_, 0);
lean_dec(v_unused_5555_);
v___x_5474_ = v_snd_5467_;
v_isShared_5475_ = v_isSharedCheck_5554_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_cache_5472_);
lean_dec(v_snd_5467_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5554_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5476_; lean_object* v___x_5477_; 
v___x_5476_ = lean_st_ref_swap(v___y_5419_, v_cache_5472_);
lean_dec(v___x_5476_);
lean_inc(v___x_5460_);
v___x_5477_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5460_, v_fst_5468_);
lean_dec(v_fst_5468_);
if (lean_obj_tag(v___x_5477_) == 0)
{
lean_object* v_a_5478_; lean_object* v_snd_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5544_; 
v_a_5478_ = lean_ctor_get(v___x_5477_, 0);
lean_inc(v_a_5478_);
lean_dec_ref_known(v___x_5477_, 1);
v_snd_5479_ = lean_ctor_get(v_b_5418_, 1);
v_isSharedCheck_5544_ = !lean_is_exclusive(v_b_5418_);
if (v_isSharedCheck_5544_ == 0)
{
lean_object* v_unused_5545_; 
v_unused_5545_ = lean_ctor_get(v_b_5418_, 0);
lean_dec(v_unused_5545_);
v___x_5481_ = v_b_5418_;
v_isShared_5482_ = v_isSharedCheck_5544_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_snd_5479_);
lean_dec(v_b_5418_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5544_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v_type_5483_; lean_object* v_value_5484_; uint8_t v___x_5485_; 
v_type_5483_ = lean_ctor_get(v_a_5478_, 1);
v_value_5484_ = lean_ctor_get(v_a_5478_, 2);
lean_inc_ref(v_type_5483_);
v___x_5485_ = l_Lean_Expr_isFalse(v_type_5483_);
if (v___x_5485_ == 0)
{
lean_object* v___x_5486_; lean_object* v___f_5487_; uint8_t v___x_5519_; 
lean_del_object(v___x_5481_);
v___x_5486_ = lean_box(0);
lean_inc(v_a_5478_);
lean_inc(v_snd_5479_);
v___f_5487_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5487_, 0, v_snd_5479_);
lean_closure_set(v___f_5487_, 1, v_a_5478_);
lean_closure_set(v___f_5487_, 2, v___x_5486_);
v___x_5519_ = lean_expr_eqv(v_type_5461_, v_type_5483_);
if (v___x_5519_ == 0)
{
lean_inc_ref(v_type_5483_);
lean_dec(v_snd_5479_);
lean_dec(v_a_5478_);
goto v___jp_5491_;
}
else
{
if (v___x_5485_ == 0)
{
lean_object* v___x_5520_; lean_object* v___x_5521_; 
lean_dec_ref(v___f_5487_);
lean_del_object(v___x_5474_);
lean_del_object(v___x_5470_);
v___x_5520_ = lean_box(0);
v___x_5521_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5479_, v_a_5478_, v___x_5486_, v___x_5520_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
v___y_5433_ = v___x_5521_;
goto v___jp_5432_;
}
else
{
lean_inc_ref(v_type_5483_);
lean_dec(v_snd_5479_);
lean_dec(v_a_5478_);
goto v___jp_5491_;
}
}
v___jp_5488_:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5489_ = lean_box(0);
v___x_5490_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5455_, v___f_5487_, v___x_5489_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
v___y_5433_ = v___x_5490_;
goto v___jp_5432_;
}
v___jp_5491_:
{
lean_object* v_options_5492_; uint8_t v_hasTrace_5493_; 
v_options_5492_ = lean_ctor_get(v___y_5429_, 1);
v_hasTrace_5493_ = lean_ctor_get_uint8(v_options_5492_, sizeof(void*)*1);
if (v_hasTrace_5493_ == 0)
{
lean_dec_ref(v_type_5483_);
lean_del_object(v___x_5474_);
lean_del_object(v___x_5470_);
goto v___jp_5488_;
}
else
{
lean_object* v_toCold_5494_; lean_object* v_inheritedTraceOptions_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; 
v_toCold_5494_ = lean_ctor_get(v___y_5429_, 0);
v_inheritedTraceOptions_5495_ = lean_ctor_get(v_toCold_5494_, 4);
v___x_5496_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5497_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5498_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5495_, v_options_5492_, v___x_5497_);
if (v___x_5498_ == 0)
{
lean_dec_ref(v_type_5483_);
lean_del_object(v___x_5474_);
lean_del_object(v___x_5470_);
goto v___jp_5488_;
}
else
{
lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5502_; 
lean_inc_ref(v_type_5461_);
v___x_5499_ = l_Lean_MessageData_ofExpr(v_type_5461_);
v___x_5500_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5475_ == 0)
{
lean_ctor_set_tag(v___x_5474_, 7);
lean_ctor_set(v___x_5474_, 1, v___x_5500_);
lean_ctor_set(v___x_5474_, 0, v___x_5499_);
v___x_5502_ = v___x_5474_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5503_; lean_object* v___x_5505_; 
v___x_5503_ = l_Lean_MessageData_ofExpr(v_type_5483_);
if (v_isShared_5471_ == 0)
{
lean_ctor_set_tag(v___x_5470_, 7);
lean_ctor_set(v___x_5470_, 1, v___x_5503_);
lean_ctor_set(v___x_5470_, 0, v___x_5502_);
v___x_5505_ = v___x_5470_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v___x_5502_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v___x_5503_);
v___x_5505_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
lean_object* v___x_5506_; 
v___x_5506_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5496_, v___x_5505_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
if (lean_obj_tag(v___x_5506_) == 0)
{
lean_object* v_a_5507_; lean_object* v___x_5508_; 
v_a_5507_ = lean_ctor_get(v___x_5506_, 0);
lean_inc(v_a_5507_);
lean_dec_ref_known(v___x_5506_, 1);
v___x_5508_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5455_, v___f_5487_, v_a_5507_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
v___y_5433_ = v___x_5508_;
goto v___jp_5432_;
}
else
{
lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5516_; 
lean_dec_ref(v___f_5487_);
lean_dec(v_a_5417_);
lean_dec_ref(v_config_5416_);
lean_dec_ref(v_methods_5415_);
v_a_5509_ = lean_ctor_get(v___x_5506_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5511_ = v___x_5506_;
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v___x_5506_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5514_; 
if (v_isShared_5512_ == 0)
{
v___x_5514_ = v___x_5511_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5509_);
v___x_5514_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
return v___x_5514_;
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
lean_object* v___x_5522_; 
lean_inc_ref(v_value_5484_);
lean_dec(v_a_5478_);
lean_del_object(v___x_5474_);
lean_del_object(v___x_5470_);
lean_dec(v_a_5417_);
lean_dec_ref(v_config_5416_);
lean_dec_ref(v_methods_5415_);
v___x_5522_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5484_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
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
v___x_5526_ = lean_box(v___x_5455_);
v___x_5527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5527_, 0, v___x_5526_);
if (v_isShared_5482_ == 0)
{
lean_ctor_set(v___x_5481_, 0, v___x_5527_);
v___x_5529_ = v___x_5481_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v_snd_5479_);
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
lean_del_object(v___x_5481_);
lean_dec(v_snd_5479_);
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
}
else
{
lean_object* v_a_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5553_; 
lean_del_object(v___x_5474_);
lean_del_object(v___x_5470_);
lean_dec_ref(v_b_5418_);
lean_dec(v_a_5417_);
lean_dec_ref(v_config_5416_);
lean_dec_ref(v_methods_5415_);
v_a_5546_ = lean_ctor_get(v___x_5477_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5477_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5548_ = v___x_5477_;
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_a_5546_);
lean_dec(v___x_5477_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v___x_5551_; 
if (v_isShared_5549_ == 0)
{
v___x_5551_ = v___x_5548_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_a_5546_);
v___x_5551_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
return v___x_5551_;
}
}
}
}
}
}
else
{
lean_object* v_a_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5564_; 
lean_dec_ref(v_b_5418_);
lean_dec(v_a_5417_);
lean_dec_ref(v_config_5416_);
lean_dec_ref(v_methods_5415_);
v_a_5557_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5564_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5559_ = v___x_5465_;
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_a_5557_);
lean_dec(v___x_5465_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5562_; 
if (v_isShared_5560_ == 0)
{
v___x_5562_ = v___x_5559_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5557_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
v___jp_5432_:
{
if (lean_obj_tag(v___y_5433_) == 0)
{
lean_object* v_a_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5446_; 
v_a_5434_ = lean_ctor_get(v___y_5433_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___y_5433_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5436_ = v___y_5433_;
v_isShared_5437_ = v_isSharedCheck_5446_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_a_5434_);
lean_dec(v___y_5433_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5446_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
if (lean_obj_tag(v_a_5434_) == 0)
{
lean_object* v_a_5438_; lean_object* v___x_5440_; 
lean_dec(v_a_5417_);
lean_dec_ref(v_config_5416_);
lean_dec_ref(v_methods_5415_);
v_a_5438_ = lean_ctor_get(v_a_5434_, 0);
lean_inc(v_a_5438_);
lean_dec_ref_known(v_a_5434_, 1);
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 0, v_a_5438_);
v___x_5440_ = v___x_5436_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_a_5438_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
else
{
lean_object* v_a_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
lean_del_object(v___x_5436_);
v_a_5442_ = lean_ctor_get(v_a_5434_, 0);
lean_inc(v_a_5442_);
lean_dec_ref_known(v_a_5434_, 1);
v___x_5443_ = lean_unsigned_to_nat(1u);
v___x_5444_ = lean_nat_add(v_a_5417_, v___x_5443_);
lean_dec(v_a_5417_);
v_a_5417_ = v___x_5444_;
v_b_5418_ = v_a_5442_;
goto _start;
}
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
lean_dec(v_a_5417_);
lean_dec_ref(v_config_5416_);
lean_dec_ref(v_methods_5415_);
v_a_5447_ = lean_ctor_get(v___y_5433_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___y_5433_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___y_5433_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___y_5433_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5565_ = _args[0];
lean_object* v___x_5566_ = _args[1];
lean_object* v_methods_5567_ = _args[2];
lean_object* v_config_5568_ = _args[3];
lean_object* v_a_5569_ = _args[4];
lean_object* v_b_5570_ = _args[5];
lean_object* v___y_5571_ = _args[6];
lean_object* v___y_5572_ = _args[7];
lean_object* v___y_5573_ = _args[8];
lean_object* v___y_5574_ = _args[9];
lean_object* v___y_5575_ = _args[10];
lean_object* v___y_5576_ = _args[11];
lean_object* v___y_5577_ = _args[12];
lean_object* v___y_5578_ = _args[13];
lean_object* v___y_5579_ = _args[14];
lean_object* v___y_5580_ = _args[15];
lean_object* v___y_5581_ = _args[16];
lean_object* v___y_5582_ = _args[17];
lean_object* v___y_5583_ = _args[18];
_start:
{
lean_object* v_res_5584_; 
v_res_5584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5565_, v___x_5566_, v_methods_5567_, v_config_5568_, v_a_5569_, v_b_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_);
lean_dec(v___y_5582_);
lean_dec_ref(v___y_5581_);
lean_dec(v___y_5580_);
lean_dec_ref(v___y_5579_);
lean_dec(v___y_5578_);
lean_dec_ref(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec_ref(v___y_5575_);
lean_dec(v___y_5574_);
lean_dec(v___y_5573_);
lean_dec_ref(v___y_5572_);
lean_dec(v___y_5571_);
lean_dec_ref(v___x_5566_);
lean_dec(v_upperBound_5565_);
return v_res_5584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5585_, lean_object* v_config_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_){
_start:
{
lean_object* v___x_5600_; lean_object* v_hypotheses_5601_; lean_object* v___x_5602_; lean_object* v_newHyps_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___x_5600_ = lean_st_ref_get(v_a_5589_);
v_hypotheses_5601_ = lean_ctor_get(v___x_5600_, 3);
lean_inc_ref(v_hypotheses_5601_);
lean_dec(v___x_5600_);
v___x_5602_ = lean_array_get_size(v_hypotheses_5601_);
v_newHyps_5603_ = lean_mk_empty_array_with_capacity(v___x_5602_);
v___x_5604_ = lean_unsigned_to_nat(0u);
v___x_5605_ = lean_box(0);
v___x_5606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5606_, 0, v___x_5605_);
lean_ctor_set(v___x_5606_, 1, v_newHyps_5603_);
v___x_5607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5602_, v_hypotheses_5601_, v_methods_5585_, v_config_5586_, v___x_5604_, v___x_5606_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_);
lean_dec_ref(v_hypotheses_5601_);
if (lean_obj_tag(v___x_5607_) == 0)
{
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5637_; 
v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
v_isSharedCheck_5637_ = !lean_is_exclusive(v___x_5607_);
if (v_isSharedCheck_5637_ == 0)
{
v___x_5610_ = v___x_5607_;
v_isShared_5611_ = v_isSharedCheck_5637_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5607_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5637_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v_fst_5612_; 
v_fst_5612_ = lean_ctor_get(v_a_5608_, 0);
if (lean_obj_tag(v_fst_5612_) == 0)
{
lean_object* v_snd_5613_; lean_object* v___x_5614_; lean_object* v_caches_5615_; lean_object* v_typeAnalysis_5616_; lean_object* v_target_5617_; uint8_t v_didChange_5618_; lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5631_; 
v_snd_5613_ = lean_ctor_get(v_a_5608_, 1);
lean_inc(v_snd_5613_);
lean_dec(v_a_5608_);
v___x_5614_ = lean_st_ref_take(v_a_5589_);
v_caches_5615_ = lean_ctor_get(v___x_5614_, 0);
v_typeAnalysis_5616_ = lean_ctor_get(v___x_5614_, 1);
v_target_5617_ = lean_ctor_get(v___x_5614_, 2);
v_didChange_5618_ = lean_ctor_get_uint8(v___x_5614_, sizeof(void*)*4);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5614_);
if (v_isSharedCheck_5631_ == 0)
{
lean_object* v_unused_5632_; 
v_unused_5632_ = lean_ctor_get(v___x_5614_, 3);
lean_dec(v_unused_5632_);
v___x_5620_ = v___x_5614_;
v_isShared_5621_ = v_isSharedCheck_5631_;
goto v_resetjp_5619_;
}
else
{
lean_inc(v_target_5617_);
lean_inc(v_typeAnalysis_5616_);
lean_inc(v_caches_5615_);
lean_dec(v___x_5614_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5631_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5623_; 
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 3, v_snd_5613_);
v___x_5623_ = v___x_5620_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_caches_5615_);
lean_ctor_set(v_reuseFailAlloc_5630_, 1, v_typeAnalysis_5616_);
lean_ctor_set(v_reuseFailAlloc_5630_, 2, v_target_5617_);
lean_ctor_set(v_reuseFailAlloc_5630_, 3, v_snd_5613_);
lean_ctor_set_uint8(v_reuseFailAlloc_5630_, sizeof(void*)*4, v_didChange_5618_);
v___x_5623_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
lean_object* v___x_5624_; uint8_t v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5628_; 
v___x_5624_ = lean_st_ref_put(v_a_5589_, v___x_5623_);
v___x_5625_ = 0;
v___x_5626_ = lean_box(v___x_5625_);
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 0, v___x_5626_);
v___x_5628_ = v___x_5610_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v___x_5626_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
}
else
{
lean_object* v_val_5633_; lean_object* v___x_5635_; 
lean_inc_ref(v_fst_5612_);
lean_dec(v_a_5608_);
v_val_5633_ = lean_ctor_get(v_fst_5612_, 0);
lean_inc(v_val_5633_);
lean_dec_ref_known(v_fst_5612_, 1);
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 0, v_val_5633_);
v___x_5635_ = v___x_5610_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_val_5633_);
v___x_5635_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
return v___x_5635_;
}
}
}
}
else
{
lean_object* v_a_5638_; lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5645_; 
v_a_5638_ = lean_ctor_get(v___x_5607_, 0);
v_isSharedCheck_5645_ = !lean_is_exclusive(v___x_5607_);
if (v_isSharedCheck_5645_ == 0)
{
v___x_5640_ = v___x_5607_;
v_isShared_5641_ = v_isSharedCheck_5645_;
goto v_resetjp_5639_;
}
else
{
lean_inc(v_a_5638_);
lean_dec(v___x_5607_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5645_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
lean_object* v___x_5643_; 
if (v_isShared_5641_ == 0)
{
v___x_5643_ = v___x_5640_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v_a_5638_);
v___x_5643_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
return v___x_5643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5646_, lean_object* v_config_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_){
_start:
{
lean_object* v_res_5661_; 
v_res_5661_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5646_, v_config_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_);
lean_dec(v_a_5659_);
lean_dec_ref(v_a_5658_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
lean_dec(v_a_5655_);
lean_dec_ref(v_a_5654_);
lean_dec(v_a_5653_);
lean_dec_ref(v_a_5652_);
lean_dec(v_a_5651_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
lean_dec(v_a_5648_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5662_, lean_object* v_msg_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_){
_start:
{
lean_object* v___x_5677_; 
v___x_5677_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5662_, v_msg_5663_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_);
return v___x_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5678_, lean_object* v_msg_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
lean_object* v_res_5693_; 
v_res_5693_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5678_, v_msg_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
lean_dec(v___y_5691_);
lean_dec_ref(v___y_5690_);
lean_dec(v___y_5689_);
lean_dec_ref(v___y_5688_);
lean_dec(v___y_5687_);
lean_dec_ref(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec(v___y_5680_);
return v_res_5693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5694_, lean_object* v___x_5695_, lean_object* v_methods_5696_, lean_object* v_config_5697_, lean_object* v_inst_5698_, lean_object* v_R_5699_, lean_object* v_a_5700_, lean_object* v_b_5701_, lean_object* v_c_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_){
_start:
{
lean_object* v___x_5716_; 
v___x_5716_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5694_, v___x_5695_, v_methods_5696_, v_config_5697_, v_a_5700_, v_b_5701_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5717_ = _args[0];
lean_object* v___x_5718_ = _args[1];
lean_object* v_methods_5719_ = _args[2];
lean_object* v_config_5720_ = _args[3];
lean_object* v_inst_5721_ = _args[4];
lean_object* v_R_5722_ = _args[5];
lean_object* v_a_5723_ = _args[6];
lean_object* v_b_5724_ = _args[7];
lean_object* v_c_5725_ = _args[8];
lean_object* v___y_5726_ = _args[9];
lean_object* v___y_5727_ = _args[10];
lean_object* v___y_5728_ = _args[11];
lean_object* v___y_5729_ = _args[12];
lean_object* v___y_5730_ = _args[13];
lean_object* v___y_5731_ = _args[14];
lean_object* v___y_5732_ = _args[15];
lean_object* v___y_5733_ = _args[16];
lean_object* v___y_5734_ = _args[17];
lean_object* v___y_5735_ = _args[18];
lean_object* v___y_5736_ = _args[19];
lean_object* v___y_5737_ = _args[20];
lean_object* v___y_5738_ = _args[21];
_start:
{
lean_object* v_res_5739_; 
v_res_5739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5717_, v___x_5718_, v_methods_5719_, v_config_5720_, v_inst_5721_, v_R_5722_, v_a_5723_, v_b_5724_, v_c_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_);
lean_dec(v___y_5737_);
lean_dec_ref(v___y_5736_);
lean_dec(v___y_5735_);
lean_dec_ref(v___y_5734_);
lean_dec(v___y_5733_);
lean_dec_ref(v___y_5732_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec(v___y_5728_);
lean_dec_ref(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v___x_5718_);
lean_dec(v_upperBound_5717_);
return v_res_5739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5740_, lean_object* v_config_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_){
_start:
{
lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5754_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5755_ = lean_st_mk_ref(v___x_5754_);
v___x_5756_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5740_, v_config_5741_, v___x_5755_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_);
if (lean_obj_tag(v___x_5756_) == 0)
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5765_; 
v_a_5757_ = lean_ctor_get(v___x_5756_, 0);
v_isSharedCheck_5765_ = !lean_is_exclusive(v___x_5756_);
if (v_isSharedCheck_5765_ == 0)
{
v___x_5759_ = v___x_5756_;
v_isShared_5760_ = v_isSharedCheck_5765_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5756_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5765_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5761_; lean_object* v___x_5763_; 
v___x_5761_ = lean_st_ref_get(v___x_5755_);
lean_dec(v___x_5755_);
lean_dec(v___x_5761_);
if (v_isShared_5760_ == 0)
{
v___x_5763_ = v___x_5759_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5764_; 
v_reuseFailAlloc_5764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5764_, 0, v_a_5757_);
v___x_5763_ = v_reuseFailAlloc_5764_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
return v___x_5763_;
}
}
}
else
{
lean_dec(v___x_5755_);
return v___x_5756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5766_, lean_object* v_config_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_){
_start:
{
lean_object* v_res_5780_; 
v_res_5780_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5766_, v_config_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_);
lean_dec(v_a_5778_);
lean_dec_ref(v_a_5777_);
lean_dec(v_a_5776_);
lean_dec_ref(v_a_5775_);
lean_dec(v_a_5774_);
lean_dec_ref(v_a_5773_);
lean_dec(v_a_5772_);
lean_dec_ref(v_a_5771_);
lean_dec(v_a_5770_);
lean_dec(v_a_5769_);
lean_dec_ref(v_a_5768_);
return v_res_5780_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5782_; lean_object* v___x_5783_; 
v___x_5782_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5783_ = l_Lean_stringToMessageData(v___x_5782_);
return v___x_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5784_, lean_object* v_x_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; 
v___x_5798_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5799_ = l_Lean_MessageData_ofName(v_name_5784_);
v___x_5800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5798_);
lean_ctor_set(v___x_5800_, 1, v___x_5799_);
v___x_5801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5801_, 0, v___x_5800_);
return v___x_5801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5802_, lean_object* v_x_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_){
_start:
{
lean_object* v_res_5816_; 
v_res_5816_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5802_, v_x_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
lean_dec(v___y_5812_);
lean_dec_ref(v___y_5811_);
lean_dec(v___y_5810_);
lean_dec_ref(v___y_5809_);
lean_dec(v___y_5808_);
lean_dec_ref(v___y_5807_);
lean_dec(v___y_5806_);
lean_dec(v___y_5805_);
lean_dec_ref(v___y_5804_);
lean_dec_ref(v_x_5803_);
return v_res_5816_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5817_; 
v___x_5817_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_5817_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; 
v___x_5818_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5819_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5818_);
return v___x_5819_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5821_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5820_);
return v___x_5821_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5823_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5822_);
return v___x_5823_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5824_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5825_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5824_);
return v___x_5825_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5826_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5827_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5826_);
return v___x_5827_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5828_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5829_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5828_);
return v___x_5829_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; 
v___x_5830_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5831_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5830_);
return v___x_5831_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5833_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5832_);
return v___x_5833_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; 
v___x_5834_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5835_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5834_);
return v___x_5835_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5836_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5837_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5836_);
return v___x_5837_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5839_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5838_);
return v___x_5839_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5841_; double v___x_5842_; 
v___x_5841_ = lean_unsigned_to_nat(1000000000u);
v___x_5842_ = lean_float_of_nat(v___x_5841_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_){
_start:
{
lean_object* v___x_5856_; lean_object* v_toApplicative_5857_; lean_object* v_toFunctor_5858_; lean_object* v_toSeq_5859_; lean_object* v_toSeqLeft_5860_; lean_object* v_toSeqRight_5861_; lean_object* v___f_5862_; lean_object* v___f_5863_; lean_object* v___f_5864_; lean_object* v___f_5865_; lean_object* v___x_5866_; lean_object* v___f_5867_; lean_object* v___f_5868_; lean_object* v___f_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v_toApplicative_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_6016_; 
v___x_5856_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5857_ = lean_ctor_get(v___x_5856_, 0);
v_toFunctor_5858_ = lean_ctor_get(v_toApplicative_5857_, 0);
v_toSeq_5859_ = lean_ctor_get(v_toApplicative_5857_, 2);
v_toSeqLeft_5860_ = lean_ctor_get(v_toApplicative_5857_, 3);
v_toSeqRight_5861_ = lean_ctor_get(v_toApplicative_5857_, 4);
v___f_5862_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5863_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5858_, 2);
v___f_5864_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5864_, 0, v_toFunctor_5858_);
v___f_5865_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5865_, 0, v_toFunctor_5858_);
v___x_5866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5866_, 0, v___f_5864_);
lean_ctor_set(v___x_5866_, 1, v___f_5865_);
lean_inc(v_toSeqRight_5861_);
v___f_5867_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5867_, 0, v_toSeqRight_5861_);
lean_inc(v_toSeqLeft_5860_);
v___f_5868_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5868_, 0, v_toSeqLeft_5860_);
lean_inc(v_toSeq_5859_);
v___f_5869_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5869_, 0, v_toSeq_5859_);
v___x_5870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5870_, 0, v___x_5866_);
lean_ctor_set(v___x_5870_, 1, v___f_5862_);
lean_ctor_set(v___x_5870_, 2, v___f_5869_);
lean_ctor_set(v___x_5870_, 3, v___f_5868_);
lean_ctor_set(v___x_5870_, 4, v___f_5867_);
v___x_5871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5871_, 0, v___x_5870_);
lean_ctor_set(v___x_5871_, 1, v___f_5863_);
v___x_5872_ = l_StateRefT_x27_instMonad___redArg(v___x_5871_);
v_toApplicative_5873_ = lean_ctor_get(v___x_5872_, 0);
v_isSharedCheck_6016_ = !lean_is_exclusive(v___x_5872_);
if (v_isSharedCheck_6016_ == 0)
{
lean_object* v_unused_6017_; 
v_unused_6017_ = lean_ctor_get(v___x_5872_, 1);
lean_dec(v_unused_6017_);
v___x_5875_ = v___x_5872_;
v_isShared_5876_ = v_isSharedCheck_6016_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_toApplicative_5873_);
lean_dec(v___x_5872_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_6016_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
lean_object* v_toFunctor_5877_; lean_object* v_toSeq_5878_; lean_object* v_toSeqLeft_5879_; lean_object* v_toSeqRight_5880_; lean_object* v___x_5882_; uint8_t v_isShared_5883_; uint8_t v_isSharedCheck_6014_; 
v_toFunctor_5877_ = lean_ctor_get(v_toApplicative_5873_, 0);
v_toSeq_5878_ = lean_ctor_get(v_toApplicative_5873_, 2);
v_toSeqLeft_5879_ = lean_ctor_get(v_toApplicative_5873_, 3);
v_toSeqRight_5880_ = lean_ctor_get(v_toApplicative_5873_, 4);
v_isSharedCheck_6014_ = !lean_is_exclusive(v_toApplicative_5873_);
if (v_isSharedCheck_6014_ == 0)
{
lean_object* v_unused_6015_; 
v_unused_6015_ = lean_ctor_get(v_toApplicative_5873_, 1);
lean_dec(v_unused_6015_);
v___x_5882_ = v_toApplicative_5873_;
v_isShared_5883_ = v_isSharedCheck_6014_;
goto v_resetjp_5881_;
}
else
{
lean_inc(v_toSeqRight_5880_);
lean_inc(v_toSeqLeft_5879_);
lean_inc(v_toSeq_5878_);
lean_inc(v_toFunctor_5877_);
lean_dec(v_toApplicative_5873_);
v___x_5882_ = lean_box(0);
v_isShared_5883_ = v_isSharedCheck_6014_;
goto v_resetjp_5881_;
}
v_resetjp_5881_:
{
lean_object* v___f_5884_; lean_object* v___f_5885_; lean_object* v___f_5886_; lean_object* v___f_5887_; lean_object* v___x_5888_; lean_object* v___f_5889_; lean_object* v___f_5890_; lean_object* v___f_5891_; lean_object* v___x_5893_; 
v___f_5884_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5885_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5877_);
v___f_5886_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5886_, 0, v_toFunctor_5877_);
v___f_5887_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5887_, 0, v_toFunctor_5877_);
v___x_5888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5888_, 0, v___f_5886_);
lean_ctor_set(v___x_5888_, 1, v___f_5887_);
v___f_5889_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5889_, 0, v_toSeqRight_5880_);
v___f_5890_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5890_, 0, v_toSeqLeft_5879_);
v___f_5891_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5891_, 0, v_toSeq_5878_);
if (v_isShared_5883_ == 0)
{
lean_ctor_set(v___x_5882_, 4, v___f_5889_);
lean_ctor_set(v___x_5882_, 3, v___f_5890_);
lean_ctor_set(v___x_5882_, 2, v___f_5891_);
lean_ctor_set(v___x_5882_, 1, v___f_5884_);
lean_ctor_set(v___x_5882_, 0, v___x_5888_);
v___x_5893_ = v___x_5882_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v___x_5888_);
lean_ctor_set(v_reuseFailAlloc_6013_, 1, v___f_5884_);
lean_ctor_set(v_reuseFailAlloc_6013_, 2, v___f_5891_);
lean_ctor_set(v_reuseFailAlloc_6013_, 3, v___f_5890_);
lean_ctor_set(v_reuseFailAlloc_6013_, 4, v___f_5889_);
v___x_5893_ = v_reuseFailAlloc_6013_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
lean_object* v___x_5895_; 
if (v_isShared_5876_ == 0)
{
lean_ctor_set(v___x_5875_, 1, v___f_5885_);
lean_ctor_set(v___x_5875_, 0, v___x_5893_);
v___x_5895_ = v___x_5875_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_5893_);
lean_ctor_set(v_reuseFailAlloc_6012_, 1, v___f_5885_);
v___x_5895_ = v_reuseFailAlloc_6012_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v_toMonadRef_5905_; lean_object* v___x_5906_; lean_object* v_name_5907_; lean_object* v_run_x27_5908_; lean_object* v___x_5910_; uint8_t v_isShared_5911_; uint8_t v_isSharedCheck_6011_; 
v___x_5896_ = l_StateRefT_x27_instMonad___redArg(v___x_5895_);
v___x_5897_ = l_ReaderT_instMonad___redArg(v___x_5896_);
v___x_5898_ = l_StateRefT_x27_instMonad___redArg(v___x_5897_);
v___x_5899_ = l_ReaderT_instMonad___redArg(v___x_5898_);
v___x_5900_ = l_ReaderT_instMonad___redArg(v___x_5899_);
v___x_5901_ = l_StateRefT_x27_instMonad___redArg(v___x_5900_);
v___x_5902_ = l_ReaderT_instMonad___redArg(v___x_5901_);
v___x_5903_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5904_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_5905_ = lean_ctor_get(v___x_5904_, 0);
v___x_5906_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_name_5907_ = lean_ctor_get(v_pass_5843_, 0);
v_run_x27_5908_ = lean_ctor_get(v_pass_5843_, 1);
v_isSharedCheck_6011_ = !lean_is_exclusive(v_pass_5843_);
if (v_isSharedCheck_6011_ == 0)
{
v___x_5910_ = v_pass_5843_;
v_isShared_5911_ = v_isSharedCheck_6011_;
goto v_resetjp_5909_;
}
else
{
lean_inc(v_run_x27_5908_);
lean_inc(v_name_5907_);
lean_dec(v_pass_5843_);
v___x_5910_ = lean_box(0);
v_isShared_5911_ = v_isSharedCheck_6011_;
goto v_resetjp_5909_;
}
v_resetjp_5909_:
{
lean_object* v___x_5912_; lean_object* v_options_5913_; uint8_t v_hasTrace_5914_; 
v___x_5912_ = l_Lean_KVMap_instValueBool;
v_options_5913_ = lean_ctor_get(v_a_5853_, 1);
v_hasTrace_5914_ = lean_ctor_get_uint8(v_options_5913_, sizeof(void*)*1);
if (v_hasTrace_5914_ == 0)
{
lean_object* v___x_5915_; 
lean_del_object(v___x_5910_);
lean_dec(v_name_5907_);
lean_dec_ref(v___x_5902_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc(v_a_5845_);
lean_inc_ref(v_a_5844_);
v___x_5915_ = lean_apply_12(v_run_x27_5908_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, lean_box(0));
return v___x_5915_;
}
else
{
lean_object* v_toCold_5916_; lean_object* v_inheritedTraceOptions_5917_; lean_object* v___f_5918_; lean_object* v___f_5919_; lean_object* v___f_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; uint8_t v___x_5924_; lean_object* v___y_5926_; lean_object* v___y_5927_; lean_object* v_a_5928_; lean_object* v___y_5944_; lean_object* v___y_5945_; lean_object* v_a_5946_; 
v_toCold_5916_ = lean_ctor_get(v_a_5853_, 0);
v_inheritedTraceOptions_5917_ = lean_ctor_get(v_toCold_5916_, 4);
v___f_5918_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5918_, 0, v_name_5907_);
v___f_5919_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_5920_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5921_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5922_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5923_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5924_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5917_, v_options_5913_, v___x_5923_);
if (v___x_5924_ == 0)
{
lean_object* v___x_6007_; lean_object* v___x_6008_; uint8_t v___x_6009_; 
v___x_6007_ = l_Lean_trace_profiler;
v___x_6008_ = l_Lean_Option_get___redArg(v___x_5912_, v_options_5913_, v___x_6007_);
v___x_6009_ = lean_unbox(v___x_6008_);
lean_dec(v___x_6008_);
if (v___x_6009_ == 0)
{
lean_object* v___x_6010_; 
lean_dec_ref(v___f_5918_);
lean_del_object(v___x_5910_);
lean_dec_ref(v___x_5902_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc(v_a_5845_);
lean_inc_ref(v_a_5844_);
v___x_6010_ = lean_apply_12(v_run_x27_5908_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, lean_box(0));
return v___x_6010_;
}
else
{
goto v___jp_5956_;
}
}
else
{
goto v___jp_5956_;
}
v___jp_5925_:
{
lean_object* v___x_5929_; double v___x_5930_; double v___x_5931_; double v___x_5932_; double v___x_5933_; double v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5938_; 
v___x_5929_ = lean_io_mono_nanos_now();
v___x_5930_ = lean_float_of_nat(v___y_5927_);
v___x_5931_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5932_ = lean_float_div(v___x_5930_, v___x_5931_);
v___x_5933_ = lean_float_of_nat(v___x_5929_);
v___x_5934_ = lean_float_div(v___x_5933_, v___x_5931_);
v___x_5935_ = lean_box_float(v___x_5932_);
v___x_5936_ = lean_box_float(v___x_5934_);
if (v_isShared_5911_ == 0)
{
lean_ctor_set(v___x_5910_, 1, v___x_5936_);
lean_ctor_set(v___x_5910_, 0, v___x_5935_);
v___x_5938_ = v___x_5910_;
goto v_reusejp_5937_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v___x_5935_);
lean_ctor_set(v_reuseFailAlloc_5942_, 1, v___x_5936_);
v___x_5938_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5937_;
}
v_reusejp_5937_:
{
lean_object* v___x_5939_; lean_object* v___x_28809__overap_5940_; lean_object* v___x_5941_; 
v___x_5939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5939_, 0, v_a_5928_);
lean_ctor_set(v___x_5939_, 1, v___x_5938_);
lean_inc_ref(v_toMonadRef_5905_);
v___x_28809__overap_5940_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5902_, v___x_5903_, v_toMonadRef_5905_, v___f_5919_, lean_box(0), v___x_5906_, v___f_5920_, v___x_5921_, v_hasTrace_5914_, v___x_5922_, v_options_5913_, v___x_5924_, v___y_5926_, v___f_5918_, v___x_5939_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc(v_a_5845_);
lean_inc_ref(v_a_5844_);
v___x_5941_ = lean_apply_12(v___x_28809__overap_5940_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, lean_box(0));
return v___x_5941_;
}
}
v___jp_5943_:
{
lean_object* v___x_5947_; double v___x_5948_; double v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_28830__overap_5954_; lean_object* v___x_5955_; 
v___x_5947_ = lean_io_get_num_heartbeats();
v___x_5948_ = lean_float_of_nat(v___y_5945_);
v___x_5949_ = lean_float_of_nat(v___x_5947_);
v___x_5950_ = lean_box_float(v___x_5948_);
v___x_5951_ = lean_box_float(v___x_5949_);
v___x_5952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5950_);
lean_ctor_set(v___x_5952_, 1, v___x_5951_);
v___x_5953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5953_, 0, v_a_5946_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
lean_inc_ref(v_toMonadRef_5905_);
v___x_28830__overap_5954_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5902_, v___x_5903_, v_toMonadRef_5905_, v___f_5919_, lean_box(0), v___x_5906_, v___f_5920_, v___x_5921_, v_hasTrace_5914_, v___x_5922_, v_options_5913_, v___x_5924_, v___y_5944_, v___f_5918_, v___x_5953_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc(v_a_5845_);
lean_inc_ref(v_a_5844_);
v___x_5955_ = lean_apply_12(v___x_28830__overap_5954_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, lean_box(0));
return v___x_5955_;
}
v___jp_5956_:
{
lean_object* v___x_28787__overap_5957_; lean_object* v___x_5958_; 
lean_inc_ref(v___x_5902_);
v___x_28787__overap_5957_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5902_, v___x_5903_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc(v_a_5845_);
lean_inc_ref(v_a_5844_);
v___x_5958_ = lean_apply_12(v___x_28787__overap_5957_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, lean_box(0));
if (lean_obj_tag(v___x_5958_) == 0)
{
lean_object* v_a_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; uint8_t v___x_5962_; 
v_a_5959_ = lean_ctor_get(v___x_5958_, 0);
lean_inc(v_a_5959_);
lean_dec_ref_known(v___x_5958_, 1);
v___x_5960_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5961_ = l_Lean_Option_get___redArg(v___x_5912_, v_options_5913_, v___x_5960_);
v___x_5962_ = lean_unbox(v___x_5961_);
lean_dec(v___x_5961_);
if (v___x_5962_ == 0)
{
lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5963_ = lean_io_mono_nanos_now();
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc(v_a_5845_);
lean_inc_ref(v_a_5844_);
v___x_5964_ = lean_apply_12(v_run_x27_5908_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, lean_box(0));
if (lean_obj_tag(v___x_5964_) == 0)
{
lean_object* v_a_5965_; lean_object* v___x_5967_; uint8_t v_isShared_5968_; uint8_t v_isSharedCheck_5972_; 
v_a_5965_ = lean_ctor_get(v___x_5964_, 0);
v_isSharedCheck_5972_ = !lean_is_exclusive(v___x_5964_);
if (v_isSharedCheck_5972_ == 0)
{
v___x_5967_ = v___x_5964_;
v_isShared_5968_ = v_isSharedCheck_5972_;
goto v_resetjp_5966_;
}
else
{
lean_inc(v_a_5965_);
lean_dec(v___x_5964_);
v___x_5967_ = lean_box(0);
v_isShared_5968_ = v_isSharedCheck_5972_;
goto v_resetjp_5966_;
}
v_resetjp_5966_:
{
lean_object* v___x_5970_; 
if (v_isShared_5968_ == 0)
{
lean_ctor_set_tag(v___x_5967_, 1);
v___x_5970_ = v___x_5967_;
goto v_reusejp_5969_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_a_5965_);
v___x_5970_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5969_;
}
v_reusejp_5969_:
{
v___y_5926_ = v_a_5959_;
v___y_5927_ = v___x_5963_;
v_a_5928_ = v___x_5970_;
goto v___jp_5925_;
}
}
}
else
{
lean_object* v_a_5973_; lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_5980_; 
v_a_5973_ = lean_ctor_get(v___x_5964_, 0);
v_isSharedCheck_5980_ = !lean_is_exclusive(v___x_5964_);
if (v_isSharedCheck_5980_ == 0)
{
v___x_5975_ = v___x_5964_;
v_isShared_5976_ = v_isSharedCheck_5980_;
goto v_resetjp_5974_;
}
else
{
lean_inc(v_a_5973_);
lean_dec(v___x_5964_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_5980_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5978_; 
if (v_isShared_5976_ == 0)
{
lean_ctor_set_tag(v___x_5975_, 0);
v___x_5978_ = v___x_5975_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v_a_5973_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
v___y_5926_ = v_a_5959_;
v___y_5927_ = v___x_5963_;
v_a_5928_ = v___x_5978_;
goto v___jp_5925_;
}
}
}
}
else
{
lean_object* v___x_5981_; lean_object* v___x_5982_; 
lean_del_object(v___x_5910_);
v___x_5981_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc(v_a_5845_);
lean_inc_ref(v_a_5844_);
v___x_5982_ = lean_apply_12(v_run_x27_5908_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, lean_box(0));
if (lean_obj_tag(v___x_5982_) == 0)
{
lean_object* v_a_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5990_; 
v_a_5983_ = lean_ctor_get(v___x_5982_, 0);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5982_);
if (v_isSharedCheck_5990_ == 0)
{
v___x_5985_ = v___x_5982_;
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_a_5983_);
lean_dec(v___x_5982_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5988_; 
if (v_isShared_5986_ == 0)
{
lean_ctor_set_tag(v___x_5985_, 1);
v___x_5988_ = v___x_5985_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
v___y_5944_ = v_a_5959_;
v___y_5945_ = v___x_5981_;
v_a_5946_ = v___x_5988_;
goto v___jp_5943_;
}
}
}
else
{
lean_object* v_a_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_5998_; 
v_a_5991_ = lean_ctor_get(v___x_5982_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v___x_5982_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5993_ = v___x_5982_;
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_a_5991_);
lean_dec(v___x_5982_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v___x_5996_; 
if (v_isShared_5994_ == 0)
{
lean_ctor_set_tag(v___x_5993_, 0);
v___x_5996_ = v___x_5993_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_a_5991_);
v___x_5996_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
v___y_5944_ = v_a_5959_;
v___y_5945_ = v___x_5981_;
v_a_5946_ = v___x_5996_;
goto v___jp_5943_;
}
}
}
}
}
else
{
lean_object* v_a_5999_; lean_object* v___x_6001_; uint8_t v_isShared_6002_; uint8_t v_isSharedCheck_6006_; 
lean_dec_ref(v___f_5918_);
lean_del_object(v___x_5910_);
lean_dec_ref(v_run_x27_5908_);
lean_dec_ref(v___x_5902_);
v_a_5999_ = lean_ctor_get(v___x_5958_, 0);
v_isSharedCheck_6006_ = !lean_is_exclusive(v___x_5958_);
if (v_isSharedCheck_6006_ == 0)
{
v___x_6001_ = v___x_5958_;
v_isShared_6002_ = v_isSharedCheck_6006_;
goto v_resetjp_6000_;
}
else
{
lean_inc(v_a_5999_);
lean_dec(v___x_5958_);
v___x_6001_ = lean_box(0);
v_isShared_6002_ = v_isSharedCheck_6006_;
goto v_resetjp_6000_;
}
v_resetjp_6000_:
{
lean_object* v___x_6004_; 
if (v_isShared_6002_ == 0)
{
v___x_6004_ = v___x_6001_;
goto v_reusejp_6003_;
}
else
{
lean_object* v_reuseFailAlloc_6005_; 
v_reuseFailAlloc_6005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6005_, 0, v_a_5999_);
v___x_6004_ = v_reuseFailAlloc_6005_;
goto v_reusejp_6003_;
}
v_reusejp_6003_:
{
return v___x_6004_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_){
_start:
{
lean_object* v_res_6031_; 
v_res_6031_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6018_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_, v_a_6027_, v_a_6028_, v_a_6029_);
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6028_);
lean_dec(v_a_6027_);
lean_dec_ref(v_a_6026_);
lean_dec(v_a_6025_);
lean_dec_ref(v_a_6024_);
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec(v_a_6020_);
lean_dec_ref(v_a_6019_);
return v_res_6031_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6032_ = lean_unsigned_to_nat(32u);
v___x_6033_ = lean_mk_empty_array_with_capacity(v___x_6032_);
v___x_6034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6033_);
return v___x_6034_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6035_ = ((size_t)5ULL);
v___x_6036_ = lean_unsigned_to_nat(0u);
v___x_6037_ = lean_unsigned_to_nat(32u);
v___x_6038_ = lean_mk_empty_array_with_capacity(v___x_6037_);
v___x_6039_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6040_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6040_, 0, v___x_6039_);
lean_ctor_set(v___x_6040_, 1, v___x_6038_);
lean_ctor_set(v___x_6040_, 2, v___x_6036_);
lean_ctor_set(v___x_6040_, 3, v___x_6036_);
lean_ctor_set_usize(v___x_6040_, 4, v___x_6035_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6041_){
_start:
{
lean_object* v___x_6043_; lean_object* v_traceState_6044_; lean_object* v_traces_6045_; lean_object* v___x_6046_; lean_object* v_traceState_6047_; lean_object* v_env_6048_; lean_object* v_nextMacroScope_6049_; lean_object* v_ngen_6050_; lean_object* v_auxDeclNGen_6051_; lean_object* v_cache_6052_; lean_object* v_messages_6053_; lean_object* v_infoState_6054_; lean_object* v_snapshotTasks_6055_; lean_object* v___x_6057_; uint8_t v_isShared_6058_; uint8_t v_isSharedCheck_6074_; 
v___x_6043_ = lean_st_ref_get(v___y_6041_);
v_traceState_6044_ = lean_ctor_get(v___x_6043_, 4);
lean_inc_ref(v_traceState_6044_);
lean_dec(v___x_6043_);
v_traces_6045_ = lean_ctor_get(v_traceState_6044_, 0);
lean_inc_ref(v_traces_6045_);
lean_dec_ref(v_traceState_6044_);
v___x_6046_ = lean_st_ref_take(v___y_6041_);
v_traceState_6047_ = lean_ctor_get(v___x_6046_, 4);
v_env_6048_ = lean_ctor_get(v___x_6046_, 0);
v_nextMacroScope_6049_ = lean_ctor_get(v___x_6046_, 1);
v_ngen_6050_ = lean_ctor_get(v___x_6046_, 2);
v_auxDeclNGen_6051_ = lean_ctor_get(v___x_6046_, 3);
v_cache_6052_ = lean_ctor_get(v___x_6046_, 5);
v_messages_6053_ = lean_ctor_get(v___x_6046_, 6);
v_infoState_6054_ = lean_ctor_get(v___x_6046_, 7);
v_snapshotTasks_6055_ = lean_ctor_get(v___x_6046_, 8);
v_isSharedCheck_6074_ = !lean_is_exclusive(v___x_6046_);
if (v_isSharedCheck_6074_ == 0)
{
v___x_6057_ = v___x_6046_;
v_isShared_6058_ = v_isSharedCheck_6074_;
goto v_resetjp_6056_;
}
else
{
lean_inc(v_snapshotTasks_6055_);
lean_inc(v_infoState_6054_);
lean_inc(v_messages_6053_);
lean_inc(v_cache_6052_);
lean_inc(v_traceState_6047_);
lean_inc(v_auxDeclNGen_6051_);
lean_inc(v_ngen_6050_);
lean_inc(v_nextMacroScope_6049_);
lean_inc(v_env_6048_);
lean_dec(v___x_6046_);
v___x_6057_ = lean_box(0);
v_isShared_6058_ = v_isSharedCheck_6074_;
goto v_resetjp_6056_;
}
v_resetjp_6056_:
{
uint64_t v_tid_6059_; lean_object* v___x_6061_; uint8_t v_isShared_6062_; uint8_t v_isSharedCheck_6072_; 
v_tid_6059_ = lean_ctor_get_uint64(v_traceState_6047_, sizeof(void*)*1);
v_isSharedCheck_6072_ = !lean_is_exclusive(v_traceState_6047_);
if (v_isSharedCheck_6072_ == 0)
{
lean_object* v_unused_6073_; 
v_unused_6073_ = lean_ctor_get(v_traceState_6047_, 0);
lean_dec(v_unused_6073_);
v___x_6061_ = v_traceState_6047_;
v_isShared_6062_ = v_isSharedCheck_6072_;
goto v_resetjp_6060_;
}
else
{
lean_dec(v_traceState_6047_);
v___x_6061_ = lean_box(0);
v_isShared_6062_ = v_isSharedCheck_6072_;
goto v_resetjp_6060_;
}
v_resetjp_6060_:
{
lean_object* v___x_6063_; lean_object* v___x_6065_; 
v___x_6063_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6062_ == 0)
{
lean_ctor_set(v___x_6061_, 0, v___x_6063_);
v___x_6065_ = v___x_6061_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6071_; 
v_reuseFailAlloc_6071_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6071_, 0, v___x_6063_);
lean_ctor_set_uint64(v_reuseFailAlloc_6071_, sizeof(void*)*1, v_tid_6059_);
v___x_6065_ = v_reuseFailAlloc_6071_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
lean_object* v___x_6067_; 
if (v_isShared_6058_ == 0)
{
lean_ctor_set(v___x_6057_, 4, v___x_6065_);
v___x_6067_ = v___x_6057_;
goto v_reusejp_6066_;
}
else
{
lean_object* v_reuseFailAlloc_6070_; 
v_reuseFailAlloc_6070_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6070_, 0, v_env_6048_);
lean_ctor_set(v_reuseFailAlloc_6070_, 1, v_nextMacroScope_6049_);
lean_ctor_set(v_reuseFailAlloc_6070_, 2, v_ngen_6050_);
lean_ctor_set(v_reuseFailAlloc_6070_, 3, v_auxDeclNGen_6051_);
lean_ctor_set(v_reuseFailAlloc_6070_, 4, v___x_6065_);
lean_ctor_set(v_reuseFailAlloc_6070_, 5, v_cache_6052_);
lean_ctor_set(v_reuseFailAlloc_6070_, 6, v_messages_6053_);
lean_ctor_set(v_reuseFailAlloc_6070_, 7, v_infoState_6054_);
lean_ctor_set(v_reuseFailAlloc_6070_, 8, v_snapshotTasks_6055_);
v___x_6067_ = v_reuseFailAlloc_6070_;
goto v_reusejp_6066_;
}
v_reusejp_6066_:
{
lean_object* v___x_6068_; lean_object* v___x_6069_; 
v___x_6068_ = lean_st_ref_put(v___y_6041_, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6069_, 0, v_traces_6045_);
return v___x_6069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6075_, lean_object* v___y_6076_){
_start:
{
lean_object* v_res_6077_; 
v_res_6077_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6075_);
lean_dec(v___y_6075_);
return v_res_6077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_){
_start:
{
lean_object* v___x_6090_; 
v___x_6090_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6088_);
return v___x_6090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_){
_start:
{
lean_object* v_res_6103_; 
v_res_6103_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_);
lean_dec(v___y_6101_);
lean_dec_ref(v___y_6100_);
lean_dec(v___y_6099_);
lean_dec_ref(v___y_6098_);
lean_dec(v___y_6097_);
lean_dec_ref(v___y_6096_);
lean_dec(v___y_6095_);
lean_dec_ref(v___y_6094_);
lean_dec(v___y_6093_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
return v_res_6103_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6104_, lean_object* v_opt_6105_){
_start:
{
lean_object* v_name_6106_; lean_object* v_defValue_6107_; lean_object* v_map_6108_; lean_object* v___x_6109_; 
v_name_6106_ = lean_ctor_get(v_opt_6105_, 0);
v_defValue_6107_ = lean_ctor_get(v_opt_6105_, 1);
v_map_6108_ = lean_ctor_get(v_opts_6104_, 0);
v___x_6109_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6108_, v_name_6106_);
if (lean_obj_tag(v___x_6109_) == 0)
{
uint8_t v___x_6110_; 
v___x_6110_ = lean_unbox(v_defValue_6107_);
return v___x_6110_;
}
else
{
lean_object* v_val_6111_; 
v_val_6111_ = lean_ctor_get(v___x_6109_, 0);
lean_inc(v_val_6111_);
lean_dec_ref_known(v___x_6109_, 1);
if (lean_obj_tag(v_val_6111_) == 1)
{
uint8_t v_v_6112_; 
v_v_6112_ = lean_ctor_get_uint8(v_val_6111_, 0);
lean_dec_ref_known(v_val_6111_, 0);
return v_v_6112_;
}
else
{
uint8_t v___x_6113_; 
lean_dec(v_val_6111_);
v___x_6113_ = lean_unbox(v_defValue_6107_);
return v___x_6113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6114_, lean_object* v_opt_6115_){
_start:
{
uint8_t v_res_6116_; lean_object* v_r_6117_; 
v_res_6116_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6114_, v_opt_6115_);
lean_dec_ref(v_opt_6115_);
lean_dec_ref(v_opts_6114_);
v_r_6117_ = lean_box(v_res_6116_);
return v_r_6117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6118_, lean_object* v_msg_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_){
_start:
{
lean_object* v_ref_6125_; lean_object* v___x_6126_; lean_object* v_a_6127_; lean_object* v___x_6129_; uint8_t v_isShared_6130_; uint8_t v_isSharedCheck_6171_; 
v_ref_6125_ = lean_ctor_get(v___y_6122_, 4);
v___x_6126_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_);
v_a_6127_ = lean_ctor_get(v___x_6126_, 0);
v_isSharedCheck_6171_ = !lean_is_exclusive(v___x_6126_);
if (v_isSharedCheck_6171_ == 0)
{
v___x_6129_ = v___x_6126_;
v_isShared_6130_ = v_isSharedCheck_6171_;
goto v_resetjp_6128_;
}
else
{
lean_inc(v_a_6127_);
lean_dec(v___x_6126_);
v___x_6129_ = lean_box(0);
v_isShared_6130_ = v_isSharedCheck_6171_;
goto v_resetjp_6128_;
}
v_resetjp_6128_:
{
lean_object* v___x_6131_; lean_object* v_traceState_6132_; lean_object* v_env_6133_; lean_object* v_nextMacroScope_6134_; lean_object* v_ngen_6135_; lean_object* v_auxDeclNGen_6136_; lean_object* v_cache_6137_; lean_object* v_messages_6138_; lean_object* v_infoState_6139_; lean_object* v_snapshotTasks_6140_; lean_object* v___x_6142_; uint8_t v_isShared_6143_; uint8_t v_isSharedCheck_6170_; 
v___x_6131_ = lean_st_ref_take(v___y_6123_);
v_traceState_6132_ = lean_ctor_get(v___x_6131_, 4);
v_env_6133_ = lean_ctor_get(v___x_6131_, 0);
v_nextMacroScope_6134_ = lean_ctor_get(v___x_6131_, 1);
v_ngen_6135_ = lean_ctor_get(v___x_6131_, 2);
v_auxDeclNGen_6136_ = lean_ctor_get(v___x_6131_, 3);
v_cache_6137_ = lean_ctor_get(v___x_6131_, 5);
v_messages_6138_ = lean_ctor_get(v___x_6131_, 6);
v_infoState_6139_ = lean_ctor_get(v___x_6131_, 7);
v_snapshotTasks_6140_ = lean_ctor_get(v___x_6131_, 8);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___x_6131_);
if (v_isSharedCheck_6170_ == 0)
{
v___x_6142_ = v___x_6131_;
v_isShared_6143_ = v_isSharedCheck_6170_;
goto v_resetjp_6141_;
}
else
{
lean_inc(v_snapshotTasks_6140_);
lean_inc(v_infoState_6139_);
lean_inc(v_messages_6138_);
lean_inc(v_cache_6137_);
lean_inc(v_traceState_6132_);
lean_inc(v_auxDeclNGen_6136_);
lean_inc(v_ngen_6135_);
lean_inc(v_nextMacroScope_6134_);
lean_inc(v_env_6133_);
lean_dec(v___x_6131_);
v___x_6142_ = lean_box(0);
v_isShared_6143_ = v_isSharedCheck_6170_;
goto v_resetjp_6141_;
}
v_resetjp_6141_:
{
uint64_t v_tid_6144_; lean_object* v_traces_6145_; lean_object* v___x_6147_; uint8_t v_isShared_6148_; uint8_t v_isSharedCheck_6169_; 
v_tid_6144_ = lean_ctor_get_uint64(v_traceState_6132_, sizeof(void*)*1);
v_traces_6145_ = lean_ctor_get(v_traceState_6132_, 0);
v_isSharedCheck_6169_ = !lean_is_exclusive(v_traceState_6132_);
if (v_isSharedCheck_6169_ == 0)
{
v___x_6147_ = v_traceState_6132_;
v_isShared_6148_ = v_isSharedCheck_6169_;
goto v_resetjp_6146_;
}
else
{
lean_inc(v_traces_6145_);
lean_dec(v_traceState_6132_);
v___x_6147_ = lean_box(0);
v_isShared_6148_ = v_isSharedCheck_6169_;
goto v_resetjp_6146_;
}
v_resetjp_6146_:
{
lean_object* v___x_6149_; double v___x_6150_; uint8_t v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6159_; 
v___x_6149_ = lean_box(0);
v___x_6150_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6151_ = 0;
v___x_6152_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6153_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6153_, 0, v_cls_6118_);
lean_ctor_set(v___x_6153_, 1, v___x_6149_);
lean_ctor_set(v___x_6153_, 2, v___x_6152_);
lean_ctor_set_float(v___x_6153_, sizeof(void*)*3, v___x_6150_);
lean_ctor_set_float(v___x_6153_, sizeof(void*)*3 + 8, v___x_6150_);
lean_ctor_set_uint8(v___x_6153_, sizeof(void*)*3 + 16, v___x_6151_);
v___x_6154_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6155_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6153_);
lean_ctor_set(v___x_6155_, 1, v_a_6127_);
lean_ctor_set(v___x_6155_, 2, v___x_6154_);
lean_inc(v_ref_6125_);
v___x_6156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6156_, 0, v_ref_6125_);
lean_ctor_set(v___x_6156_, 1, v___x_6155_);
v___x_6157_ = l_Lean_PersistentArray_push___redArg(v_traces_6145_, v___x_6156_);
if (v_isShared_6148_ == 0)
{
lean_ctor_set(v___x_6147_, 0, v___x_6157_);
v___x_6159_ = v___x_6147_;
goto v_reusejp_6158_;
}
else
{
lean_object* v_reuseFailAlloc_6168_; 
v_reuseFailAlloc_6168_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6168_, 0, v___x_6157_);
lean_ctor_set_uint64(v_reuseFailAlloc_6168_, sizeof(void*)*1, v_tid_6144_);
v___x_6159_ = v_reuseFailAlloc_6168_;
goto v_reusejp_6158_;
}
v_reusejp_6158_:
{
lean_object* v___x_6161_; 
if (v_isShared_6143_ == 0)
{
lean_ctor_set(v___x_6142_, 4, v___x_6159_);
v___x_6161_ = v___x_6142_;
goto v_reusejp_6160_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v_env_6133_);
lean_ctor_set(v_reuseFailAlloc_6167_, 1, v_nextMacroScope_6134_);
lean_ctor_set(v_reuseFailAlloc_6167_, 2, v_ngen_6135_);
lean_ctor_set(v_reuseFailAlloc_6167_, 3, v_auxDeclNGen_6136_);
lean_ctor_set(v_reuseFailAlloc_6167_, 4, v___x_6159_);
lean_ctor_set(v_reuseFailAlloc_6167_, 5, v_cache_6137_);
lean_ctor_set(v_reuseFailAlloc_6167_, 6, v_messages_6138_);
lean_ctor_set(v_reuseFailAlloc_6167_, 7, v_infoState_6139_);
lean_ctor_set(v_reuseFailAlloc_6167_, 8, v_snapshotTasks_6140_);
v___x_6161_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6160_;
}
v_reusejp_6160_:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6165_; 
v___x_6162_ = lean_st_ref_put(v___y_6123_, v___x_6161_);
v___x_6163_ = lean_box(0);
if (v_isShared_6130_ == 0)
{
lean_ctor_set(v___x_6129_, 0, v___x_6163_);
v___x_6165_ = v___x_6129_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v___x_6163_);
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
lean_object* v_toCold_6248_; lean_object* v_options_6249_; lean_object* v_currRecDepth_6250_; lean_object* v_maxRecDepth_6251_; lean_object* v_ref_6252_; lean_object* v_currNamespace_6253_; lean_object* v_openDecls_6254_; lean_object* v_initHeartbeats_6255_; lean_object* v_maxHeartbeats_6256_; lean_object* v_currMacroScope_6257_; uint8_t v_diag_6258_; uint8_t v_suppressElabErrors_6259_; lean_object* v___x_6260_; lean_object* v_traceState_6261_; lean_object* v_traces_6262_; lean_object* v_ref_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; size_t v_sz_6266_; size_t v___x_6267_; lean_object* v___x_6268_; lean_object* v_msg_6269_; lean_object* v___x_6270_; lean_object* v_a_6271_; lean_object* v___x_6273_; uint8_t v_isShared_6274_; uint8_t v_isSharedCheck_6308_; 
v_toCold_6248_ = lean_ctor_get(v___y_6245_, 0);
v_options_6249_ = lean_ctor_get(v___y_6245_, 1);
v_currRecDepth_6250_ = lean_ctor_get(v___y_6245_, 2);
v_maxRecDepth_6251_ = lean_ctor_get(v___y_6245_, 3);
v_ref_6252_ = lean_ctor_get(v___y_6245_, 4);
v_currNamespace_6253_ = lean_ctor_get(v___y_6245_, 5);
v_openDecls_6254_ = lean_ctor_get(v___y_6245_, 6);
v_initHeartbeats_6255_ = lean_ctor_get(v___y_6245_, 7);
v_maxHeartbeats_6256_ = lean_ctor_get(v___y_6245_, 8);
v_currMacroScope_6257_ = lean_ctor_get(v___y_6245_, 9);
v_diag_6258_ = lean_ctor_get_uint8(v___y_6245_, sizeof(void*)*10);
v_suppressElabErrors_6259_ = lean_ctor_get_uint8(v___y_6245_, sizeof(void*)*10 + 1);
v___x_6260_ = lean_st_ref_get(v___y_6246_);
v_traceState_6261_ = lean_ctor_get(v___x_6260_, 4);
lean_inc_ref(v_traceState_6261_);
lean_dec(v___x_6260_);
v_traces_6262_ = lean_ctor_get(v_traceState_6261_, 0);
lean_inc_ref(v_traces_6262_);
lean_dec_ref(v_traceState_6261_);
v_ref_6263_ = l_Lean_replaceRef(v_ref_6241_, v_ref_6252_);
lean_inc(v_currMacroScope_6257_);
lean_inc(v_maxHeartbeats_6256_);
lean_inc(v_initHeartbeats_6255_);
lean_inc(v_openDecls_6254_);
lean_inc(v_currNamespace_6253_);
lean_inc(v_maxRecDepth_6251_);
lean_inc(v_currRecDepth_6250_);
lean_inc_ref(v_options_6249_);
lean_inc_ref(v_toCold_6248_);
v___x_6264_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_6264_, 0, v_toCold_6248_);
lean_ctor_set(v___x_6264_, 1, v_options_6249_);
lean_ctor_set(v___x_6264_, 2, v_currRecDepth_6250_);
lean_ctor_set(v___x_6264_, 3, v_maxRecDepth_6251_);
lean_ctor_set(v___x_6264_, 4, v_ref_6263_);
lean_ctor_set(v___x_6264_, 5, v_currNamespace_6253_);
lean_ctor_set(v___x_6264_, 6, v_openDecls_6254_);
lean_ctor_set(v___x_6264_, 7, v_initHeartbeats_6255_);
lean_ctor_set(v___x_6264_, 8, v_maxHeartbeats_6256_);
lean_ctor_set(v___x_6264_, 9, v_currMacroScope_6257_);
lean_ctor_set_uint8(v___x_6264_, sizeof(void*)*10, v_diag_6258_);
lean_ctor_set_uint8(v___x_6264_, sizeof(void*)*10 + 1, v_suppressElabErrors_6259_);
v___x_6265_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6262_);
lean_dec_ref(v_traces_6262_);
v_sz_6266_ = lean_array_size(v___x_6265_);
v___x_6267_ = ((size_t)0ULL);
v___x_6268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6266_, v___x_6267_, v___x_6265_);
v_msg_6269_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6269_, 0, v_data_6240_);
lean_ctor_set(v_msg_6269_, 1, v_msg_6242_);
lean_ctor_set(v_msg_6269_, 2, v___x_6268_);
v___x_6270_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6269_, v___y_6243_, v___y_6244_, v___x_6264_, v___y_6246_);
lean_dec_ref_known(v___x_6264_, 10);
v_a_6271_ = lean_ctor_get(v___x_6270_, 0);
v_isSharedCheck_6308_ = !lean_is_exclusive(v___x_6270_);
if (v_isSharedCheck_6308_ == 0)
{
v___x_6273_ = v___x_6270_;
v_isShared_6274_ = v_isSharedCheck_6308_;
goto v_resetjp_6272_;
}
else
{
lean_inc(v_a_6271_);
lean_dec(v___x_6270_);
v___x_6273_ = lean_box(0);
v_isShared_6274_ = v_isSharedCheck_6308_;
goto v_resetjp_6272_;
}
v_resetjp_6272_:
{
lean_object* v___x_6275_; lean_object* v_traceState_6276_; lean_object* v_env_6277_; lean_object* v_nextMacroScope_6278_; lean_object* v_ngen_6279_; lean_object* v_auxDeclNGen_6280_; lean_object* v_cache_6281_; lean_object* v_messages_6282_; lean_object* v_infoState_6283_; lean_object* v_snapshotTasks_6284_; lean_object* v___x_6286_; uint8_t v_isShared_6287_; uint8_t v_isSharedCheck_6307_; 
v___x_6275_ = lean_st_ref_take(v___y_6246_);
v_traceState_6276_ = lean_ctor_get(v___x_6275_, 4);
v_env_6277_ = lean_ctor_get(v___x_6275_, 0);
v_nextMacroScope_6278_ = lean_ctor_get(v___x_6275_, 1);
v_ngen_6279_ = lean_ctor_get(v___x_6275_, 2);
v_auxDeclNGen_6280_ = lean_ctor_get(v___x_6275_, 3);
v_cache_6281_ = lean_ctor_get(v___x_6275_, 5);
v_messages_6282_ = lean_ctor_get(v___x_6275_, 6);
v_infoState_6283_ = lean_ctor_get(v___x_6275_, 7);
v_snapshotTasks_6284_ = lean_ctor_get(v___x_6275_, 8);
v_isSharedCheck_6307_ = !lean_is_exclusive(v___x_6275_);
if (v_isSharedCheck_6307_ == 0)
{
v___x_6286_ = v___x_6275_;
v_isShared_6287_ = v_isSharedCheck_6307_;
goto v_resetjp_6285_;
}
else
{
lean_inc(v_snapshotTasks_6284_);
lean_inc(v_infoState_6283_);
lean_inc(v_messages_6282_);
lean_inc(v_cache_6281_);
lean_inc(v_traceState_6276_);
lean_inc(v_auxDeclNGen_6280_);
lean_inc(v_ngen_6279_);
lean_inc(v_nextMacroScope_6278_);
lean_inc(v_env_6277_);
lean_dec(v___x_6275_);
v___x_6286_ = lean_box(0);
v_isShared_6287_ = v_isSharedCheck_6307_;
goto v_resetjp_6285_;
}
v_resetjp_6285_:
{
uint64_t v_tid_6288_; lean_object* v___x_6290_; uint8_t v_isShared_6291_; uint8_t v_isSharedCheck_6305_; 
v_tid_6288_ = lean_ctor_get_uint64(v_traceState_6276_, sizeof(void*)*1);
v_isSharedCheck_6305_ = !lean_is_exclusive(v_traceState_6276_);
if (v_isSharedCheck_6305_ == 0)
{
lean_object* v_unused_6306_; 
v_unused_6306_ = lean_ctor_get(v_traceState_6276_, 0);
lean_dec(v_unused_6306_);
v___x_6290_ = v_traceState_6276_;
v_isShared_6291_ = v_isSharedCheck_6305_;
goto v_resetjp_6289_;
}
else
{
lean_dec(v_traceState_6276_);
v___x_6290_ = lean_box(0);
v_isShared_6291_ = v_isSharedCheck_6305_;
goto v_resetjp_6289_;
}
v_resetjp_6289_:
{
lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6295_; 
v___x_6292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6292_, 0, v_ref_6241_);
lean_ctor_set(v___x_6292_, 1, v_a_6271_);
v___x_6293_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6239_, v___x_6292_);
if (v_isShared_6291_ == 0)
{
lean_ctor_set(v___x_6290_, 0, v___x_6293_);
v___x_6295_ = v___x_6290_;
goto v_reusejp_6294_;
}
else
{
lean_object* v_reuseFailAlloc_6304_; 
v_reuseFailAlloc_6304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6304_, 0, v___x_6293_);
lean_ctor_set_uint64(v_reuseFailAlloc_6304_, sizeof(void*)*1, v_tid_6288_);
v___x_6295_ = v_reuseFailAlloc_6304_;
goto v_reusejp_6294_;
}
v_reusejp_6294_:
{
lean_object* v___x_6297_; 
if (v_isShared_6287_ == 0)
{
lean_ctor_set(v___x_6286_, 4, v___x_6295_);
v___x_6297_ = v___x_6286_;
goto v_reusejp_6296_;
}
else
{
lean_object* v_reuseFailAlloc_6303_; 
v_reuseFailAlloc_6303_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6303_, 0, v_env_6277_);
lean_ctor_set(v_reuseFailAlloc_6303_, 1, v_nextMacroScope_6278_);
lean_ctor_set(v_reuseFailAlloc_6303_, 2, v_ngen_6279_);
lean_ctor_set(v_reuseFailAlloc_6303_, 3, v_auxDeclNGen_6280_);
lean_ctor_set(v_reuseFailAlloc_6303_, 4, v___x_6295_);
lean_ctor_set(v_reuseFailAlloc_6303_, 5, v_cache_6281_);
lean_ctor_set(v_reuseFailAlloc_6303_, 6, v_messages_6282_);
lean_ctor_set(v_reuseFailAlloc_6303_, 7, v_infoState_6283_);
lean_ctor_set(v_reuseFailAlloc_6303_, 8, v_snapshotTasks_6284_);
v___x_6297_ = v_reuseFailAlloc_6303_;
goto v_reusejp_6296_;
}
v_reusejp_6296_:
{
lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6301_; 
v___x_6298_ = lean_st_ref_put(v___y_6246_, v___x_6297_);
v___x_6299_ = lean_box(0);
if (v_isShared_6274_ == 0)
{
lean_ctor_set(v___x_6273_, 0, v___x_6299_);
v___x_6301_ = v___x_6273_;
goto v_reusejp_6300_;
}
else
{
lean_object* v_reuseFailAlloc_6302_; 
v_reuseFailAlloc_6302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6302_, 0, v___x_6299_);
v___x_6301_ = v_reuseFailAlloc_6302_;
goto v_reusejp_6300_;
}
v_reusejp_6300_:
{
return v___x_6301_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6309_, lean_object* v_data_6310_, lean_object* v_ref_6311_, lean_object* v_msg_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_){
_start:
{
lean_object* v_res_6318_; 
v_res_6318_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6309_, v_data_6310_, v_ref_6311_, v_msg_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_);
lean_dec(v___y_6316_);
lean_dec_ref(v___y_6315_);
lean_dec(v___y_6314_);
lean_dec_ref(v___y_6313_);
return v_res_6318_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; 
v___x_6320_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6321_ = l_Lean_stringToMessageData(v___x_6320_);
return v___x_6321_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6322_; double v___x_6323_; 
v___x_6322_ = lean_unsigned_to_nat(1000u);
v___x_6323_ = lean_float_of_nat(v___x_6322_);
return v___x_6323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6324_, uint8_t v_collapsed_6325_, lean_object* v_tag_6326_, lean_object* v_opts_6327_, uint8_t v_clsEnabled_6328_, lean_object* v_oldTraces_6329_, lean_object* v_msg_6330_, lean_object* v_resStartStop_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_){
_start:
{
lean_object* v_fst_6344_; lean_object* v_snd_6345_; lean_object* v___y_6347_; lean_object* v___y_6348_; lean_object* v_data_6349_; lean_object* v_fst_6360_; lean_object* v_snd_6361_; lean_object* v___x_6362_; uint8_t v___x_6363_; lean_object* v___y_6365_; lean_object* v_a_6366_; uint8_t v___y_6381_; double v___y_6412_; 
v_fst_6344_ = lean_ctor_get(v_resStartStop_6331_, 0);
lean_inc(v_fst_6344_);
v_snd_6345_ = lean_ctor_get(v_resStartStop_6331_, 1);
lean_inc(v_snd_6345_);
lean_dec_ref(v_resStartStop_6331_);
v_fst_6360_ = lean_ctor_get(v_snd_6345_, 0);
lean_inc(v_fst_6360_);
v_snd_6361_ = lean_ctor_get(v_snd_6345_, 1);
lean_inc(v_snd_6361_);
lean_dec(v_snd_6345_);
v___x_6362_ = l_Lean_trace_profiler;
v___x_6363_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6327_, v___x_6362_);
if (v___x_6363_ == 0)
{
v___y_6381_ = v___x_6363_;
goto v___jp_6380_;
}
else
{
lean_object* v___x_6417_; uint8_t v___x_6418_; 
v___x_6417_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6418_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6327_, v___x_6417_);
if (v___x_6418_ == 0)
{
lean_object* v___x_6419_; lean_object* v___x_6420_; double v___x_6421_; double v___x_6422_; double v___x_6423_; 
v___x_6419_ = l_Lean_trace_profiler_threshold;
v___x_6420_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6327_, v___x_6419_);
v___x_6421_ = lean_float_of_nat(v___x_6420_);
v___x_6422_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6423_ = lean_float_div(v___x_6421_, v___x_6422_);
v___y_6412_ = v___x_6423_;
goto v___jp_6411_;
}
else
{
lean_object* v___x_6424_; lean_object* v___x_6425_; double v___x_6426_; 
v___x_6424_ = l_Lean_trace_profiler_threshold;
v___x_6425_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6327_, v___x_6424_);
v___x_6426_ = lean_float_of_nat(v___x_6425_);
v___y_6412_ = v___x_6426_;
goto v___jp_6411_;
}
}
v___jp_6346_:
{
lean_object* v___x_6350_; 
lean_inc(v___y_6347_);
v___x_6350_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6329_, v_data_6349_, v___y_6347_, v___y_6348_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_);
if (lean_obj_tag(v___x_6350_) == 0)
{
lean_object* v___x_6351_; 
lean_dec_ref_known(v___x_6350_, 1);
v___x_6351_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6344_);
return v___x_6351_;
}
else
{
lean_object* v_a_6352_; lean_object* v___x_6354_; uint8_t v_isShared_6355_; uint8_t v_isSharedCheck_6359_; 
lean_dec(v_fst_6344_);
v_a_6352_ = lean_ctor_get(v___x_6350_, 0);
v_isSharedCheck_6359_ = !lean_is_exclusive(v___x_6350_);
if (v_isSharedCheck_6359_ == 0)
{
v___x_6354_ = v___x_6350_;
v_isShared_6355_ = v_isSharedCheck_6359_;
goto v_resetjp_6353_;
}
else
{
lean_inc(v_a_6352_);
lean_dec(v___x_6350_);
v___x_6354_ = lean_box(0);
v_isShared_6355_ = v_isSharedCheck_6359_;
goto v_resetjp_6353_;
}
v_resetjp_6353_:
{
lean_object* v___x_6357_; 
if (v_isShared_6355_ == 0)
{
v___x_6357_ = v___x_6354_;
goto v_reusejp_6356_;
}
else
{
lean_object* v_reuseFailAlloc_6358_; 
v_reuseFailAlloc_6358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6358_, 0, v_a_6352_);
v___x_6357_ = v_reuseFailAlloc_6358_;
goto v_reusejp_6356_;
}
v_reusejp_6356_:
{
return v___x_6357_;
}
}
}
}
v___jp_6364_:
{
uint8_t v_result_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; double v___x_6370_; lean_object* v_data_6371_; 
v_result_6367_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6344_);
v___x_6368_ = lean_box(v_result_6367_);
v___x_6369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6369_, 0, v___x_6368_);
v___x_6370_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6326_);
lean_inc_ref(v___x_6369_);
lean_inc(v_cls_6324_);
v_data_6371_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6371_, 0, v_cls_6324_);
lean_ctor_set(v_data_6371_, 1, v___x_6369_);
lean_ctor_set(v_data_6371_, 2, v_tag_6326_);
lean_ctor_set_float(v_data_6371_, sizeof(void*)*3, v___x_6370_);
lean_ctor_set_float(v_data_6371_, sizeof(void*)*3 + 8, v___x_6370_);
lean_ctor_set_uint8(v_data_6371_, sizeof(void*)*3 + 16, v_collapsed_6325_);
if (v___x_6363_ == 0)
{
lean_dec_ref_known(v___x_6369_, 1);
lean_dec(v_snd_6361_);
lean_dec(v_fst_6360_);
lean_dec_ref(v_tag_6326_);
lean_dec(v_cls_6324_);
v___y_6347_ = v___y_6365_;
v___y_6348_ = v_a_6366_;
v_data_6349_ = v_data_6371_;
goto v___jp_6346_;
}
else
{
lean_object* v_data_6372_; double v___x_6373_; double v___x_6374_; 
lean_dec_ref_known(v_data_6371_, 3);
v_data_6372_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6372_, 0, v_cls_6324_);
lean_ctor_set(v_data_6372_, 1, v___x_6369_);
lean_ctor_set(v_data_6372_, 2, v_tag_6326_);
v___x_6373_ = lean_unbox_float(v_fst_6360_);
lean_dec(v_fst_6360_);
lean_ctor_set_float(v_data_6372_, sizeof(void*)*3, v___x_6373_);
v___x_6374_ = lean_unbox_float(v_snd_6361_);
lean_dec(v_snd_6361_);
lean_ctor_set_float(v_data_6372_, sizeof(void*)*3 + 8, v___x_6374_);
lean_ctor_set_uint8(v_data_6372_, sizeof(void*)*3 + 16, v_collapsed_6325_);
v___y_6347_ = v___y_6365_;
v___y_6348_ = v_a_6366_;
v_data_6349_ = v_data_6372_;
goto v___jp_6346_;
}
}
v___jp_6375_:
{
lean_object* v_ref_6376_; lean_object* v___x_6377_; 
v_ref_6376_ = lean_ctor_get(v___y_6341_, 4);
lean_inc(v___y_6342_);
lean_inc_ref(v___y_6341_);
lean_inc(v___y_6340_);
lean_inc_ref(v___y_6339_);
lean_inc(v___y_6338_);
lean_inc_ref(v___y_6337_);
lean_inc(v___y_6336_);
lean_inc_ref(v___y_6335_);
lean_inc(v___y_6334_);
lean_inc(v___y_6333_);
lean_inc_ref(v___y_6332_);
lean_inc(v_fst_6344_);
v___x_6377_ = lean_apply_13(v_msg_6330_, v_fst_6344_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_, lean_box(0));
if (lean_obj_tag(v___x_6377_) == 0)
{
lean_object* v_a_6378_; 
v_a_6378_ = lean_ctor_get(v___x_6377_, 0);
lean_inc(v_a_6378_);
lean_dec_ref_known(v___x_6377_, 1);
v___y_6365_ = v_ref_6376_;
v_a_6366_ = v_a_6378_;
goto v___jp_6364_;
}
else
{
lean_object* v___x_6379_; 
lean_dec_ref_known(v___x_6377_, 1);
v___x_6379_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6365_ = v_ref_6376_;
v_a_6366_ = v___x_6379_;
goto v___jp_6364_;
}
}
v___jp_6380_:
{
if (v_clsEnabled_6328_ == 0)
{
if (v___y_6381_ == 0)
{
lean_object* v___x_6382_; lean_object* v_traceState_6383_; lean_object* v_env_6384_; lean_object* v_nextMacroScope_6385_; lean_object* v_ngen_6386_; lean_object* v_auxDeclNGen_6387_; lean_object* v_cache_6388_; lean_object* v_messages_6389_; lean_object* v_infoState_6390_; lean_object* v_snapshotTasks_6391_; lean_object* v___x_6393_; uint8_t v_isShared_6394_; uint8_t v_isSharedCheck_6410_; 
lean_dec(v_snd_6361_);
lean_dec(v_fst_6360_);
lean_dec_ref(v_msg_6330_);
lean_dec_ref(v_tag_6326_);
lean_dec(v_cls_6324_);
v___x_6382_ = lean_st_ref_take(v___y_6342_);
v_traceState_6383_ = lean_ctor_get(v___x_6382_, 4);
v_env_6384_ = lean_ctor_get(v___x_6382_, 0);
v_nextMacroScope_6385_ = lean_ctor_get(v___x_6382_, 1);
v_ngen_6386_ = lean_ctor_get(v___x_6382_, 2);
v_auxDeclNGen_6387_ = lean_ctor_get(v___x_6382_, 3);
v_cache_6388_ = lean_ctor_get(v___x_6382_, 5);
v_messages_6389_ = lean_ctor_get(v___x_6382_, 6);
v_infoState_6390_ = lean_ctor_get(v___x_6382_, 7);
v_snapshotTasks_6391_ = lean_ctor_get(v___x_6382_, 8);
v_isSharedCheck_6410_ = !lean_is_exclusive(v___x_6382_);
if (v_isSharedCheck_6410_ == 0)
{
v___x_6393_ = v___x_6382_;
v_isShared_6394_ = v_isSharedCheck_6410_;
goto v_resetjp_6392_;
}
else
{
lean_inc(v_snapshotTasks_6391_);
lean_inc(v_infoState_6390_);
lean_inc(v_messages_6389_);
lean_inc(v_cache_6388_);
lean_inc(v_traceState_6383_);
lean_inc(v_auxDeclNGen_6387_);
lean_inc(v_ngen_6386_);
lean_inc(v_nextMacroScope_6385_);
lean_inc(v_env_6384_);
lean_dec(v___x_6382_);
v___x_6393_ = lean_box(0);
v_isShared_6394_ = v_isSharedCheck_6410_;
goto v_resetjp_6392_;
}
v_resetjp_6392_:
{
uint64_t v_tid_6395_; lean_object* v_traces_6396_; lean_object* v___x_6398_; uint8_t v_isShared_6399_; uint8_t v_isSharedCheck_6409_; 
v_tid_6395_ = lean_ctor_get_uint64(v_traceState_6383_, sizeof(void*)*1);
v_traces_6396_ = lean_ctor_get(v_traceState_6383_, 0);
v_isSharedCheck_6409_ = !lean_is_exclusive(v_traceState_6383_);
if (v_isSharedCheck_6409_ == 0)
{
v___x_6398_ = v_traceState_6383_;
v_isShared_6399_ = v_isSharedCheck_6409_;
goto v_resetjp_6397_;
}
else
{
lean_inc(v_traces_6396_);
lean_dec(v_traceState_6383_);
v___x_6398_ = lean_box(0);
v_isShared_6399_ = v_isSharedCheck_6409_;
goto v_resetjp_6397_;
}
v_resetjp_6397_:
{
lean_object* v___x_6400_; lean_object* v___x_6402_; 
v___x_6400_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6329_, v_traces_6396_);
lean_dec_ref(v_traces_6396_);
if (v_isShared_6399_ == 0)
{
lean_ctor_set(v___x_6398_, 0, v___x_6400_);
v___x_6402_ = v___x_6398_;
goto v_reusejp_6401_;
}
else
{
lean_object* v_reuseFailAlloc_6408_; 
v_reuseFailAlloc_6408_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6408_, 0, v___x_6400_);
lean_ctor_set_uint64(v_reuseFailAlloc_6408_, sizeof(void*)*1, v_tid_6395_);
v___x_6402_ = v_reuseFailAlloc_6408_;
goto v_reusejp_6401_;
}
v_reusejp_6401_:
{
lean_object* v___x_6404_; 
if (v_isShared_6394_ == 0)
{
lean_ctor_set(v___x_6393_, 4, v___x_6402_);
v___x_6404_ = v___x_6393_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6407_; 
v_reuseFailAlloc_6407_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6407_, 0, v_env_6384_);
lean_ctor_set(v_reuseFailAlloc_6407_, 1, v_nextMacroScope_6385_);
lean_ctor_set(v_reuseFailAlloc_6407_, 2, v_ngen_6386_);
lean_ctor_set(v_reuseFailAlloc_6407_, 3, v_auxDeclNGen_6387_);
lean_ctor_set(v_reuseFailAlloc_6407_, 4, v___x_6402_);
lean_ctor_set(v_reuseFailAlloc_6407_, 5, v_cache_6388_);
lean_ctor_set(v_reuseFailAlloc_6407_, 6, v_messages_6389_);
lean_ctor_set(v_reuseFailAlloc_6407_, 7, v_infoState_6390_);
lean_ctor_set(v_reuseFailAlloc_6407_, 8, v_snapshotTasks_6391_);
v___x_6404_ = v_reuseFailAlloc_6407_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
lean_object* v___x_6405_; lean_object* v___x_6406_; 
v___x_6405_ = lean_st_ref_put(v___y_6342_, v___x_6404_);
v___x_6406_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6344_);
return v___x_6406_;
}
}
}
}
}
else
{
goto v___jp_6375_;
}
}
else
{
goto v___jp_6375_;
}
}
v___jp_6411_:
{
double v___x_6413_; double v___x_6414_; double v___x_6415_; uint8_t v___x_6416_; 
v___x_6413_ = lean_unbox_float(v_snd_6361_);
v___x_6414_ = lean_unbox_float(v_fst_6360_);
v___x_6415_ = lean_float_sub(v___x_6413_, v___x_6414_);
v___x_6416_ = lean_float_decLt(v___y_6412_, v___x_6415_);
v___y_6381_ = v___x_6416_;
goto v___jp_6380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6427_ = _args[0];
lean_object* v_collapsed_6428_ = _args[1];
lean_object* v_tag_6429_ = _args[2];
lean_object* v_opts_6430_ = _args[3];
lean_object* v_clsEnabled_6431_ = _args[4];
lean_object* v_oldTraces_6432_ = _args[5];
lean_object* v_msg_6433_ = _args[6];
lean_object* v_resStartStop_6434_ = _args[7];
lean_object* v___y_6435_ = _args[8];
lean_object* v___y_6436_ = _args[9];
lean_object* v___y_6437_ = _args[10];
lean_object* v___y_6438_ = _args[11];
lean_object* v___y_6439_ = _args[12];
lean_object* v___y_6440_ = _args[13];
lean_object* v___y_6441_ = _args[14];
lean_object* v___y_6442_ = _args[15];
lean_object* v___y_6443_ = _args[16];
lean_object* v___y_6444_ = _args[17];
lean_object* v___y_6445_ = _args[18];
lean_object* v___y_6446_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6447_; uint8_t v_clsEnabled_boxed_6448_; lean_object* v_res_6449_; 
v_collapsed_boxed_6447_ = lean_unbox(v_collapsed_6428_);
v_clsEnabled_boxed_6448_ = lean_unbox(v_clsEnabled_6431_);
v_res_6449_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6427_, v_collapsed_boxed_6447_, v_tag_6429_, v_opts_6430_, v_clsEnabled_boxed_6448_, v_oldTraces_6432_, v_msg_6433_, v_resStartStop_6434_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
lean_dec(v___y_6445_);
lean_dec_ref(v___y_6444_);
lean_dec(v___y_6443_);
lean_dec_ref(v___y_6442_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec(v___y_6439_);
lean_dec_ref(v___y_6438_);
lean_dec(v___y_6437_);
lean_dec(v___y_6436_);
lean_dec_ref(v___y_6435_);
lean_dec_ref(v_opts_6430_);
return v_res_6449_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6454_; lean_object* v___x_6455_; 
v___x_6454_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6455_ = l_Lean_stringToMessageData(v___x_6454_);
return v___x_6455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6456_, lean_object* v_b_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_){
_start:
{
if (lean_obj_tag(v_as_x27_6456_) == 0)
{
lean_object* v___x_6470_; 
v___x_6470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6470_, 0, v_b_6457_);
return v___x_6470_;
}
else
{
lean_object* v_head_6471_; lean_object* v_options_6472_; lean_object* v_tail_6473_; lean_object* v_name_6474_; lean_object* v_run_x27_6475_; lean_object* v_toCold_6476_; uint8_t v_hasTrace_6477_; lean_object* v___x_6478_; uint8_t v___y_6480_; lean_object* v___x_6485_; lean_object* v___y_6487_; 
lean_dec_ref(v_b_6457_);
v_head_6471_ = lean_ctor_get(v_as_x27_6456_, 0);
v_options_6472_ = lean_ctor_get(v___y_6467_, 1);
v_tail_6473_ = lean_ctor_get(v_as_x27_6456_, 1);
v_name_6474_ = lean_ctor_get(v_head_6471_, 0);
v_run_x27_6475_ = lean_ctor_get(v_head_6471_, 1);
v_toCold_6476_ = lean_ctor_get(v___y_6467_, 0);
v_hasTrace_6477_ = lean_ctor_get_uint8(v_options_6472_, sizeof(void*)*1);
v___x_6478_ = lean_box(0);
v___x_6485_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6477_ == 0)
{
lean_object* v___x_6516_; 
lean_inc_ref(v_run_x27_6475_);
lean_inc(v___y_6468_);
lean_inc_ref(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc_ref(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
v___x_6516_ = lean_apply_12(v_run_x27_6475_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, lean_box(0));
v___y_6487_ = v___x_6516_;
goto v___jp_6486_;
}
else
{
lean_object* v_inheritedTraceOptions_6517_; lean_object* v___f_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; uint8_t v___x_6522_; lean_object* v___y_6524_; lean_object* v___y_6525_; lean_object* v_a_6526_; lean_object* v___y_6539_; lean_object* v___y_6540_; lean_object* v_a_6541_; 
v_inheritedTraceOptions_6517_ = lean_ctor_get(v_toCold_6476_, 4);
lean_inc(v_name_6474_);
v___f_6518_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6518_, 0, v_name_6474_);
v___x_6519_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6520_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6521_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6522_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6517_, v_options_6472_, v___x_6521_);
if (v___x_6522_ == 0)
{
lean_object* v___x_6591_; uint8_t v___x_6592_; 
v___x_6591_ = l_Lean_trace_profiler;
v___x_6592_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6472_, v___x_6591_);
if (v___x_6592_ == 0)
{
lean_object* v___x_6593_; 
lean_dec_ref(v___f_6518_);
lean_inc_ref(v_run_x27_6475_);
lean_inc(v___y_6468_);
lean_inc_ref(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc_ref(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
v___x_6593_ = lean_apply_12(v_run_x27_6475_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, lean_box(0));
v___y_6487_ = v___x_6593_;
goto v___jp_6486_;
}
else
{
goto v___jp_6550_;
}
}
else
{
goto v___jp_6550_;
}
v___jp_6523_:
{
lean_object* v___x_6527_; double v___x_6528_; double v___x_6529_; double v___x_6530_; double v___x_6531_; double v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; 
v___x_6527_ = lean_io_mono_nanos_now();
v___x_6528_ = lean_float_of_nat(v___y_6524_);
v___x_6529_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6530_ = lean_float_div(v___x_6528_, v___x_6529_);
v___x_6531_ = lean_float_of_nat(v___x_6527_);
v___x_6532_ = lean_float_div(v___x_6531_, v___x_6529_);
v___x_6533_ = lean_box_float(v___x_6530_);
v___x_6534_ = lean_box_float(v___x_6532_);
v___x_6535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6535_, 0, v___x_6533_);
lean_ctor_set(v___x_6535_, 1, v___x_6534_);
v___x_6536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6536_, 0, v_a_6526_);
lean_ctor_set(v___x_6536_, 1, v___x_6535_);
v___x_6537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6519_, v_hasTrace_6477_, v___x_6520_, v_options_6472_, v___x_6522_, v___y_6525_, v___f_6518_, v___x_6536_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_);
v___y_6487_ = v___x_6537_;
goto v___jp_6486_;
}
v___jp_6538_:
{
lean_object* v___x_6542_; double v___x_6543_; double v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; 
v___x_6542_ = lean_io_get_num_heartbeats();
v___x_6543_ = lean_float_of_nat(v___y_6540_);
v___x_6544_ = lean_float_of_nat(v___x_6542_);
v___x_6545_ = lean_box_float(v___x_6543_);
v___x_6546_ = lean_box_float(v___x_6544_);
v___x_6547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6547_, 0, v___x_6545_);
lean_ctor_set(v___x_6547_, 1, v___x_6546_);
v___x_6548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6548_, 0, v_a_6541_);
lean_ctor_set(v___x_6548_, 1, v___x_6547_);
v___x_6549_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6519_, v_hasTrace_6477_, v___x_6520_, v_options_6472_, v___x_6522_, v___y_6539_, v___f_6518_, v___x_6548_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_);
v___y_6487_ = v___x_6549_;
goto v___jp_6486_;
}
v___jp_6550_:
{
lean_object* v___x_6551_; lean_object* v_a_6552_; lean_object* v___x_6553_; uint8_t v___x_6554_; 
v___x_6551_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6468_);
v_a_6552_ = lean_ctor_get(v___x_6551_, 0);
lean_inc(v_a_6552_);
lean_dec_ref(v___x_6551_);
v___x_6553_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6554_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6472_, v___x_6553_);
if (v___x_6554_ == 0)
{
lean_object* v___x_6555_; lean_object* v___x_6556_; 
v___x_6555_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_6475_);
lean_inc(v___y_6468_);
lean_inc_ref(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc_ref(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
v___x_6556_ = lean_apply_12(v_run_x27_6475_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, lean_box(0));
if (lean_obj_tag(v___x_6556_) == 0)
{
lean_object* v_a_6557_; lean_object* v___x_6559_; uint8_t v_isShared_6560_; uint8_t v_isSharedCheck_6564_; 
v_a_6557_ = lean_ctor_get(v___x_6556_, 0);
v_isSharedCheck_6564_ = !lean_is_exclusive(v___x_6556_);
if (v_isSharedCheck_6564_ == 0)
{
v___x_6559_ = v___x_6556_;
v_isShared_6560_ = v_isSharedCheck_6564_;
goto v_resetjp_6558_;
}
else
{
lean_inc(v_a_6557_);
lean_dec(v___x_6556_);
v___x_6559_ = lean_box(0);
v_isShared_6560_ = v_isSharedCheck_6564_;
goto v_resetjp_6558_;
}
v_resetjp_6558_:
{
lean_object* v___x_6562_; 
if (v_isShared_6560_ == 0)
{
lean_ctor_set_tag(v___x_6559_, 1);
v___x_6562_ = v___x_6559_;
goto v_reusejp_6561_;
}
else
{
lean_object* v_reuseFailAlloc_6563_; 
v_reuseFailAlloc_6563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6563_, 0, v_a_6557_);
v___x_6562_ = v_reuseFailAlloc_6563_;
goto v_reusejp_6561_;
}
v_reusejp_6561_:
{
v___y_6524_ = v___x_6555_;
v___y_6525_ = v_a_6552_;
v_a_6526_ = v___x_6562_;
goto v___jp_6523_;
}
}
}
else
{
lean_object* v_a_6565_; lean_object* v___x_6567_; uint8_t v_isShared_6568_; uint8_t v_isSharedCheck_6572_; 
v_a_6565_ = lean_ctor_get(v___x_6556_, 0);
v_isSharedCheck_6572_ = !lean_is_exclusive(v___x_6556_);
if (v_isSharedCheck_6572_ == 0)
{
v___x_6567_ = v___x_6556_;
v_isShared_6568_ = v_isSharedCheck_6572_;
goto v_resetjp_6566_;
}
else
{
lean_inc(v_a_6565_);
lean_dec(v___x_6556_);
v___x_6567_ = lean_box(0);
v_isShared_6568_ = v_isSharedCheck_6572_;
goto v_resetjp_6566_;
}
v_resetjp_6566_:
{
lean_object* v___x_6570_; 
if (v_isShared_6568_ == 0)
{
lean_ctor_set_tag(v___x_6567_, 0);
v___x_6570_ = v___x_6567_;
goto v_reusejp_6569_;
}
else
{
lean_object* v_reuseFailAlloc_6571_; 
v_reuseFailAlloc_6571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_a_6565_);
v___x_6570_ = v_reuseFailAlloc_6571_;
goto v_reusejp_6569_;
}
v_reusejp_6569_:
{
v___y_6524_ = v___x_6555_;
v___y_6525_ = v_a_6552_;
v_a_6526_ = v___x_6570_;
goto v___jp_6523_;
}
}
}
}
else
{
lean_object* v___x_6573_; lean_object* v___x_6574_; 
v___x_6573_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_6475_);
lean_inc(v___y_6468_);
lean_inc_ref(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc_ref(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
v___x_6574_ = lean_apply_12(v_run_x27_6475_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, lean_box(0));
if (lean_obj_tag(v___x_6574_) == 0)
{
lean_object* v_a_6575_; lean_object* v___x_6577_; uint8_t v_isShared_6578_; uint8_t v_isSharedCheck_6582_; 
v_a_6575_ = lean_ctor_get(v___x_6574_, 0);
v_isSharedCheck_6582_ = !lean_is_exclusive(v___x_6574_);
if (v_isSharedCheck_6582_ == 0)
{
v___x_6577_ = v___x_6574_;
v_isShared_6578_ = v_isSharedCheck_6582_;
goto v_resetjp_6576_;
}
else
{
lean_inc(v_a_6575_);
lean_dec(v___x_6574_);
v___x_6577_ = lean_box(0);
v_isShared_6578_ = v_isSharedCheck_6582_;
goto v_resetjp_6576_;
}
v_resetjp_6576_:
{
lean_object* v___x_6580_; 
if (v_isShared_6578_ == 0)
{
lean_ctor_set_tag(v___x_6577_, 1);
v___x_6580_ = v___x_6577_;
goto v_reusejp_6579_;
}
else
{
lean_object* v_reuseFailAlloc_6581_; 
v_reuseFailAlloc_6581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6581_, 0, v_a_6575_);
v___x_6580_ = v_reuseFailAlloc_6581_;
goto v_reusejp_6579_;
}
v_reusejp_6579_:
{
v___y_6539_ = v_a_6552_;
v___y_6540_ = v___x_6573_;
v_a_6541_ = v___x_6580_;
goto v___jp_6538_;
}
}
}
else
{
lean_object* v_a_6583_; lean_object* v___x_6585_; uint8_t v_isShared_6586_; uint8_t v_isSharedCheck_6590_; 
v_a_6583_ = lean_ctor_get(v___x_6574_, 0);
v_isSharedCheck_6590_ = !lean_is_exclusive(v___x_6574_);
if (v_isSharedCheck_6590_ == 0)
{
v___x_6585_ = v___x_6574_;
v_isShared_6586_ = v_isSharedCheck_6590_;
goto v_resetjp_6584_;
}
else
{
lean_inc(v_a_6583_);
lean_dec(v___x_6574_);
v___x_6585_ = lean_box(0);
v_isShared_6586_ = v_isSharedCheck_6590_;
goto v_resetjp_6584_;
}
v_resetjp_6584_:
{
lean_object* v___x_6588_; 
if (v_isShared_6586_ == 0)
{
lean_ctor_set_tag(v___x_6585_, 0);
v___x_6588_ = v___x_6585_;
goto v_reusejp_6587_;
}
else
{
lean_object* v_reuseFailAlloc_6589_; 
v_reuseFailAlloc_6589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6589_, 0, v_a_6583_);
v___x_6588_ = v_reuseFailAlloc_6589_;
goto v_reusejp_6587_;
}
v_reusejp_6587_:
{
v___y_6539_ = v_a_6552_;
v___y_6540_ = v___x_6573_;
v_a_6541_ = v___x_6588_;
goto v___jp_6538_;
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
v_as_x27_6456_ = v_tail_6473_;
v_b_6457_ = v___x_6485_;
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
lean_object* v_inheritedTraceOptions_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; uint8_t v___x_6495_; 
v_inheritedTraceOptions_6492_ = lean_ctor_get(v_toCold_6476_, 4);
v___x_6493_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6494_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6492_, v_options_6472_, v___x_6494_);
if (v___x_6495_ == 0)
{
uint8_t v___x_6496_; 
v___x_6496_ = lean_unbox(v_a_6488_);
lean_dec(v_a_6488_);
v___y_6480_ = v___x_6496_;
goto v___jp_6479_;
}
else
{
lean_object* v___x_6497_; lean_object* v___x_6498_; 
v___x_6497_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_6498_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6493_, v___x_6497_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_);
if (lean_obj_tag(v___x_6498_) == 0)
{
uint8_t v___x_6499_; 
lean_dec_ref_known(v___x_6498_, 1);
v___x_6499_ = lean_unbox(v_a_6488_);
lean_dec(v_a_6488_);
v___y_6480_ = v___x_6499_;
goto v___jp_6479_;
}
else
{
lean_object* v_a_6500_; lean_object* v___x_6502_; uint8_t v_isShared_6503_; uint8_t v_isSharedCheck_6507_; 
lean_dec(v_a_6488_);
v_a_6500_ = lean_ctor_get(v___x_6498_, 0);
v_isSharedCheck_6507_ = !lean_is_exclusive(v___x_6498_);
if (v_isSharedCheck_6507_ == 0)
{
v___x_6502_ = v___x_6498_;
v_isShared_6503_ = v_isSharedCheck_6507_;
goto v_resetjp_6501_;
}
else
{
lean_inc(v_a_6500_);
lean_dec(v___x_6498_);
v___x_6502_ = lean_box(0);
v_isShared_6503_ = v_isSharedCheck_6507_;
goto v_resetjp_6501_;
}
v_resetjp_6501_:
{
lean_object* v___x_6505_; 
if (v_isShared_6503_ == 0)
{
v___x_6505_ = v___x_6502_;
goto v_reusejp_6504_;
}
else
{
lean_object* v_reuseFailAlloc_6506_; 
v_reuseFailAlloc_6506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6506_, 0, v_a_6500_);
v___x_6505_ = v_reuseFailAlloc_6506_;
goto v_reusejp_6504_;
}
v_reusejp_6504_:
{
return v___x_6505_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6508_; lean_object* v___x_6510_; uint8_t v_isShared_6511_; uint8_t v_isSharedCheck_6515_; 
v_a_6508_ = lean_ctor_get(v___y_6487_, 0);
v_isSharedCheck_6515_ = !lean_is_exclusive(v___y_6487_);
if (v_isSharedCheck_6515_ == 0)
{
v___x_6510_ = v___y_6487_;
v_isShared_6511_ = v_isSharedCheck_6515_;
goto v_resetjp_6509_;
}
else
{
lean_inc(v_a_6508_);
lean_dec(v___y_6487_);
v___x_6510_ = lean_box(0);
v_isShared_6511_ = v_isSharedCheck_6515_;
goto v_resetjp_6509_;
}
v_resetjp_6509_:
{
lean_object* v___x_6513_; 
if (v_isShared_6511_ == 0)
{
v___x_6513_ = v___x_6510_;
goto v_reusejp_6512_;
}
else
{
lean_object* v_reuseFailAlloc_6514_; 
v_reuseFailAlloc_6514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6514_, 0, v_a_6508_);
v___x_6513_ = v_reuseFailAlloc_6514_;
goto v_reusejp_6512_;
}
v_reusejp_6512_:
{
return v___x_6513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_6594_, lean_object* v_b_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_, lean_object* v___y_6604_, lean_object* v___y_6605_, lean_object* v___y_6606_, lean_object* v___y_6607_){
_start:
{
lean_object* v_res_6608_; 
v_res_6608_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6594_, v_b_6595_, v___y_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_);
lean_dec(v___y_6606_);
lean_dec_ref(v___y_6605_);
lean_dec(v___y_6604_);
lean_dec_ref(v___y_6603_);
lean_dec(v___y_6602_);
lean_dec_ref(v___y_6601_);
lean_dec(v___y_6600_);
lean_dec_ref(v___y_6599_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec_ref(v___y_6596_);
lean_dec(v_as_x27_6594_);
return v_res_6608_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_6611_; lean_object* v___x_6612_; 
v___x_6611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_6612_ = l_Lean_stringToMessageData(v___x_6611_);
return v___x_6612_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_6614_; lean_object* v___x_6615_; 
v___x_6614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_6615_ = l_Lean_stringToMessageData(v___x_6614_);
return v___x_6615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_, lean_object* v_a_6626_, lean_object* v_a_6627_){
_start:
{
lean_object* v___x_6629_; lean_object* v___x_6630_; 
v___x_6629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_6630_ = l_Lean_Core_checkSystem(v___x_6629_, v_a_6626_, v_a_6627_);
if (lean_obj_tag(v___x_6630_) == 0)
{
lean_object* v___x_6631_; lean_object* v_caches_6632_; lean_object* v_typeAnalysis_6633_; lean_object* v_target_6634_; lean_object* v_hypotheses_6635_; lean_object* v___x_6637_; uint8_t v_isShared_6638_; uint8_t v_isSharedCheck_6720_; 
lean_dec_ref_known(v___x_6630_, 1);
v___x_6631_ = lean_st_ref_take(v_a_6618_);
v_caches_6632_ = lean_ctor_get(v___x_6631_, 0);
v_typeAnalysis_6633_ = lean_ctor_get(v___x_6631_, 1);
v_target_6634_ = lean_ctor_get(v___x_6631_, 2);
v_hypotheses_6635_ = lean_ctor_get(v___x_6631_, 3);
v_isSharedCheck_6720_ = !lean_is_exclusive(v___x_6631_);
if (v_isSharedCheck_6720_ == 0)
{
v___x_6637_ = v___x_6631_;
v_isShared_6638_ = v_isSharedCheck_6720_;
goto v_resetjp_6636_;
}
else
{
lean_inc(v_hypotheses_6635_);
lean_inc(v_target_6634_);
lean_inc(v_typeAnalysis_6633_);
lean_inc(v_caches_6632_);
lean_dec(v___x_6631_);
v___x_6637_ = lean_box(0);
v_isShared_6638_ = v_isSharedCheck_6720_;
goto v_resetjp_6636_;
}
v_resetjp_6636_:
{
uint8_t v___x_6639_; lean_object* v___x_6641_; 
v___x_6639_ = 0;
if (v_isShared_6638_ == 0)
{
v___x_6641_ = v___x_6637_;
goto v_reusejp_6640_;
}
else
{
lean_object* v_reuseFailAlloc_6719_; 
v_reuseFailAlloc_6719_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6719_, 0, v_caches_6632_);
lean_ctor_set(v_reuseFailAlloc_6719_, 1, v_typeAnalysis_6633_);
lean_ctor_set(v_reuseFailAlloc_6719_, 2, v_target_6634_);
lean_ctor_set(v_reuseFailAlloc_6719_, 3, v_hypotheses_6635_);
v___x_6641_ = v_reuseFailAlloc_6719_;
goto v_reusejp_6640_;
}
v_reusejp_6640_:
{
lean_object* v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; 
lean_ctor_set_uint8(v___x_6641_, sizeof(void*)*4, v___x_6639_);
v___x_6642_ = lean_st_ref_put(v_a_6618_, v___x_6641_);
v___x_6643_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_6644_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_6616_, v___x_6643_, v_a_6617_, v_a_6618_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_, v_a_6623_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_);
if (lean_obj_tag(v___x_6644_) == 0)
{
lean_object* v_a_6645_; lean_object* v___x_6647_; uint8_t v_isShared_6648_; uint8_t v_isSharedCheck_6710_; 
v_a_6645_ = lean_ctor_get(v___x_6644_, 0);
v_isSharedCheck_6710_ = !lean_is_exclusive(v___x_6644_);
if (v_isSharedCheck_6710_ == 0)
{
v___x_6647_ = v___x_6644_;
v_isShared_6648_ = v_isSharedCheck_6710_;
goto v_resetjp_6646_;
}
else
{
lean_inc(v_a_6645_);
lean_dec(v___x_6644_);
v___x_6647_ = lean_box(0);
v_isShared_6648_ = v_isSharedCheck_6710_;
goto v_resetjp_6646_;
}
v_resetjp_6646_:
{
lean_object* v_fst_6649_; 
v_fst_6649_ = lean_ctor_get(v_a_6645_, 0);
lean_inc(v_fst_6649_);
lean_dec(v_a_6645_);
if (lean_obj_tag(v_fst_6649_) == 0)
{
lean_object* v___x_6650_; uint8_t v_didChange_6651_; 
v___x_6650_ = lean_st_ref_get(v_a_6618_);
v_didChange_6651_ = lean_ctor_get_uint8(v___x_6650_, sizeof(void*)*4);
lean_dec(v___x_6650_);
if (v_didChange_6651_ == 0)
{
lean_object* v_options_6652_; uint8_t v_hasTrace_6653_; 
v_options_6652_ = lean_ctor_get(v_a_6626_, 1);
v_hasTrace_6653_ = lean_ctor_get_uint8(v_options_6652_, sizeof(void*)*1);
if (v_hasTrace_6653_ == 0)
{
lean_object* v___x_6654_; lean_object* v___x_6656_; 
v___x_6654_ = lean_box(v_didChange_6651_);
if (v_isShared_6648_ == 0)
{
lean_ctor_set(v___x_6647_, 0, v___x_6654_);
v___x_6656_ = v___x_6647_;
goto v_reusejp_6655_;
}
else
{
lean_object* v_reuseFailAlloc_6657_; 
v_reuseFailAlloc_6657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6657_, 0, v___x_6654_);
v___x_6656_ = v_reuseFailAlloc_6657_;
goto v_reusejp_6655_;
}
v_reusejp_6655_:
{
return v___x_6656_;
}
}
else
{
lean_object* v_toCold_6658_; lean_object* v_inheritedTraceOptions_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; uint8_t v___x_6662_; 
v_toCold_6658_ = lean_ctor_get(v_a_6626_, 0);
v_inheritedTraceOptions_6659_ = lean_ctor_get(v_toCold_6658_, 4);
v___x_6660_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6661_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6662_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6659_, v_options_6652_, v___x_6661_);
if (v___x_6662_ == 0)
{
lean_object* v___x_6663_; lean_object* v___x_6665_; 
v___x_6663_ = lean_box(v_didChange_6651_);
if (v_isShared_6648_ == 0)
{
lean_ctor_set(v___x_6647_, 0, v___x_6663_);
v___x_6665_ = v___x_6647_;
goto v_reusejp_6664_;
}
else
{
lean_object* v_reuseFailAlloc_6666_; 
v_reuseFailAlloc_6666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6666_, 0, v___x_6663_);
v___x_6665_ = v_reuseFailAlloc_6666_;
goto v_reusejp_6664_;
}
v_reusejp_6664_:
{
return v___x_6665_;
}
}
else
{
lean_object* v___x_6667_; lean_object* v___x_6668_; 
lean_del_object(v___x_6647_);
v___x_6667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6668_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6660_, v___x_6667_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_);
if (lean_obj_tag(v___x_6668_) == 0)
{
lean_object* v___x_6670_; uint8_t v_isShared_6671_; uint8_t v_isSharedCheck_6676_; 
v_isSharedCheck_6676_ = !lean_is_exclusive(v___x_6668_);
if (v_isSharedCheck_6676_ == 0)
{
lean_object* v_unused_6677_; 
v_unused_6677_ = lean_ctor_get(v___x_6668_, 0);
lean_dec(v_unused_6677_);
v___x_6670_ = v___x_6668_;
v_isShared_6671_ = v_isSharedCheck_6676_;
goto v_resetjp_6669_;
}
else
{
lean_dec(v___x_6668_);
v___x_6670_ = lean_box(0);
v_isShared_6671_ = v_isSharedCheck_6676_;
goto v_resetjp_6669_;
}
v_resetjp_6669_:
{
lean_object* v___x_6672_; lean_object* v___x_6674_; 
v___x_6672_ = lean_box(v_didChange_6651_);
if (v_isShared_6671_ == 0)
{
lean_ctor_set(v___x_6670_, 0, v___x_6672_);
v___x_6674_ = v___x_6670_;
goto v_reusejp_6673_;
}
else
{
lean_object* v_reuseFailAlloc_6675_; 
v_reuseFailAlloc_6675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6675_, 0, v___x_6672_);
v___x_6674_ = v_reuseFailAlloc_6675_;
goto v_reusejp_6673_;
}
v_reusejp_6673_:
{
return v___x_6674_;
}
}
}
else
{
lean_object* v_a_6678_; lean_object* v___x_6680_; uint8_t v_isShared_6681_; uint8_t v_isSharedCheck_6685_; 
v_a_6678_ = lean_ctor_get(v___x_6668_, 0);
v_isSharedCheck_6685_ = !lean_is_exclusive(v___x_6668_);
if (v_isSharedCheck_6685_ == 0)
{
v___x_6680_ = v___x_6668_;
v_isShared_6681_ = v_isSharedCheck_6685_;
goto v_resetjp_6679_;
}
else
{
lean_inc(v_a_6678_);
lean_dec(v___x_6668_);
v___x_6680_ = lean_box(0);
v_isShared_6681_ = v_isSharedCheck_6685_;
goto v_resetjp_6679_;
}
v_resetjp_6679_:
{
lean_object* v___x_6683_; 
if (v_isShared_6681_ == 0)
{
v___x_6683_ = v___x_6680_;
goto v_reusejp_6682_;
}
else
{
lean_object* v_reuseFailAlloc_6684_; 
v_reuseFailAlloc_6684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6684_, 0, v_a_6678_);
v___x_6683_ = v_reuseFailAlloc_6684_;
goto v_reusejp_6682_;
}
v_reusejp_6682_:
{
return v___x_6683_;
}
}
}
}
}
}
else
{
lean_object* v_options_6686_; uint8_t v_hasTrace_6687_; 
lean_del_object(v___x_6647_);
v_options_6686_ = lean_ctor_get(v_a_6626_, 1);
v_hasTrace_6687_ = lean_ctor_get_uint8(v_options_6686_, sizeof(void*)*1);
if (v_hasTrace_6687_ == 0)
{
goto _start;
}
else
{
lean_object* v_toCold_6689_; lean_object* v_inheritedTraceOptions_6690_; lean_object* v___x_6691_; lean_object* v___x_6692_; uint8_t v___x_6693_; 
v_toCold_6689_ = lean_ctor_get(v_a_6626_, 0);
v_inheritedTraceOptions_6690_ = lean_ctor_get(v_toCold_6689_, 4);
v___x_6691_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6692_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6690_, v_options_6686_, v___x_6692_);
if (v___x_6693_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6695_; lean_object* v___x_6696_; 
v___x_6695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6696_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6691_, v___x_6695_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_);
if (lean_obj_tag(v___x_6696_) == 0)
{
lean_dec_ref_known(v___x_6696_, 1);
goto _start;
}
else
{
lean_object* v_a_6698_; lean_object* v___x_6700_; uint8_t v_isShared_6701_; uint8_t v_isSharedCheck_6705_; 
v_a_6698_ = lean_ctor_get(v___x_6696_, 0);
v_isSharedCheck_6705_ = !lean_is_exclusive(v___x_6696_);
if (v_isSharedCheck_6705_ == 0)
{
v___x_6700_ = v___x_6696_;
v_isShared_6701_ = v_isSharedCheck_6705_;
goto v_resetjp_6699_;
}
else
{
lean_inc(v_a_6698_);
lean_dec(v___x_6696_);
v___x_6700_ = lean_box(0);
v_isShared_6701_ = v_isSharedCheck_6705_;
goto v_resetjp_6699_;
}
v_resetjp_6699_:
{
lean_object* v___x_6703_; 
if (v_isShared_6701_ == 0)
{
v___x_6703_ = v___x_6700_;
goto v_reusejp_6702_;
}
else
{
lean_object* v_reuseFailAlloc_6704_; 
v_reuseFailAlloc_6704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6704_, 0, v_a_6698_);
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
}
}
}
else
{
lean_object* v_val_6706_; lean_object* v___x_6708_; 
v_val_6706_ = lean_ctor_get(v_fst_6649_, 0);
lean_inc(v_val_6706_);
lean_dec_ref_known(v_fst_6649_, 1);
if (v_isShared_6648_ == 0)
{
lean_ctor_set(v___x_6647_, 0, v_val_6706_);
v___x_6708_ = v___x_6647_;
goto v_reusejp_6707_;
}
else
{
lean_object* v_reuseFailAlloc_6709_; 
v_reuseFailAlloc_6709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6709_, 0, v_val_6706_);
v___x_6708_ = v_reuseFailAlloc_6709_;
goto v_reusejp_6707_;
}
v_reusejp_6707_:
{
return v___x_6708_;
}
}
}
}
else
{
lean_object* v_a_6711_; lean_object* v___x_6713_; uint8_t v_isShared_6714_; uint8_t v_isSharedCheck_6718_; 
v_a_6711_ = lean_ctor_get(v___x_6644_, 0);
v_isSharedCheck_6718_ = !lean_is_exclusive(v___x_6644_);
if (v_isSharedCheck_6718_ == 0)
{
v___x_6713_ = v___x_6644_;
v_isShared_6714_ = v_isSharedCheck_6718_;
goto v_resetjp_6712_;
}
else
{
lean_inc(v_a_6711_);
lean_dec(v___x_6644_);
v___x_6713_ = lean_box(0);
v_isShared_6714_ = v_isSharedCheck_6718_;
goto v_resetjp_6712_;
}
v_resetjp_6712_:
{
lean_object* v___x_6716_; 
if (v_isShared_6714_ == 0)
{
v___x_6716_ = v___x_6713_;
goto v_reusejp_6715_;
}
else
{
lean_object* v_reuseFailAlloc_6717_; 
v_reuseFailAlloc_6717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6717_, 0, v_a_6711_);
v___x_6716_ = v_reuseFailAlloc_6717_;
goto v_reusejp_6715_;
}
v_reusejp_6715_:
{
return v___x_6716_;
}
}
}
}
}
}
else
{
lean_object* v_a_6721_; lean_object* v___x_6723_; uint8_t v_isShared_6724_; uint8_t v_isSharedCheck_6728_; 
v_a_6721_ = lean_ctor_get(v___x_6630_, 0);
v_isSharedCheck_6728_ = !lean_is_exclusive(v___x_6630_);
if (v_isSharedCheck_6728_ == 0)
{
v___x_6723_ = v___x_6630_;
v_isShared_6724_ = v_isSharedCheck_6728_;
goto v_resetjp_6722_;
}
else
{
lean_inc(v_a_6721_);
lean_dec(v___x_6630_);
v___x_6723_ = lean_box(0);
v_isShared_6724_ = v_isSharedCheck_6728_;
goto v_resetjp_6722_;
}
v_resetjp_6722_:
{
lean_object* v___x_6726_; 
if (v_isShared_6724_ == 0)
{
v___x_6726_ = v___x_6723_;
goto v_reusejp_6725_;
}
else
{
lean_object* v_reuseFailAlloc_6727_; 
v_reuseFailAlloc_6727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6727_, 0, v_a_6721_);
v___x_6726_ = v_reuseFailAlloc_6727_;
goto v_reusejp_6725_;
}
v_reusejp_6725_:
{
return v___x_6726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6729_, lean_object* v_a_6730_, lean_object* v_a_6731_, lean_object* v_a_6732_, lean_object* v_a_6733_, lean_object* v_a_6734_, lean_object* v_a_6735_, lean_object* v_a_6736_, lean_object* v_a_6737_, lean_object* v_a_6738_, lean_object* v_a_6739_, lean_object* v_a_6740_, lean_object* v_a_6741_){
_start:
{
lean_object* v_res_6742_; 
v_res_6742_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6729_, v_a_6730_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_, v_a_6735_, v_a_6736_, v_a_6737_, v_a_6738_, v_a_6739_, v_a_6740_);
lean_dec(v_a_6740_);
lean_dec_ref(v_a_6739_);
lean_dec(v_a_6738_);
lean_dec_ref(v_a_6737_);
lean_dec(v_a_6736_);
lean_dec_ref(v_a_6735_);
lean_dec(v_a_6734_);
lean_dec_ref(v_a_6733_);
lean_dec(v_a_6732_);
lean_dec(v_a_6731_);
lean_dec_ref(v_a_6730_);
lean_dec(v_passes_6729_);
return v_res_6742_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6743_, lean_object* v_msg_6744_, lean_object* v___y_6745_, lean_object* v___y_6746_, lean_object* v___y_6747_, lean_object* v___y_6748_, lean_object* v___y_6749_, lean_object* v___y_6750_, lean_object* v___y_6751_, lean_object* v___y_6752_, lean_object* v___y_6753_, lean_object* v___y_6754_, lean_object* v___y_6755_){
_start:
{
lean_object* v___x_6757_; 
v___x_6757_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6743_, v_msg_6744_, v___y_6752_, v___y_6753_, v___y_6754_, v___y_6755_);
return v___x_6757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6758_, lean_object* v_msg_6759_, lean_object* v___y_6760_, lean_object* v___y_6761_, lean_object* v___y_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_, lean_object* v___y_6765_, lean_object* v___y_6766_, lean_object* v___y_6767_, lean_object* v___y_6768_, lean_object* v___y_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_){
_start:
{
lean_object* v_res_6772_; 
v_res_6772_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6758_, v_msg_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_);
lean_dec(v___y_6770_);
lean_dec_ref(v___y_6769_);
lean_dec(v___y_6768_);
lean_dec_ref(v___y_6767_);
lean_dec(v___y_6766_);
lean_dec_ref(v___y_6765_);
lean_dec(v___y_6764_);
lean_dec_ref(v___y_6763_);
lean_dec(v___y_6762_);
lean_dec(v___y_6761_);
lean_dec_ref(v___y_6760_);
return v_res_6772_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6773_, lean_object* v_x_6774_, lean_object* v___y_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_){
_start:
{
lean_object* v___x_6787_; 
v___x_6787_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6774_);
return v___x_6787_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6788_, lean_object* v_x_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_){
_start:
{
lean_object* v_res_6802_; 
v_res_6802_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6788_, v_x_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6803_, lean_object* v_as_x27_6804_, lean_object* v_b_6805_, lean_object* v_a_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_, lean_object* v___y_6809_, lean_object* v___y_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_, lean_object* v___y_6816_, lean_object* v___y_6817_){
_start:
{
lean_object* v___x_6819_; 
v___x_6819_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6804_, v_b_6805_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_, v___y_6813_, v___y_6814_, v___y_6815_, v___y_6816_, v___y_6817_);
return v___x_6819_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6820_, lean_object* v_as_x27_6821_, lean_object* v_b_6822_, lean_object* v_a_6823_, lean_object* v___y_6824_, lean_object* v___y_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_, lean_object* v___y_6834_, lean_object* v___y_6835_){
_start:
{
lean_object* v_res_6836_; 
v_res_6836_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6820_, v_as_x27_6821_, v_b_6822_, v_a_6823_, v___y_6824_, v___y_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_, v___y_6833_, v___y_6834_);
lean_dec(v___y_6834_);
lean_dec_ref(v___y_6833_);
lean_dec(v___y_6832_);
lean_dec_ref(v___y_6831_);
lean_dec(v___y_6830_);
lean_dec_ref(v___y_6829_);
lean_dec(v___y_6828_);
lean_dec_ref(v___y_6827_);
lean_dec(v___y_6826_);
lean_dec(v___y_6825_);
lean_dec_ref(v___y_6824_);
lean_dec(v_as_x27_6821_);
lean_dec(v_as_6820_);
return v_res_6836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6837_, lean_object* v_data_6838_, lean_object* v_ref_6839_, lean_object* v_msg_6840_, lean_object* v___y_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_, lean_object* v___y_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_, lean_object* v___y_6850_, lean_object* v___y_6851_){
_start:
{
lean_object* v___x_6853_; 
v___x_6853_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6837_, v_data_6838_, v_ref_6839_, v_msg_6840_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_);
return v___x_6853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6854_, lean_object* v_data_6855_, lean_object* v_ref_6856_, lean_object* v_msg_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_, lean_object* v___y_6868_, lean_object* v___y_6869_){
_start:
{
lean_object* v_res_6870_; 
v_res_6870_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6854_, v_data_6855_, v_ref_6856_, v_msg_6857_, v___y_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_);
lean_dec(v___y_6868_);
lean_dec_ref(v___y_6867_);
lean_dec(v___y_6866_);
lean_dec_ref(v___y_6865_);
lean_dec(v___y_6864_);
lean_dec_ref(v___y_6863_);
lean_dec(v___y_6862_);
lean_dec_ref(v___y_6861_);
lean_dec(v___y_6860_);
lean_dec(v___y_6859_);
lean_dec_ref(v___y_6858_);
return v_res_6870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_, lean_object* v_a_6878_, lean_object* v_a_6879_, lean_object* v_a_6880_, lean_object* v_a_6881_, lean_object* v_a_6882_){
_start:
{
lean_object* v___x_6884_; 
v___x_6884_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6871_, v_a_6872_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_, v_a_6877_, v_a_6878_, v_a_6879_, v_a_6880_, v_a_6881_, v_a_6882_);
if (lean_obj_tag(v___x_6884_) == 0)
{
lean_object* v_a_6885_; lean_object* v___x_6886_; lean_object* v___x_6888_; uint8_t v_isShared_6889_; uint8_t v_isSharedCheck_6893_; 
v_a_6885_ = lean_ctor_get(v___x_6884_, 0);
lean_inc(v_a_6885_);
lean_dec_ref_known(v___x_6884_, 1);
v___x_6886_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_6872_, v_a_6873_);
v_isSharedCheck_6893_ = !lean_is_exclusive(v___x_6886_);
if (v_isSharedCheck_6893_ == 0)
{
lean_object* v_unused_6894_; 
v_unused_6894_ = lean_ctor_get(v___x_6886_, 0);
lean_dec(v_unused_6894_);
v___x_6888_ = v___x_6886_;
v_isShared_6889_ = v_isSharedCheck_6893_;
goto v_resetjp_6887_;
}
else
{
lean_dec(v___x_6886_);
v___x_6888_ = lean_box(0);
v_isShared_6889_ = v_isSharedCheck_6893_;
goto v_resetjp_6887_;
}
v_resetjp_6887_:
{
lean_object* v___x_6891_; 
if (v_isShared_6889_ == 0)
{
lean_ctor_set(v___x_6888_, 0, v_a_6885_);
v___x_6891_ = v___x_6888_;
goto v_reusejp_6890_;
}
else
{
lean_object* v_reuseFailAlloc_6892_; 
v_reuseFailAlloc_6892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6892_, 0, v_a_6885_);
v___x_6891_ = v_reuseFailAlloc_6892_;
goto v_reusejp_6890_;
}
v_reusejp_6890_:
{
return v___x_6891_;
}
}
}
else
{
return v___x_6884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_, lean_object* v_a_6903_, lean_object* v_a_6904_, lean_object* v_a_6905_, lean_object* v_a_6906_, lean_object* v_a_6907_){
_start:
{
lean_object* v_res_6908_; 
v_res_6908_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6895_, v_a_6896_, v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_, v_a_6905_, v_a_6906_);
lean_dec(v_a_6906_);
lean_dec_ref(v_a_6905_);
lean_dec(v_a_6904_);
lean_dec_ref(v_a_6903_);
lean_dec(v_a_6902_);
lean_dec_ref(v_a_6901_);
lean_dec(v_a_6900_);
lean_dec_ref(v_a_6899_);
lean_dec(v_a_6898_);
lean_dec(v_a_6897_);
lean_dec_ref(v_a_6896_);
lean_dec(v_passes_6895_);
return v_res_6908_;
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
