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
lean_object* v___y_2722_; lean_object* v___x_2740_; lean_object* v_toApplicative_2741_; lean_object* v_toFunctor_2742_; lean_object* v_toSeq_2743_; lean_object* v_toSeqLeft_2744_; lean_object* v_toSeqRight_2745_; lean_object* v___f_2746_; lean_object* v___f_2747_; lean_object* v___f_2748_; lean_object* v___f_2749_; lean_object* v___x_2750_; lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v_toApplicative_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2807_; 
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
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v___x_2756_, 1);
lean_dec(v_unused_2808_);
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2807_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_toApplicative_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2807_;
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
lean_object* v_toFunctor_2761_; lean_object* v_toSeq_2762_; lean_object* v_toSeqLeft_2763_; lean_object* v_toSeqRight_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2805_; 
v_toFunctor_2761_ = lean_ctor_get(v_toApplicative_2757_, 0);
v_toSeq_2762_ = lean_ctor_get(v_toApplicative_2757_, 2);
v_toSeqLeft_2763_ = lean_ctor_get(v_toApplicative_2757_, 3);
v_toSeqRight_2764_ = lean_ctor_get(v_toApplicative_2757_, 4);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_toApplicative_2757_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v_toApplicative_2757_, 1);
lean_dec(v_unused_2806_);
v___x_2766_ = v_toApplicative_2757_;
v_isShared_2767_ = v_isSharedCheck_2805_;
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
v_isShared_2767_ = v_isSharedCheck_2805_;
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
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___f_2768_);
lean_ctor_set(v_reuseFailAlloc_2804_, 2, v___f_2775_);
lean_ctor_set(v_reuseFailAlloc_2804_, 3, v___f_2774_);
lean_ctor_set(v_reuseFailAlloc_2804_, 4, v___f_2773_);
v___x_2777_ = v_reuseFailAlloc_2804_;
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
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___f_2769_);
v___x_2779_ = v_reuseFailAlloc_2803_;
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
v_options_2789_ = lean_ctor_get(v_a_2718_, 2);
v_hasTrace_2790_ = lean_ctor_get_uint8(v_options_2789_, sizeof(void*)*1);
if (v_hasTrace_2790_ == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_object* v_toMonadRef_2791_; lean_object* v_inheritedTraceOptions_2792_; lean_object* v_cls_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v_toMonadRef_2791_ = lean_ctor_get(v___x_2788_, 0);
v_inheritedTraceOptions_2792_ = lean_ctor_get(v_a_2718_, 13);
v_cls_2793_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2794_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2795_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2792_, v_options_2789_, v___x_2794_);
if (v___x_2795_ == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_object* v_type_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_5266__overap_2801_; lean_object* v___x_2802_; 
v_type_2796_ = lean_ctor_get(v_hyp_2708_, 1);
v___f_2797_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_2798_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_2796_);
v___x_2799_ = l_Lean_MessageData_ofExpr(v_type_2796_);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
lean_inc_ref(v_toMonadRef_2791_);
v___x_5266__overap_2801_ = l_Lean_addTrace___redArg(v___x_2786_, v___x_2787_, v_toMonadRef_2791_, v___f_2797_, v_cls_2793_, v___x_2800_);
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
v___x_2802_ = lean_apply_12(v___x_5266__overap_2801_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, lean_box(0));
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_dec_ref_known(v___x_2802_, 1);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_dec_ref(v_hyp_2708_);
return v___x_2802_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v_toMonadRef_2825_, lean_object* v___f_2826_, lean_object* v_x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_options_2844_; uint8_t v_hasTrace_2845_; 
v_options_2844_ = lean_ctor_get(v___y_2838_, 2);
v_hasTrace_2845_ = lean_ctor_get_uint8(v_options_2844_, sizeof(void*)*1);
if (v_hasTrace_2845_ == 0)
{
lean_dec_ref(v___y_2828_);
lean_dec(v___f_2826_);
lean_dec_ref(v_toMonadRef_2825_);
lean_dec_ref(v___x_2824_);
lean_dec_ref(v___x_2823_);
goto v___jp_2841_;
}
else
{
lean_object* v_inheritedTraceOptions_2846_; lean_object* v_cls_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_inheritedTraceOptions_2846_ = lean_ctor_get(v___y_2838_, 13);
v_cls_2847_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2848_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2849_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2846_, v_options_2844_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_dec_ref(v___y_2828_);
lean_dec(v___f_2826_);
lean_dec_ref(v_toMonadRef_2825_);
lean_dec_ref(v___x_2824_);
lean_dec_ref(v___x_2823_);
goto v___jp_2841_;
}
else
{
lean_object* v_type_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_6307__overap_2854_; lean_object* v___x_2855_; 
v_type_2850_ = lean_ctor_get(v___y_2828_, 1);
lean_inc_ref(v_type_2850_);
lean_dec_ref(v___y_2828_);
v___x_2851_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2852_ = l_Lean_MessageData_ofExpr(v_type_2850_);
v___x_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_6307__overap_2854_ = l_Lean_addTrace___redArg(v___x_2823_, v___x_2824_, v_toMonadRef_2825_, v___f_2826_, v_cls_2847_, v___x_2853_);
lean_inc(v___y_2839_);
lean_inc_ref(v___y_2838_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___y_2831_);
lean_inc(v___y_2830_);
lean_inc_ref(v___y_2829_);
v___x_2855_ = lean_apply_12(v___x_6307__overap_2854_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, lean_box(0));
return v___x_2855_;
}
}
v___jp_2841_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2856_ = _args[0];
lean_object* v___x_2857_ = _args[1];
lean_object* v_toMonadRef_2858_ = _args[2];
lean_object* v___f_2859_ = _args[3];
lean_object* v_x_2860_ = _args[4];
lean_object* v___y_2861_ = _args[5];
lean_object* v___y_2862_ = _args[6];
lean_object* v___y_2863_ = _args[7];
lean_object* v___y_2864_ = _args[8];
lean_object* v___y_2865_ = _args[9];
lean_object* v___y_2866_ = _args[10];
lean_object* v___y_2867_ = _args[11];
lean_object* v___y_2868_ = _args[12];
lean_object* v___y_2869_ = _args[13];
lean_object* v___y_2870_ = _args[14];
lean_object* v___y_2871_ = _args[15];
lean_object* v___y_2872_ = _args[16];
lean_object* v___y_2873_ = _args[17];
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2856_, v___x_2857_, v_toMonadRef_2858_, v___f_2859_, v_x_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___y_2907_; lean_object* v___x_2908_; lean_object* v_toApplicative_2909_; lean_object* v_toFunctor_2910_; lean_object* v_toSeq_2911_; lean_object* v_toSeqLeft_2912_; lean_object* v_toSeqRight_2913_; lean_object* v___f_2914_; lean_object* v___f_2915_; lean_object* v___f_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; lean_object* v___f_2919_; lean_object* v___f_2920_; lean_object* v___f_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v_toApplicative_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2977_; 
v___x_2908_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2909_ = lean_ctor_get(v___x_2908_, 0);
v_toFunctor_2910_ = lean_ctor_get(v_toApplicative_2909_, 0);
v_toSeq_2911_ = lean_ctor_get(v_toApplicative_2909_, 2);
v_toSeqLeft_2912_ = lean_ctor_get(v_toApplicative_2909_, 3);
v_toSeqRight_2913_ = lean_ctor_get(v_toApplicative_2909_, 4);
v___f_2914_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2915_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2910_, 2);
v___f_2916_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2916_, 0, v_toFunctor_2910_);
v___f_2917_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2917_, 0, v_toFunctor_2910_);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___f_2916_);
lean_ctor_set(v___x_2918_, 1, v___f_2917_);
lean_inc(v_toSeqRight_2913_);
v___f_2919_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2919_, 0, v_toSeqRight_2913_);
lean_inc(v_toSeqLeft_2912_);
v___f_2920_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2920_, 0, v_toSeqLeft_2912_);
lean_inc(v_toSeq_2911_);
v___f_2921_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2921_, 0, v_toSeq_2911_);
v___x_2922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2918_);
lean_ctor_set(v___x_2922_, 1, v___f_2914_);
lean_ctor_set(v___x_2922_, 2, v___f_2921_);
lean_ctor_set(v___x_2922_, 3, v___f_2920_);
lean_ctor_set(v___x_2922_, 4, v___f_2919_);
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v___f_2915_);
v___x_2924_ = l_StateRefT_x27_instMonad___redArg(v___x_2923_);
v_toApplicative_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v___x_2924_, 1);
lean_dec(v_unused_2978_);
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2977_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_toApplicative_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2977_;
goto v_resetjp_2926_;
}
v___jp_2888_:
{
lean_object* v___x_2889_; lean_object* v_caches_2890_; lean_object* v_typeAnalysis_2891_; lean_object* v_target_2892_; lean_object* v_hypotheses_2893_; uint8_t v_didChange_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2905_; 
v___x_2889_ = lean_st_ref_take(v_a_2877_);
v_caches_2890_ = lean_ctor_get(v___x_2889_, 0);
v_typeAnalysis_2891_ = lean_ctor_get(v___x_2889_, 1);
v_target_2892_ = lean_ctor_get(v___x_2889_, 2);
v_hypotheses_2893_ = lean_ctor_get(v___x_2889_, 3);
v_didChange_2894_ = lean_ctor_get_uint8(v___x_2889_, sizeof(void*)*4);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2896_ = v___x_2889_;
v_isShared_2897_ = v_isSharedCheck_2905_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_hypotheses_2893_);
lean_inc(v_target_2892_);
lean_inc(v_typeAnalysis_2891_);
lean_inc(v_caches_2890_);
lean_dec(v___x_2889_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2905_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2898_ = l_Array_append___redArg(v_hypotheses_2893_, v_hyps_2875_);
lean_dec_ref(v_hyps_2875_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 3, v___x_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_caches_2890_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_typeAnalysis_2891_);
lean_ctor_set(v_reuseFailAlloc_2904_, 2, v_target_2892_);
lean_ctor_set(v_reuseFailAlloc_2904_, 3, v___x_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2904_, sizeof(void*)*4, v_didChange_2894_);
v___x_2900_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = lean_st_ref_put(v_a_2877_, v___x_2900_);
v___x_2902_ = lean_box(0);
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
return v___x_2903_;
}
}
}
v___jp_2906_:
{
if (lean_obj_tag(v___y_2907_) == 0)
{
lean_dec_ref_known(v___y_2907_, 1);
goto v___jp_2888_;
}
else
{
lean_dec_ref(v_hyps_2875_);
return v___y_2907_;
}
}
v_resetjp_2926_:
{
lean_object* v_toFunctor_2929_; lean_object* v_toSeq_2930_; lean_object* v_toSeqLeft_2931_; lean_object* v_toSeqRight_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2975_; 
v_toFunctor_2929_ = lean_ctor_get(v_toApplicative_2925_, 0);
v_toSeq_2930_ = lean_ctor_get(v_toApplicative_2925_, 2);
v_toSeqLeft_2931_ = lean_ctor_get(v_toApplicative_2925_, 3);
v_toSeqRight_2932_ = lean_ctor_get(v_toApplicative_2925_, 4);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_toApplicative_2925_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v_toApplicative_2925_, 1);
lean_dec(v_unused_2976_);
v___x_2934_ = v_toApplicative_2925_;
v_isShared_2935_ = v_isSharedCheck_2975_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_toSeqRight_2932_);
lean_inc(v_toSeqLeft_2931_);
lean_inc(v_toSeq_2930_);
lean_inc(v_toFunctor_2929_);
lean_dec(v_toApplicative_2925_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2975_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___f_2936_; lean_object* v___f_2937_; lean_object* v___f_2938_; lean_object* v___f_2939_; lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___x_2945_; 
v___f_2936_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2937_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2929_);
v___f_2938_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2938_, 0, v_toFunctor_2929_);
v___f_2939_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2939_, 0, v_toFunctor_2929_);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___f_2938_);
lean_ctor_set(v___x_2940_, 1, v___f_2939_);
v___f_2941_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2941_, 0, v_toSeqRight_2932_);
v___f_2942_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2942_, 0, v_toSeqLeft_2931_);
v___f_2943_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2943_, 0, v_toSeq_2930_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 4, v___f_2941_);
lean_ctor_set(v___x_2934_, 3, v___f_2942_);
lean_ctor_set(v___x_2934_, 2, v___f_2943_);
lean_ctor_set(v___x_2934_, 1, v___f_2936_);
lean_ctor_set(v___x_2934_, 0, v___x_2940_);
v___x_2945_ = v___x_2934_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v___f_2936_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v___f_2943_);
lean_ctor_set(v_reuseFailAlloc_2974_, 3, v___f_2942_);
lean_ctor_set(v_reuseFailAlloc_2974_, 4, v___f_2941_);
v___x_2945_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2947_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 1, v___f_2937_);
lean_ctor_set(v___x_2927_, 0, v___x_2945_);
v___x_2947_ = v___x_2927_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___f_2937_);
v___x_2947_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_toMonadRef_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2948_ = l_StateRefT_x27_instMonad___redArg(v___x_2947_);
v___x_2949_ = l_ReaderT_instMonad___redArg(v___x_2948_);
v___x_2950_ = l_StateRefT_x27_instMonad___redArg(v___x_2949_);
v___x_2951_ = l_ReaderT_instMonad___redArg(v___x_2950_);
v___x_2952_ = l_ReaderT_instMonad___redArg(v___x_2951_);
v___x_2953_ = l_StateRefT_x27_instMonad___redArg(v___x_2952_);
v___x_2954_ = l_ReaderT_instMonad___redArg(v___x_2953_);
v___x_2955_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2956_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_2957_ = lean_ctor_get(v___x_2956_, 0);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = lean_array_get_size(v_hyps_2875_);
v___x_2960_ = lean_nat_dec_lt(v___x_2958_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v___x_2954_);
goto v___jp_2888_;
}
else
{
lean_object* v___f_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___f_2961_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
lean_inc_ref(v_toMonadRef_2957_);
lean_inc_ref(v___x_2954_);
v___f_2962_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 18, 4);
lean_closure_set(v___f_2962_, 0, v___x_2954_);
lean_closure_set(v___f_2962_, 1, v___x_2955_);
lean_closure_set(v___f_2962_, 2, v_toMonadRef_2957_);
lean_closure_set(v___f_2962_, 3, v___f_2961_);
v___x_2963_ = lean_box(0);
v___x_2964_ = lean_nat_dec_le(v___x_2959_, v___x_2959_);
if (v___x_2964_ == 0)
{
if (v___x_2960_ == 0)
{
lean_dec_ref(v___f_2962_);
lean_dec_ref(v___x_2954_);
goto v___jp_2888_;
}
else
{
size_t v___x_2965_; size_t v___x_2966_; lean_object* v___x_5991__overap_2967_; lean_object* v___x_2968_; 
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = lean_usize_of_nat(v___x_2959_);
lean_inc_ref(v_hyps_2875_);
v___x_5991__overap_2967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2954_, v___f_2962_, v_hyps_2875_, v___x_2965_, v___x_2966_, v___x_2963_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc_ref(v_a_2883_);
lean_inc(v_a_2882_);
lean_inc_ref(v_a_2881_);
lean_inc(v_a_2880_);
lean_inc_ref(v_a_2879_);
lean_inc(v_a_2878_);
lean_inc(v_a_2877_);
lean_inc_ref(v_a_2876_);
v___x_2968_ = lean_apply_12(v___x_5991__overap_2967_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, lean_box(0));
v___y_2907_ = v___x_2968_;
goto v___jp_2906_;
}
}
else
{
size_t v___x_2969_; size_t v___x_2970_; lean_object* v___x_5994__overap_2971_; lean_object* v___x_2972_; 
v___x_2969_ = ((size_t)0ULL);
v___x_2970_ = lean_usize_of_nat(v___x_2959_);
lean_inc_ref(v_hyps_2875_);
v___x_5994__overap_2971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2954_, v___f_2962_, v_hyps_2875_, v___x_2969_, v___x_2970_, v___x_2963_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc_ref(v_a_2883_);
lean_inc(v_a_2882_);
lean_inc_ref(v_a_2881_);
lean_inc(v_a_2880_);
lean_inc_ref(v_a_2879_);
lean_inc(v_a_2878_);
lean_inc(v_a_2877_);
lean_inc_ref(v_a_2876_);
v___x_2972_ = lean_apply_12(v___x_5994__overap_2971_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, lean_box(0));
v___y_2907_ = v___x_2972_;
goto v___jp_2906_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_2993_){
_start:
{
lean_object* v___x_2995_; lean_object* v_hypotheses_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_st_ref_get(v_a_2993_);
v_hypotheses_2996_ = lean_ctor_get(v___x_2995_, 3);
lean_inc_ref(v_hypotheses_2996_);
lean_dec(v___x_2995_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_hypotheses_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_2998_);
lean_dec(v_a_2998_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v_hypotheses_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_st_ref_get(v_a_3002_);
v_hypotheses_3014_ = lean_ctor_get(v___x_3013_, 3);
lean_inc_ref(v_hypotheses_3014_);
lean_dec(v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_hypotheses_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v_caches_3043_; lean_object* v_typeAnalysis_3044_; lean_object* v_target_3045_; uint8_t v_didChange_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3056_; 
v___x_3042_ = lean_st_ref_take(v___y_3031_);
v_caches_3043_ = lean_ctor_get(v___x_3042_, 0);
v_typeAnalysis_3044_ = lean_ctor_get(v___x_3042_, 1);
v_target_3045_ = lean_ctor_get(v___x_3042_, 2);
v_didChange_3046_ = lean_ctor_get_uint8(v___x_3042_, sizeof(void*)*4);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3042_, 3);
lean_dec(v_unused_3057_);
v___x_3048_ = v___x_3042_;
v_isShared_3049_ = v_isSharedCheck_3056_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_target_3045_);
lean_inc(v_typeAnalysis_3044_);
lean_inc(v_caches_3043_);
lean_dec(v___x_3042_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3056_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 3, v_hyps_3029_);
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_caches_3043_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_typeAnalysis_3044_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_target_3045_);
lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_hyps_3029_);
lean_ctor_set_uint8(v_reuseFailAlloc_3055_, sizeof(void*)*4, v_didChange_3046_);
v___x_3051_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_st_ref_put(v___y_3031_, v___x_3051_);
v___x_3053_ = lean_box(0);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3072_, lean_object* v_hyps_3073_){
_start:
{
lean_object* v___f_3074_; lean_object* v___x_3075_; 
v___f_3074_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3074_, 0, v_hyps_3073_);
v___x_3075_ = lean_apply_2(v_inst_3072_, lean_box(0), v___f_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; lean_object* v_caches_3089_; lean_object* v_typeAnalysis_3090_; lean_object* v_target_3091_; uint8_t v_didChange_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3103_; 
v___x_3088_ = lean_st_ref_take(v___y_3077_);
v_caches_3089_ = lean_ctor_get(v___x_3088_, 0);
v_typeAnalysis_3090_ = lean_ctor_get(v___x_3088_, 1);
v_target_3091_ = lean_ctor_get(v___x_3088_, 2);
v_didChange_3092_ = lean_ctor_get_uint8(v___x_3088_, sizeof(void*)*4);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; 
v_unused_3104_ = lean_ctor_get(v___x_3088_, 3);
lean_dec(v_unused_3104_);
v___x_3094_ = v___x_3088_;
v_isShared_3095_ = v_isSharedCheck_3103_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_target_3091_);
lean_inc(v_typeAnalysis_3090_);
lean_inc(v_caches_3089_);
lean_dec(v___x_3088_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3103_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3096_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 3, v___x_3096_);
v___x_3098_ = v___x_3094_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_caches_3089_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_typeAnalysis_3090_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_target_3091_);
lean_ctor_set(v_reuseFailAlloc_3102_, 3, v___x_3096_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*4, v_didChange_3092_);
v___x_3098_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = lean_st_ref_put(v___y_3077_, v___x_3098_);
v___x_3100_ = lean_box(0);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
return v___x_3101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3118_, lean_object* v_cls_3119_, lean_object* v_____do__lift_3120_, lean_object* v_____do__lift_3121_){
_start:
{
uint8_t v_hasTrace_3122_; 
v_hasTrace_3122_ = lean_ctor_get_uint8(v_____do__lift_3121_, sizeof(void*)*1);
if (v_hasTrace_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_dec(v_cls_3119_);
v___x_3123_ = lean_box(v_hasTrace_3122_);
v___x_3124_ = lean_apply_2(v_toPure_3118_, lean_box(0), v___x_3123_);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3125_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3126_ = l_Lean_Name_append(v___x_3125_, v_cls_3119_);
v___x_3127_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3120_, v_____do__lift_3121_, v___x_3126_);
lean_dec(v___x_3126_);
v___x_3128_ = lean_box(v___x_3127_);
v___x_3129_ = lean_apply_2(v_toPure_3118_, lean_box(0), v___x_3128_);
return v___x_3129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3130_, lean_object* v_cls_3131_, lean_object* v_____do__lift_3132_, lean_object* v_____do__lift_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3130_, v_cls_3131_, v_____do__lift_3132_, v_____do__lift_3133_);
lean_dec_ref(v_____do__lift_3133_);
lean_dec_ref(v_____do__lift_3132_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_toPure_3135_, lean_object* v_cls_3136_, lean_object* v_toBind_3137_, lean_object* v_inst_3138_, lean_object* v_____do__lift_3139_){
_start:
{
lean_object* v___f_3140_; lean_object* v___x_3141_; 
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3140_, 0, v_toPure_3135_);
lean_closure_set(v___f_3140_, 1, v_cls_3136_);
lean_closure_set(v___f_3140_, 2, v_____do__lift_3139_);
v___x_3141_ = lean_apply_4(v_toBind_3137_, lean_box(0), lean_box(0), v_inst_3138_, v___f_3140_);
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
uint8_t v_____do__lift_3036__boxed_3173_; lean_object* v_res_3174_; 
v_____do__lift_3036__boxed_3173_ = lean_unbox(v_____do__lift_3172_);
v_res_3174_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3164_, v_a_3165_, v___y_3166_, v_inst_3167_, v_inst_3168_, v_inst_3169_, v_inst_3170_, v_cls_3171_, v_____do__lift_3036__boxed_3173_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3175_, lean_object* v_toPure_3176_, lean_object* v_toBind_3177_, lean_object* v_inst_3178_, lean_object* v_a_3179_, lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_x_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_getInheritedTraceOptions_3185_; lean_object* v_cls_3186_; lean_object* v___f_3187_; lean_object* v___f_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_getInheritedTraceOptions_3185_ = lean_ctor_get(v_inst_3175_, 2);
lean_inc(v_getInheritedTraceOptions_3185_);
v_cls_3186_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3177_, 2);
lean_inc(v_toPure_3176_);
v___f_3187_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3187_, 0, v_toPure_3176_);
lean_closure_set(v___f_3187_, 1, v_cls_3186_);
lean_closure_set(v___f_3187_, 2, v_toBind_3177_);
lean_closure_set(v___f_3187_, 3, v_inst_3178_);
v___f_3188_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3188_, 0, v_toPure_3176_);
lean_closure_set(v___f_3188_, 1, v_a_3179_);
lean_closure_set(v___f_3188_, 2, v___y_3184_);
lean_closure_set(v___f_3188_, 3, v_inst_3180_);
lean_closure_set(v___f_3188_, 4, v_inst_3175_);
lean_closure_set(v___f_3188_, 5, v_inst_3181_);
lean_closure_set(v___f_3188_, 6, v_inst_3182_);
lean_closure_set(v___f_3188_, 7, v_cls_3186_);
v___x_3189_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3185_, v___f_3187_);
v___x_3190_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v___x_3189_, v___f_3188_);
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
uint8_t v_____do__lift_3136__boxed_3236_; lean_object* v_res_3237_; 
v_____do__lift_3136__boxed_3236_ = lean_unbox(v_____do__lift_3235_);
v_res_3237_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3225_, v_type_3226_, v_type_3227_, v_inst_3228_, v_inst_3229_, v_inst_3230_, v_inst_3231_, v_cls_3232_, v_toBind_3233_, v___f_3234_, v_____do__lift_3136__boxed_3236_);
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
lean_dec(v_inst_3245_);
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
lean_closure_set(v___f_3282_, 0, v_toPure_3238_);
lean_closure_set(v___f_3282_, 1, v_cls_3281_);
lean_closure_set(v___f_3282_, 2, v_toBind_3240_);
lean_closure_set(v___f_3282_, 3, v_inst_3245_);
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
lean_dec(v_inst_3245_);
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
lean_dec(v_inst_3245_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3313_, lean_object* v_toPure_3314_, lean_object* v_toBind_3315_, lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_f_3321_, lean_object* v_bs_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v___f_3324_; lean_object* v___f_3325_; lean_object* v___f_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_inc(v_inst_3319_);
lean_inc_ref(v_inst_3318_);
lean_inc_ref(v_inst_3317_);
lean_inc_ref_n(v_a_3323_, 2);
lean_inc(v_inst_3316_);
lean_inc_n(v_toBind_3315_, 3);
lean_inc_n(v_toPure_3314_, 2);
lean_inc_ref(v_inst_3313_);
v___f_3324_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3324_, 0, v_inst_3313_);
lean_closure_set(v___f_3324_, 1, v_toPure_3314_);
lean_closure_set(v___f_3324_, 2, v_toBind_3315_);
lean_closure_set(v___f_3324_, 3, v_inst_3316_);
lean_closure_set(v___f_3324_, 4, v_a_3323_);
lean_closure_set(v___f_3324_, 5, v_inst_3317_);
lean_closure_set(v___f_3324_, 6, v_inst_3318_);
lean_closure_set(v___f_3324_, 7, v_inst_3319_);
lean_inc_ref(v___f_3324_);
v___f_3325_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3325_, 0, v_toPure_3314_);
lean_closure_set(v___f_3325_, 1, v_inst_3320_);
lean_closure_set(v___f_3325_, 2, v_toBind_3315_);
lean_closure_set(v___f_3325_, 3, v_inst_3317_);
lean_closure_set(v___f_3325_, 4, v___f_3324_);
lean_closure_set(v___f_3325_, 5, v_a_3323_);
lean_closure_set(v___f_3325_, 6, v_inst_3313_);
lean_closure_set(v___f_3325_, 7, v_inst_3316_);
lean_closure_set(v___f_3325_, 8, v_inst_3318_);
lean_closure_set(v___f_3325_, 9, v_inst_3319_);
lean_closure_set(v___f_3325_, 10, v___f_3324_);
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3326_, 0, v_bs_3322_);
lean_closure_set(v___f_3326_, 1, v_toPure_3314_);
v___x_3327_ = lean_apply_1(v_f_3321_, v_a_3323_);
v___x_3328_ = lean_apply_4(v_toBind_3315_, lean_box(0), lean_box(0), v___x_3327_, v___f_3325_);
v___x_3329_ = lean_apply_4(v_toBind_3315_, lean_box(0), lean_box(0), v___x_3328_, v___f_3326_);
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
lean_closure_set(v___f_3375_, 1, v_toPure_3370_);
lean_closure_set(v___f_3375_, 2, v_toBind_3369_);
lean_closure_set(v___f_3375_, 3, v_inst_3363_);
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
lean_closure_set(v___f_3393_, 1, v_toPure_3388_);
lean_closure_set(v___f_3393_, 2, v_toBind_3387_);
lean_closure_set(v___f_3393_, 3, v_inst_3381_);
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
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 3, v_snd_3401_);
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
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
v___x_3423_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = lean_st_ref_put(v___y_3403_, v___x_3423_);
v___x_3425_ = lean_box(0);
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
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
uint8_t v___x_1673__boxed_3487_; lean_object* v_res_3488_; 
v___x_1673__boxed_3487_ = lean_unbox(v___x_3483_);
v_res_3488_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_1673__boxed_3487_, v_snd_3484_, v_toPure_3485_, v_____r_3486_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v_toPure_3515_, lean_object* v___x_3516_, lean_object* v_toBind_3517_, lean_object* v_inst_3518_, lean_object* v_____do__lift_3519_){
_start:
{
lean_object* v___f_3520_; lean_object* v___x_3521_; 
v___f_3520_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_3520_, 0, v_toPure_3515_);
lean_closure_set(v___f_3520_, 1, v___x_3516_);
lean_closure_set(v___f_3520_, 2, v_____do__lift_3519_);
v___x_3521_ = lean_apply_4(v_toBind_3517_, lean_box(0), lean_box(0), v_inst_3518_, v___f_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object* v___f_3522_, lean_object* v___x_3523_, lean_object* v_type_3524_, lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_toMonadRef_3527_, lean_object* v_inst_3528_, lean_object* v___x_3529_, lean_object* v_toBind_3530_, lean_object* v___f_3531_, uint8_t v_____do__lift_3532_){
_start:
{
if (v_____do__lift_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec(v___f_3531_);
lean_dec(v_toBind_3530_);
lean_dec(v___x_3529_);
lean_dec(v_inst_3528_);
lean_dec_ref(v_toMonadRef_3527_);
lean_dec_ref(v_inst_3526_);
lean_dec_ref(v_inst_3525_);
lean_dec_ref(v_type_3524_);
lean_dec_ref(v___x_3523_);
v___x_3533_ = lean_box(0);
v___x_3534_ = lean_apply_1(v___f_3522_, v___x_3533_);
return v___x_3534_;
}
else
{
lean_object* v_type_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_dec(v___f_3522_);
v_type_3535_ = lean_ctor_get(v___x_3523_, 1);
lean_inc_ref(v_type_3535_);
lean_dec_ref(v___x_3523_);
v___x_3536_ = l_Lean_MessageData_ofExpr(v_type_3535_);
v___x_3537_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = l_Lean_MessageData_ofExpr(v_type_3524_);
v___x_3540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3538_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = l_Lean_addTrace___redArg(v_inst_3525_, v_inst_3526_, v_toMonadRef_3527_, v_inst_3528_, v___x_3529_, v___x_3540_);
v___x_3542_ = lean_apply_4(v_toBind_3530_, lean_box(0), lean_box(0), v___x_3541_, v___f_3531_);
return v___x_3542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___f_3543_, lean_object* v___x_3544_, lean_object* v_type_3545_, lean_object* v_inst_3546_, lean_object* v_inst_3547_, lean_object* v_toMonadRef_3548_, lean_object* v_inst_3549_, lean_object* v___x_3550_, lean_object* v_toBind_3551_, lean_object* v___f_3552_, lean_object* v_____do__lift_3553_){
_start:
{
uint8_t v_____do__lift_1748__boxed_3554_; lean_object* v_res_3555_; 
v_____do__lift_1748__boxed_3554_ = lean_unbox(v_____do__lift_3553_);
v_res_3555_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3543_, v___x_3544_, v_type_3545_, v_inst_3546_, v_inst_3547_, v_toMonadRef_3548_, v_inst_3549_, v___x_3550_, v_toBind_3551_, v___f_3552_, v_____do__lift_1748__boxed_3554_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v___x_3556_, lean_object* v_snd_3557_, lean_object* v___x_3558_, lean_object* v_toPure_3559_, lean_object* v_inst_3560_, lean_object* v_toBind_3561_, lean_object* v_inst_3562_, lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_toMonadRef_3565_, lean_object* v_inst_3566_, lean_object* v___f_3567_, lean_object* v_newHyp_3568_){
_start:
{
lean_object* v_type_3569_; lean_object* v_value_3570_; uint8_t v___x_3571_; 
v_type_3569_ = lean_ctor_get(v_newHyp_3568_, 1);
v_value_3570_ = lean_ctor_get(v_newHyp_3568_, 2);
lean_inc_ref(v_type_3569_);
v___x_3571_ = l_Lean_Expr_isFalse(v_type_3569_);
if (v___x_3571_ == 0)
{
lean_object* v_type_3572_; lean_object* v___f_3573_; lean_object* v___f_3574_; lean_object* v___f_3575_; lean_object* v___f_3576_; uint8_t v___x_3584_; 
lean_dec(v___f_3567_);
v_type_3572_ = lean_ctor_get(v___x_3556_, 1);
lean_inc(v_toPure_3559_);
lean_inc(v___x_3558_);
lean_inc_ref(v_newHyp_3568_);
lean_inc(v_snd_3557_);
v___f_3573_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3573_, 0, v_snd_3557_);
lean_closure_set(v___f_3573_, 1, v_newHyp_3568_);
lean_closure_set(v___f_3573_, 2, v___x_3558_);
lean_closure_set(v___f_3573_, 3, v_toPure_3559_);
v___f_3574_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3574_, 0, v___f_3573_);
lean_inc(v_toBind_3561_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3575_, 0, v_inst_3560_);
lean_closure_set(v___f_3575_, 1, v_toBind_3561_);
lean_closure_set(v___f_3575_, 2, v___f_3574_);
lean_inc_ref(v___f_3575_);
v___f_3576_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3576_, 0, v___f_3575_);
v___x_3584_ = lean_expr_eqv(v_type_3572_, v_type_3569_);
if (v___x_3584_ == 0)
{
lean_inc_ref(v_type_3569_);
lean_dec_ref(v_newHyp_3568_);
lean_dec(v___x_3558_);
lean_dec(v_snd_3557_);
goto v___jp_3577_;
}
else
{
if (v___x_3571_ == 0)
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec_ref(v___f_3576_);
lean_dec_ref(v___f_3575_);
lean_dec(v_inst_3566_);
lean_dec_ref(v_toMonadRef_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec(v_inst_3563_);
lean_dec_ref(v_inst_3562_);
lean_dec(v_toBind_3561_);
lean_dec_ref(v___x_3556_);
v___x_3585_ = lean_box(0);
v___x_3586_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3557_, v_newHyp_3568_, v___x_3558_, v_toPure_3559_, v___x_3585_);
return v___x_3586_;
}
else
{
lean_inc_ref(v_type_3569_);
lean_dec_ref(v_newHyp_3568_);
lean_dec(v___x_3558_);
lean_dec(v_snd_3557_);
goto v___jp_3577_;
}
}
v___jp_3577_:
{
lean_object* v_getInheritedTraceOptions_3578_; lean_object* v___x_3579_; lean_object* v___f_3580_; lean_object* v___f_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v_getInheritedTraceOptions_3578_ = lean_ctor_get(v_inst_3562_, 2);
lean_inc(v_getInheritedTraceOptions_3578_);
v___x_3579_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3561_, 3);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3580_, 0, v_toPure_3559_);
lean_closure_set(v___f_3580_, 1, v___x_3579_);
lean_closure_set(v___f_3580_, 2, v_toBind_3561_);
lean_closure_set(v___f_3580_, 3, v_inst_3563_);
v___f_3581_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3581_, 0, v___f_3575_);
lean_closure_set(v___f_3581_, 1, v___x_3556_);
lean_closure_set(v___f_3581_, 2, v_type_3569_);
lean_closure_set(v___f_3581_, 3, v_inst_3564_);
lean_closure_set(v___f_3581_, 4, v_inst_3562_);
lean_closure_set(v___f_3581_, 5, v_toMonadRef_3565_);
lean_closure_set(v___f_3581_, 6, v_inst_3566_);
lean_closure_set(v___f_3581_, 7, v___x_3579_);
lean_closure_set(v___f_3581_, 8, v_toBind_3561_);
lean_closure_set(v___f_3581_, 9, v___f_3576_);
v___x_3582_ = lean_apply_4(v_toBind_3561_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3578_, v___f_3580_);
v___x_3583_ = lean_apply_4(v_toBind_3561_, lean_box(0), lean_box(0), v___x_3582_, v___f_3581_);
return v___x_3583_;
}
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_inc_ref(v_value_3570_);
lean_dec_ref(v_newHyp_3568_);
lean_dec(v_inst_3566_);
lean_dec_ref(v_toMonadRef_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec(v_inst_3563_);
lean_dec_ref(v_inst_3562_);
lean_dec(v_toPure_3559_);
lean_dec(v___x_3558_);
lean_dec(v_snd_3557_);
lean_dec_ref(v___x_3556_);
v___x_3587_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3587_, 0, v_value_3570_);
v___x_3588_ = lean_apply_2(v_inst_3560_, lean_box(0), v___x_3587_);
v___x_3589_ = lean_apply_4(v_toBind_3561_, lean_box(0), lean_box(0), v___x_3588_, v___f_3567_);
return v___x_3589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3590_, lean_object* v_toPure_3591_, lean_object* v_hyps_3592_, lean_object* v___x_3593_, lean_object* v_inst_3594_, lean_object* v_toBind_3595_, lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_toMonadRef_3599_, lean_object* v_inst_3600_, lean_object* v_f_3601_, lean_object* v___f_3602_, lean_object* v_next_3603_, lean_object* v_acc_3604_, lean_object* v_h_3605_, lean_object* v_G_3606_){
_start:
{
uint8_t v___x_3607_; 
v___x_3607_ = lean_nat_dec_lt(v_next_3603_, v___x_3590_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; 
lean_dec(v_G_3606_);
lean_dec(v_next_3603_);
lean_dec(v___f_3602_);
lean_dec(v_f_3601_);
lean_dec(v_inst_3600_);
lean_dec_ref(v_toMonadRef_3599_);
lean_dec_ref(v_inst_3598_);
lean_dec(v_inst_3597_);
lean_dec_ref(v_inst_3596_);
lean_dec(v_toBind_3595_);
lean_dec(v_inst_3594_);
lean_dec(v___x_3593_);
v___x_3608_ = lean_apply_2(v_toPure_3591_, lean_box(0), v_acc_3604_);
return v___x_3608_;
}
else
{
lean_object* v_snd_3609_; lean_object* v___f_3610_; lean_object* v___x_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; lean_object* v___f_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_snd_3609_ = lean_ctor_get(v_acc_3604_, 1);
lean_inc_n(v_snd_3609_, 2);
lean_dec_ref(v_acc_3604_);
lean_inc(v_next_3603_);
lean_inc_n(v_toPure_3591_, 2);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3610_, 0, v_toPure_3591_);
lean_closure_set(v___f_3610_, 1, v_next_3603_);
lean_closure_set(v___f_3610_, 2, v_G_3606_);
v___x_3611_ = lean_box(v___x_3607_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3612_, 0, v___x_3611_);
lean_closure_set(v___f_3612_, 1, v_snd_3609_);
lean_closure_set(v___f_3612_, 2, v_toPure_3591_);
v___x_3613_ = lean_array_fget_borrowed(v_hyps_3592_, v_next_3603_);
lean_inc_n(v_toBind_3595_, 3);
lean_inc_n(v___x_3613_, 2);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9), 13, 12);
lean_closure_set(v___f_3614_, 0, v___x_3613_);
lean_closure_set(v___f_3614_, 1, v_snd_3609_);
lean_closure_set(v___f_3614_, 2, v___x_3593_);
lean_closure_set(v___f_3614_, 3, v_toPure_3591_);
lean_closure_set(v___f_3614_, 4, v_inst_3594_);
lean_closure_set(v___f_3614_, 5, v_toBind_3595_);
lean_closure_set(v___f_3614_, 6, v_inst_3596_);
lean_closure_set(v___f_3614_, 7, v_inst_3597_);
lean_closure_set(v___f_3614_, 8, v_inst_3598_);
lean_closure_set(v___f_3614_, 9, v_toMonadRef_3599_);
lean_closure_set(v___f_3614_, 10, v_inst_3600_);
lean_closure_set(v___f_3614_, 11, v___f_3612_);
v___x_3615_ = lean_apply_2(v_f_3601_, v_next_3603_, v___x_3613_);
v___x_3616_ = lean_apply_4(v_toBind_3595_, lean_box(0), lean_box(0), v___x_3615_, v___f_3614_);
v___x_3617_ = lean_apply_4(v_toBind_3595_, lean_box(0), lean_box(0), v___x_3616_, v___f_3602_);
v___x_3618_ = lean_apply_4(v_toBind_3595_, lean_box(0), lean_box(0), v___x_3617_, v___f_3610_);
return v___x_3618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3619_ = _args[0];
lean_object* v_toPure_3620_ = _args[1];
lean_object* v_hyps_3621_ = _args[2];
lean_object* v___x_3622_ = _args[3];
lean_object* v_inst_3623_ = _args[4];
lean_object* v_toBind_3624_ = _args[5];
lean_object* v_inst_3625_ = _args[6];
lean_object* v_inst_3626_ = _args[7];
lean_object* v_inst_3627_ = _args[8];
lean_object* v_toMonadRef_3628_ = _args[9];
lean_object* v_inst_3629_ = _args[10];
lean_object* v_f_3630_ = _args[11];
lean_object* v___f_3631_ = _args[12];
lean_object* v_next_3632_ = _args[13];
lean_object* v_acc_3633_ = _args[14];
lean_object* v_h_3634_ = _args[15];
lean_object* v_G_3635_ = _args[16];
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3619_, v_toPure_3620_, v_hyps_3621_, v___x_3622_, v_inst_3623_, v_toBind_3624_, v_inst_3625_, v_inst_3626_, v_inst_3627_, v_toMonadRef_3628_, v_inst_3629_, v_f_3630_, v___f_3631_, v_next_3632_, v_acc_3633_, v_h_3634_, v_G_3635_);
lean_dec_ref(v_hyps_3621_);
lean_dec(v___x_3619_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3637_, lean_object* v_inst_3638_, lean_object* v_toBind_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_inst_3642_, lean_object* v_toMonadRef_3643_, lean_object* v_inst_3644_, lean_object* v_f_3645_, lean_object* v___f_3646_, lean_object* v___f_3647_, lean_object* v_hyps_3648_){
_start:
{
lean_object* v___x_3649_; lean_object* v_newHyps_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___f_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3649_ = lean_array_get_size(v_hyps_3648_);
v_newHyps_3650_ = lean_mk_empty_array_with_capacity(v___x_3649_);
v___x_3651_ = lean_unsigned_to_nat(0u);
v___x_3652_ = lean_box(0);
lean_inc(v_toBind_3639_);
v___f_3653_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3653_, 0, v___x_3649_);
lean_closure_set(v___f_3653_, 1, v_toPure_3637_);
lean_closure_set(v___f_3653_, 2, v_hyps_3648_);
lean_closure_set(v___f_3653_, 3, v___x_3652_);
lean_closure_set(v___f_3653_, 4, v_inst_3638_);
lean_closure_set(v___f_3653_, 5, v_toBind_3639_);
lean_closure_set(v___f_3653_, 6, v_inst_3640_);
lean_closure_set(v___f_3653_, 7, v_inst_3641_);
lean_closure_set(v___f_3653_, 8, v_inst_3642_);
lean_closure_set(v___f_3653_, 9, v_toMonadRef_3643_);
lean_closure_set(v___f_3653_, 10, v_inst_3644_);
lean_closure_set(v___f_3653_, 11, v_f_3645_);
lean_closure_set(v___f_3653_, 12, v___f_3646_);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v_newHyps_3650_);
v___x_3655_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3653_, v___x_3651_, v___x_3654_, lean_box(0));
v___x_3656_ = lean_apply_4(v_toBind_3639_, lean_box(0), lean_box(0), v___x_3655_, v___f_3647_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3657_, lean_object* v_inst_3658_, lean_object* v_inst_3659_, lean_object* v_inst_3660_, lean_object* v_inst_3661_, lean_object* v_inst_3662_, lean_object* v_f_3663_){
_start:
{
lean_object* v_toApplicative_3664_; lean_object* v_toBind_3665_; lean_object* v_toPure_3666_; lean_object* v_toMonadRef_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___f_3670_; lean_object* v___f_3671_; lean_object* v___f_3672_; lean_object* v___f_3673_; lean_object* v___x_3674_; 
v_toApplicative_3664_ = lean_ctor_get(v_inst_3657_, 0);
v_toBind_3665_ = lean_ctor_get(v_inst_3657_, 1);
lean_inc_n(v_toBind_3665_, 3);
v_toPure_3666_ = lean_ctor_get(v_toApplicative_3664_, 1);
lean_inc_n(v_toPure_3666_, 4);
v_toMonadRef_3667_ = lean_ctor_get(v_inst_3659_, 1);
lean_inc_ref(v_toMonadRef_3667_);
lean_dec_ref(v_inst_3659_);
v___x_3668_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3658_, 2);
v___x_3669_ = lean_apply_2(v_inst_3658_, lean_box(0), v___x_3668_);
v___f_3670_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3670_, 0, v_toPure_3666_);
v___f_3671_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3671_, 0, v_inst_3658_);
lean_closure_set(v___f_3671_, 1, v_toBind_3665_);
lean_closure_set(v___f_3671_, 2, v___f_3670_);
lean_closure_set(v___f_3671_, 3, v_toPure_3666_);
v___f_3672_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3672_, 0, v_toPure_3666_);
v___f_3673_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3673_, 0, v_toPure_3666_);
lean_closure_set(v___f_3673_, 1, v_inst_3658_);
lean_closure_set(v___f_3673_, 2, v_toBind_3665_);
lean_closure_set(v___f_3673_, 3, v_inst_3660_);
lean_closure_set(v___f_3673_, 4, v_inst_3661_);
lean_closure_set(v___f_3673_, 5, v_inst_3657_);
lean_closure_set(v___f_3673_, 6, v_toMonadRef_3667_);
lean_closure_set(v___f_3673_, 7, v_inst_3662_);
lean_closure_set(v___f_3673_, 8, v_f_3663_);
lean_closure_set(v___f_3673_, 9, v___f_3672_);
lean_closure_set(v___f_3673_, 10, v___f_3671_);
v___x_3674_ = lean_apply_4(v_toBind_3665_, lean_box(0), lean_box(0), v___x_3669_, v___f_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3675_, lean_object* v_inst_3676_, lean_object* v_inst_3677_, lean_object* v_inst_3678_, lean_object* v_inst_3679_, lean_object* v_inst_3680_, lean_object* v_inst_3681_, lean_object* v_inst_3682_, lean_object* v_inst_3683_, lean_object* v_f_3684_){
_start:
{
lean_object* v_toApplicative_3685_; lean_object* v_toBind_3686_; lean_object* v_toPure_3687_; lean_object* v_toMonadRef_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___f_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___x_3695_; 
v_toApplicative_3685_ = lean_ctor_get(v_inst_3676_, 0);
v_toBind_3686_ = lean_ctor_get(v_inst_3676_, 1);
lean_inc_n(v_toBind_3686_, 3);
v_toPure_3687_ = lean_ctor_get(v_toApplicative_3685_, 1);
lean_inc_n(v_toPure_3687_, 4);
v_toMonadRef_3688_ = lean_ctor_get(v_inst_3678_, 1);
lean_inc_ref(v_toMonadRef_3688_);
lean_dec_ref(v_inst_3678_);
v___x_3689_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3677_, 2);
v___x_3690_ = lean_apply_2(v_inst_3677_, lean_box(0), v___x_3689_);
v___f_3691_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3691_, 0, v_toPure_3687_);
v___f_3692_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3692_, 0, v_inst_3677_);
lean_closure_set(v___f_3692_, 1, v_toBind_3686_);
lean_closure_set(v___f_3692_, 2, v___f_3691_);
lean_closure_set(v___f_3692_, 3, v_toPure_3687_);
v___f_3693_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3693_, 0, v_toPure_3687_);
v___f_3694_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3694_, 0, v_toPure_3687_);
lean_closure_set(v___f_3694_, 1, v_inst_3677_);
lean_closure_set(v___f_3694_, 2, v_toBind_3686_);
lean_closure_set(v___f_3694_, 3, v_inst_3680_);
lean_closure_set(v___f_3694_, 4, v_inst_3681_);
lean_closure_set(v___f_3694_, 5, v_inst_3676_);
lean_closure_set(v___f_3694_, 6, v_toMonadRef_3688_);
lean_closure_set(v___f_3694_, 7, v_inst_3682_);
lean_closure_set(v___f_3694_, 8, v_f_3684_);
lean_closure_set(v___f_3694_, 9, v___f_3693_);
lean_closure_set(v___f_3694_, 10, v___f_3692_);
v___x_3695_ = lean_apply_4(v_toBind_3686_, lean_box(0), lean_box(0), v___x_3690_, v___f_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3696_, lean_object* v_inst_3697_, lean_object* v_inst_3698_, lean_object* v_inst_3699_, lean_object* v_inst_3700_, lean_object* v_inst_3701_, lean_object* v_inst_3702_, lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_f_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3696_, v_inst_3697_, v_inst_3698_, v_inst_3699_, v_inst_3700_, v_inst_3701_, v_inst_3702_, v_inst_3703_, v_inst_3704_, v_f_3705_);
lean_dec_ref(v_inst_3704_);
lean_dec_ref(v_inst_3700_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3707_, lean_object* v_snd_3708_, lean_object* v___x_3709_, lean_object* v_toPure_3710_, lean_object* v_inst_3711_, lean_object* v_toBind_3712_, lean_object* v_inst_3713_, lean_object* v_inst_3714_, lean_object* v_toMonadRef_3715_, lean_object* v_inst_3716_, lean_object* v_inst_3717_, lean_object* v___f_3718_, lean_object* v_newHyp_3719_){
_start:
{
lean_object* v_type_3720_; lean_object* v_value_3721_; uint8_t v___x_3722_; 
v_type_3720_ = lean_ctor_get(v_newHyp_3719_, 1);
v_value_3721_ = lean_ctor_get(v_newHyp_3719_, 2);
lean_inc_ref(v_type_3720_);
v___x_3722_ = l_Lean_Expr_isFalse(v_type_3720_);
if (v___x_3722_ == 0)
{
lean_object* v_type_3723_; lean_object* v___f_3724_; lean_object* v___f_3725_; lean_object* v___f_3726_; lean_object* v___f_3727_; uint8_t v___x_3735_; 
lean_dec(v___f_3718_);
v_type_3723_ = lean_ctor_get(v___x_3707_, 1);
lean_inc(v_toPure_3710_);
lean_inc(v___x_3709_);
lean_inc_ref(v_newHyp_3719_);
lean_inc(v_snd_3708_);
v___f_3724_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3724_, 0, v_snd_3708_);
lean_closure_set(v___f_3724_, 1, v_newHyp_3719_);
lean_closure_set(v___f_3724_, 2, v___x_3709_);
lean_closure_set(v___f_3724_, 3, v_toPure_3710_);
v___f_3725_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3725_, 0, v___f_3724_);
lean_inc(v_toBind_3712_);
v___f_3726_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3726_, 0, v_inst_3711_);
lean_closure_set(v___f_3726_, 1, v_toBind_3712_);
lean_closure_set(v___f_3726_, 2, v___f_3725_);
lean_inc_ref(v___f_3726_);
v___f_3727_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3727_, 0, v___f_3726_);
v___x_3735_ = lean_expr_eqv(v_type_3723_, v_type_3720_);
if (v___x_3735_ == 0)
{
lean_inc_ref(v_type_3720_);
lean_dec_ref(v_newHyp_3719_);
lean_dec(v___x_3709_);
lean_dec(v_snd_3708_);
goto v___jp_3728_;
}
else
{
if (v___x_3722_ == 0)
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_dec_ref(v___f_3727_);
lean_dec_ref(v___f_3726_);
lean_dec(v_inst_3717_);
lean_dec(v_inst_3716_);
lean_dec_ref(v_toMonadRef_3715_);
lean_dec_ref(v_inst_3714_);
lean_dec_ref(v_inst_3713_);
lean_dec(v_toBind_3712_);
lean_dec_ref(v___x_3707_);
v___x_3736_ = lean_box(0);
v___x_3737_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3708_, v_newHyp_3719_, v___x_3709_, v_toPure_3710_, v___x_3736_);
return v___x_3737_;
}
else
{
lean_inc_ref(v_type_3720_);
lean_dec_ref(v_newHyp_3719_);
lean_dec(v___x_3709_);
lean_dec(v_snd_3708_);
goto v___jp_3728_;
}
}
v___jp_3728_:
{
lean_object* v_getInheritedTraceOptions_3729_; lean_object* v___x_3730_; lean_object* v___f_3731_; lean_object* v___f_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_getInheritedTraceOptions_3729_ = lean_ctor_get(v_inst_3713_, 2);
lean_inc(v_getInheritedTraceOptions_3729_);
v___x_3730_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3712_, 3);
v___f_3731_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3731_, 0, v___f_3726_);
lean_closure_set(v___f_3731_, 1, v___x_3707_);
lean_closure_set(v___f_3731_, 2, v_type_3720_);
lean_closure_set(v___f_3731_, 3, v_inst_3714_);
lean_closure_set(v___f_3731_, 4, v_inst_3713_);
lean_closure_set(v___f_3731_, 5, v_toMonadRef_3715_);
lean_closure_set(v___f_3731_, 6, v_inst_3716_);
lean_closure_set(v___f_3731_, 7, v___x_3730_);
lean_closure_set(v___f_3731_, 8, v_toBind_3712_);
lean_closure_set(v___f_3731_, 9, v___f_3727_);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3732_, 0, v_toPure_3710_);
lean_closure_set(v___f_3732_, 1, v___x_3730_);
lean_closure_set(v___f_3732_, 2, v_toBind_3712_);
lean_closure_set(v___f_3732_, 3, v_inst_3717_);
v___x_3733_ = lean_apply_4(v_toBind_3712_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3729_, v___f_3732_);
v___x_3734_ = lean_apply_4(v_toBind_3712_, lean_box(0), lean_box(0), v___x_3733_, v___f_3731_);
return v___x_3734_;
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_inc_ref(v_value_3721_);
lean_dec_ref(v_newHyp_3719_);
lean_dec(v_inst_3717_);
lean_dec(v_inst_3716_);
lean_dec_ref(v_toMonadRef_3715_);
lean_dec_ref(v_inst_3714_);
lean_dec_ref(v_inst_3713_);
lean_dec(v_toPure_3710_);
lean_dec(v___x_3709_);
lean_dec(v_snd_3708_);
lean_dec_ref(v___x_3707_);
v___x_3738_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3738_, 0, v_value_3721_);
v___x_3739_ = lean_apply_2(v_inst_3711_, lean_box(0), v___x_3738_);
v___x_3740_ = lean_apply_4(v_toBind_3712_, lean_box(0), lean_box(0), v___x_3739_, v___f_3718_);
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3741_, lean_object* v_toPure_3742_, lean_object* v_hyps_3743_, lean_object* v___x_3744_, lean_object* v_inst_3745_, lean_object* v_toBind_3746_, lean_object* v_inst_3747_, lean_object* v_inst_3748_, lean_object* v_toMonadRef_3749_, lean_object* v_inst_3750_, lean_object* v_inst_3751_, lean_object* v_f_3752_, lean_object* v___f_3753_, lean_object* v_next_3754_, lean_object* v_acc_3755_, lean_object* v_h_3756_, lean_object* v_G_3757_){
_start:
{
uint8_t v___x_3758_; 
v___x_3758_ = lean_nat_dec_lt(v_next_3754_, v___x_3741_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; 
lean_dec(v_G_3757_);
lean_dec(v_next_3754_);
lean_dec(v___f_3753_);
lean_dec(v_f_3752_);
lean_dec(v_inst_3751_);
lean_dec(v_inst_3750_);
lean_dec_ref(v_toMonadRef_3749_);
lean_dec_ref(v_inst_3748_);
lean_dec_ref(v_inst_3747_);
lean_dec(v_toBind_3746_);
lean_dec(v_inst_3745_);
lean_dec(v___x_3744_);
v___x_3759_ = lean_apply_2(v_toPure_3742_, lean_box(0), v_acc_3755_);
return v___x_3759_;
}
else
{
lean_object* v_snd_3760_; lean_object* v___f_3761_; lean_object* v___x_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; lean_object* v___f_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v_snd_3760_ = lean_ctor_get(v_acc_3755_, 1);
lean_inc_n(v_snd_3760_, 2);
lean_dec_ref(v_acc_3755_);
lean_inc(v_next_3754_);
lean_inc_n(v_toPure_3742_, 2);
v___f_3761_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3761_, 0, v_toPure_3742_);
lean_closure_set(v___f_3761_, 1, v_next_3754_);
lean_closure_set(v___f_3761_, 2, v_G_3757_);
v___x_3762_ = lean_box(v___x_3758_);
v___f_3763_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3763_, 0, v___x_3762_);
lean_closure_set(v___f_3763_, 1, v_snd_3760_);
lean_closure_set(v___f_3763_, 2, v_toPure_3742_);
v___x_3764_ = lean_array_fget_borrowed(v_hyps_3743_, v_next_3754_);
lean_dec(v_next_3754_);
lean_inc_n(v_toBind_3746_, 3);
lean_inc_n(v___x_3764_, 2);
v___f_3765_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3765_, 0, v___x_3764_);
lean_closure_set(v___f_3765_, 1, v_snd_3760_);
lean_closure_set(v___f_3765_, 2, v___x_3744_);
lean_closure_set(v___f_3765_, 3, v_toPure_3742_);
lean_closure_set(v___f_3765_, 4, v_inst_3745_);
lean_closure_set(v___f_3765_, 5, v_toBind_3746_);
lean_closure_set(v___f_3765_, 6, v_inst_3747_);
lean_closure_set(v___f_3765_, 7, v_inst_3748_);
lean_closure_set(v___f_3765_, 8, v_toMonadRef_3749_);
lean_closure_set(v___f_3765_, 9, v_inst_3750_);
lean_closure_set(v___f_3765_, 10, v_inst_3751_);
lean_closure_set(v___f_3765_, 11, v___f_3763_);
v___x_3766_ = lean_apply_1(v_f_3752_, v___x_3764_);
v___x_3767_ = lean_apply_4(v_toBind_3746_, lean_box(0), lean_box(0), v___x_3766_, v___f_3765_);
v___x_3768_ = lean_apply_4(v_toBind_3746_, lean_box(0), lean_box(0), v___x_3767_, v___f_3753_);
v___x_3769_ = lean_apply_4(v_toBind_3746_, lean_box(0), lean_box(0), v___x_3768_, v___f_3761_);
return v___x_3769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3770_ = _args[0];
lean_object* v_toPure_3771_ = _args[1];
lean_object* v_hyps_3772_ = _args[2];
lean_object* v___x_3773_ = _args[3];
lean_object* v_inst_3774_ = _args[4];
lean_object* v_toBind_3775_ = _args[5];
lean_object* v_inst_3776_ = _args[6];
lean_object* v_inst_3777_ = _args[7];
lean_object* v_toMonadRef_3778_ = _args[8];
lean_object* v_inst_3779_ = _args[9];
lean_object* v_inst_3780_ = _args[10];
lean_object* v_f_3781_ = _args[11];
lean_object* v___f_3782_ = _args[12];
lean_object* v_next_3783_ = _args[13];
lean_object* v_acc_3784_ = _args[14];
lean_object* v_h_3785_ = _args[15];
lean_object* v_G_3786_ = _args[16];
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3770_, v_toPure_3771_, v_hyps_3772_, v___x_3773_, v_inst_3774_, v_toBind_3775_, v_inst_3776_, v_inst_3777_, v_toMonadRef_3778_, v_inst_3779_, v_inst_3780_, v_f_3781_, v___f_3782_, v_next_3783_, v_acc_3784_, v_h_3785_, v_G_3786_);
lean_dec_ref(v_hyps_3772_);
lean_dec(v___x_3770_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3788_, lean_object* v_inst_3789_, lean_object* v_toBind_3790_, lean_object* v_inst_3791_, lean_object* v_inst_3792_, lean_object* v_toMonadRef_3793_, lean_object* v_inst_3794_, lean_object* v_inst_3795_, lean_object* v_f_3796_, lean_object* v___f_3797_, lean_object* v___f_3798_, lean_object* v_hyps_3799_){
_start:
{
lean_object* v___x_3800_; lean_object* v_newHyps_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___f_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3800_ = lean_array_get_size(v_hyps_3799_);
v_newHyps_3801_ = lean_mk_empty_array_with_capacity(v___x_3800_);
v___x_3802_ = lean_unsigned_to_nat(0u);
v___x_3803_ = lean_box(0);
lean_inc(v_toBind_3790_);
v___f_3804_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3804_, 0, v___x_3800_);
lean_closure_set(v___f_3804_, 1, v_toPure_3788_);
lean_closure_set(v___f_3804_, 2, v_hyps_3799_);
lean_closure_set(v___f_3804_, 3, v___x_3803_);
lean_closure_set(v___f_3804_, 4, v_inst_3789_);
lean_closure_set(v___f_3804_, 5, v_toBind_3790_);
lean_closure_set(v___f_3804_, 6, v_inst_3791_);
lean_closure_set(v___f_3804_, 7, v_inst_3792_);
lean_closure_set(v___f_3804_, 8, v_toMonadRef_3793_);
lean_closure_set(v___f_3804_, 9, v_inst_3794_);
lean_closure_set(v___f_3804_, 10, v_inst_3795_);
lean_closure_set(v___f_3804_, 11, v_f_3796_);
lean_closure_set(v___f_3804_, 12, v___f_3797_);
v___x_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v_newHyps_3801_);
v___x_3806_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3804_, v___x_3802_, v___x_3805_, lean_box(0));
v___x_3807_ = lean_apply_4(v_toBind_3790_, lean_box(0), lean_box(0), v___x_3806_, v___f_3798_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3808_, lean_object* v_inst_3809_, lean_object* v_inst_3810_, lean_object* v_inst_3811_, lean_object* v_inst_3812_, lean_object* v_inst_3813_, lean_object* v_f_3814_){
_start:
{
lean_object* v_toApplicative_3815_; lean_object* v_toBind_3816_; lean_object* v_toPure_3817_; lean_object* v_toMonadRef_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___f_3821_; lean_object* v___f_3822_; lean_object* v___f_3823_; lean_object* v___f_3824_; lean_object* v___x_3825_; 
v_toApplicative_3815_ = lean_ctor_get(v_inst_3808_, 0);
v_toBind_3816_ = lean_ctor_get(v_inst_3808_, 1);
lean_inc_n(v_toBind_3816_, 3);
v_toPure_3817_ = lean_ctor_get(v_toApplicative_3815_, 1);
lean_inc_n(v_toPure_3817_, 4);
v_toMonadRef_3818_ = lean_ctor_get(v_inst_3810_, 1);
lean_inc_ref(v_toMonadRef_3818_);
lean_dec_ref(v_inst_3810_);
v___x_3819_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3809_, 2);
v___x_3820_ = lean_apply_2(v_inst_3809_, lean_box(0), v___x_3819_);
v___f_3821_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3821_, 0, v_toPure_3817_);
v___f_3822_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3822_, 0, v_inst_3809_);
lean_closure_set(v___f_3822_, 1, v_toBind_3816_);
lean_closure_set(v___f_3822_, 2, v___f_3821_);
lean_closure_set(v___f_3822_, 3, v_toPure_3817_);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3823_, 0, v_toPure_3817_);
v___f_3824_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3824_, 0, v_toPure_3817_);
lean_closure_set(v___f_3824_, 1, v_inst_3809_);
lean_closure_set(v___f_3824_, 2, v_toBind_3816_);
lean_closure_set(v___f_3824_, 3, v_inst_3811_);
lean_closure_set(v___f_3824_, 4, v_inst_3808_);
lean_closure_set(v___f_3824_, 5, v_toMonadRef_3818_);
lean_closure_set(v___f_3824_, 6, v_inst_3813_);
lean_closure_set(v___f_3824_, 7, v_inst_3812_);
lean_closure_set(v___f_3824_, 8, v_f_3814_);
lean_closure_set(v___f_3824_, 9, v___f_3823_);
lean_closure_set(v___f_3824_, 10, v___f_3822_);
v___x_3825_ = lean_apply_4(v_toBind_3816_, lean_box(0), lean_box(0), v___x_3820_, v___f_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3826_, lean_object* v_inst_3827_, lean_object* v_inst_3828_, lean_object* v_inst_3829_, lean_object* v_inst_3830_, lean_object* v_inst_3831_, lean_object* v_inst_3832_, lean_object* v_inst_3833_, lean_object* v_inst_3834_, lean_object* v_f_3835_){
_start:
{
lean_object* v_toApplicative_3836_; lean_object* v_toBind_3837_; lean_object* v_toPure_3838_; lean_object* v_toMonadRef_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___f_3842_; lean_object* v___f_3843_; lean_object* v___f_3844_; lean_object* v___f_3845_; lean_object* v___x_3846_; 
v_toApplicative_3836_ = lean_ctor_get(v_inst_3827_, 0);
v_toBind_3837_ = lean_ctor_get(v_inst_3827_, 1);
lean_inc_n(v_toBind_3837_, 3);
v_toPure_3838_ = lean_ctor_get(v_toApplicative_3836_, 1);
lean_inc_n(v_toPure_3838_, 4);
v_toMonadRef_3839_ = lean_ctor_get(v_inst_3829_, 1);
lean_inc_ref(v_toMonadRef_3839_);
lean_dec_ref(v_inst_3829_);
v___x_3840_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3828_, 2);
v___x_3841_ = lean_apply_2(v_inst_3828_, lean_box(0), v___x_3840_);
v___f_3842_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3842_, 0, v_toPure_3838_);
v___f_3843_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3843_, 0, v_inst_3828_);
lean_closure_set(v___f_3843_, 1, v_toBind_3837_);
lean_closure_set(v___f_3843_, 2, v___f_3842_);
lean_closure_set(v___f_3843_, 3, v_toPure_3838_);
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3844_, 0, v_toPure_3838_);
v___f_3845_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3845_, 0, v_toPure_3838_);
lean_closure_set(v___f_3845_, 1, v_inst_3828_);
lean_closure_set(v___f_3845_, 2, v_toBind_3837_);
lean_closure_set(v___f_3845_, 3, v_inst_3831_);
lean_closure_set(v___f_3845_, 4, v_inst_3827_);
lean_closure_set(v___f_3845_, 5, v_toMonadRef_3839_);
lean_closure_set(v___f_3845_, 6, v_inst_3833_);
lean_closure_set(v___f_3845_, 7, v_inst_3832_);
lean_closure_set(v___f_3845_, 8, v_f_3835_);
lean_closure_set(v___f_3845_, 9, v___f_3844_);
lean_closure_set(v___f_3845_, 10, v___f_3843_);
v___x_3846_ = lean_apply_4(v_toBind_3837_, lean_box(0), lean_box(0), v___x_3841_, v___f_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3847_, lean_object* v_inst_3848_, lean_object* v_inst_3849_, lean_object* v_inst_3850_, lean_object* v_inst_3851_, lean_object* v_inst_3852_, lean_object* v_inst_3853_, lean_object* v_inst_3854_, lean_object* v_inst_3855_, lean_object* v_f_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3847_, v_inst_3848_, v_inst_3849_, v_inst_3850_, v_inst_3851_, v_inst_3852_, v_inst_3853_, v_inst_3854_, v_inst_3855_, v_f_3856_);
lean_dec_ref(v_inst_3855_);
lean_dec_ref(v_inst_3851_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3858_, lean_object* v_x_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_apply_1(v_f_3858_, v___y_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3862_, lean_object* v_inst_3863_, lean_object* v___f_3864_, lean_object* v_hyps_3865_){
_start:
{
lean_object* v_toPure_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v_toPure_3866_ = lean_ctor_get(v_toApplicative_3862_, 1);
lean_inc(v_toPure_3866_);
lean_dec_ref(v_toApplicative_3862_);
v___x_3867_ = lean_unsigned_to_nat(0u);
v___x_3868_ = lean_array_get_size(v_hyps_3865_);
v___x_3869_ = lean_box(0);
v___x_3870_ = lean_nat_dec_lt(v___x_3867_, v___x_3868_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
lean_dec_ref(v_hyps_3865_);
lean_dec(v___f_3864_);
lean_dec_ref(v_inst_3863_);
v___x_3871_ = lean_apply_2(v_toPure_3866_, lean_box(0), v___x_3869_);
return v___x_3871_;
}
else
{
uint8_t v___x_3872_; 
v___x_3872_ = lean_nat_dec_le(v___x_3868_, v___x_3868_);
if (v___x_3872_ == 0)
{
if (v___x_3870_ == 0)
{
lean_object* v___x_3873_; 
lean_dec_ref(v_hyps_3865_);
lean_dec(v___f_3864_);
lean_dec_ref(v_inst_3863_);
v___x_3873_ = lean_apply_2(v_toPure_3866_, lean_box(0), v___x_3869_);
return v___x_3873_;
}
else
{
size_t v___x_3874_; size_t v___x_3875_; lean_object* v___x_3876_; 
lean_dec(v_toPure_3866_);
v___x_3874_ = ((size_t)0ULL);
v___x_3875_ = lean_usize_of_nat(v___x_3868_);
v___x_3876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3863_, v___f_3864_, v_hyps_3865_, v___x_3874_, v___x_3875_, v___x_3869_);
return v___x_3876_;
}
}
else
{
size_t v___x_3877_; size_t v___x_3878_; lean_object* v___x_3879_; 
lean_dec(v_toPure_3866_);
v___x_3877_ = ((size_t)0ULL);
v___x_3878_ = lean_usize_of_nat(v___x_3868_);
v___x_3879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3863_, v___f_3864_, v_hyps_3865_, v___x_3877_, v___x_3878_, v___x_3869_);
return v___x_3879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3880_, lean_object* v_inst_3881_, lean_object* v_f_3882_){
_start:
{
lean_object* v_toApplicative_3883_; lean_object* v_toBind_3884_; lean_object* v___f_3885_; lean_object* v___f_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_toApplicative_3883_ = lean_ctor_get(v_inst_3880_, 0);
lean_inc_ref(v_toApplicative_3883_);
v_toBind_3884_ = lean_ctor_get(v_inst_3880_, 1);
lean_inc(v_toBind_3884_);
v___f_3885_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3885_, 0, v_f_3882_);
v___f_3886_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3886_, 0, v_toApplicative_3883_);
lean_closure_set(v___f_3886_, 1, v_inst_3880_);
lean_closure_set(v___f_3886_, 2, v___f_3885_);
v___x_3887_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3888_ = lean_apply_2(v_inst_3881_, lean_box(0), v___x_3887_);
v___x_3889_ = lean_apply_4(v_toBind_3884_, lean_box(0), lean_box(0), v___x_3888_, v___f_3886_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3890_, lean_object* v_inst_3891_, lean_object* v_inst_3892_, lean_object* v_inst_3893_, lean_object* v_f_3894_){
_start:
{
lean_object* v_toApplicative_3895_; lean_object* v_toBind_3896_; lean_object* v___f_3897_; lean_object* v___f_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_toApplicative_3895_ = lean_ctor_get(v_inst_3891_, 0);
lean_inc_ref(v_toApplicative_3895_);
v_toBind_3896_ = lean_ctor_get(v_inst_3891_, 1);
lean_inc(v_toBind_3896_);
v___f_3897_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3897_, 0, v_f_3894_);
v___f_3898_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3898_, 0, v_toApplicative_3895_);
lean_closure_set(v___f_3898_, 1, v_inst_3891_);
lean_closure_set(v___f_3898_, 2, v___f_3897_);
v___x_3899_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3900_ = lean_apply_2(v_inst_3892_, lean_box(0), v___x_3899_);
v___x_3901_ = lean_apply_4(v_toBind_3896_, lean_box(0), lean_box(0), v___x_3900_, v___f_3898_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3902_, lean_object* v_inst_3903_, lean_object* v_inst_3904_, lean_object* v_inst_3905_, lean_object* v_f_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3902_, v_inst_3903_, v_inst_3904_, v_inst_3905_, v_f_3906_);
lean_dec_ref(v_inst_3905_);
return v_res_3907_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3908_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_3911_, lean_object* v_methods_3912_, lean_object* v_config_3913_, lean_object* v_hyp_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_){
_start:
{
lean_object* v___x_3923_; lean_object* v_caches_3924_; lean_object* v___x_3925_; lean_object* v_typeAnalysis_3926_; lean_object* v_target_3927_; lean_object* v_hypotheses_3928_; uint8_t v_didChange_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3975_; 
v___x_3923_ = lean_st_ref_get(v_a_3915_);
v_caches_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc_ref(v_caches_3924_);
lean_dec(v___x_3923_);
v___x_3925_ = lean_st_ref_take(v_a_3915_);
v_typeAnalysis_3926_ = lean_ctor_get(v___x_3925_, 1);
v_target_3927_ = lean_ctor_get(v___x_3925_, 2);
v_hypotheses_3928_ = lean_ctor_get(v___x_3925_, 3);
v_didChange_3929_ = lean_ctor_get_uint8(v___x_3925_, sizeof(void*)*4);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; 
v_unused_3976_ = lean_ctor_get(v___x_3925_, 0);
lean_dec(v_unused_3976_);
v___x_3931_ = v___x_3925_;
v_isShared_3932_ = v_isSharedCheck_3975_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_hypotheses_3928_);
lean_inc(v_target_3927_);
lean_inc(v_typeAnalysis_3926_);
lean_dec(v___x_3925_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3975_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3933_ = lean_unsigned_to_nat(0u);
v___x_3934_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_3911_, v_caches_3924_);
v___x_3935_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_3936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3933_);
lean_ctor_set(v___x_3936_, 1, v___x_3934_);
lean_ctor_set(v___x_3936_, 2, v___x_3935_);
lean_ctor_set(v___x_3936_, 3, v___x_3935_);
v___x_3937_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3911_, v___x_3935_, v_caches_3924_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3937_);
v___x_3939_ = v___x_3931_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_typeAnalysis_3926_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_target_3927_);
lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_hypotheses_3928_);
lean_ctor_set_uint8(v_reuseFailAlloc_3974_, sizeof(void*)*4, v_didChange_3929_);
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
v___x_3943_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3942_, v_methods_3912_, v_config_3913_, v___x_3936_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v_fst_3945_; lean_object* v_snd_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v_caches_3949_; lean_object* v_persistentCache_3950_; lean_object* v_typeAnalysis_3951_; lean_object* v_target_3952_; lean_object* v_hypotheses_3953_; uint8_t v_didChange_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3964_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v_fst_3945_ = lean_ctor_get(v_a_3944_, 0);
lean_inc(v_fst_3945_);
v_snd_3946_ = lean_ctor_get(v_a_3944_, 1);
lean_inc(v_snd_3946_);
lean_dec(v_a_3944_);
v___x_3947_ = lean_st_ref_get(v_a_3915_);
v___x_3948_ = lean_st_ref_take(v_a_3915_);
v_caches_3949_ = lean_ctor_get(v___x_3947_, 0);
lean_inc_ref(v_caches_3949_);
lean_dec(v___x_3947_);
v_persistentCache_3950_ = lean_ctor_get(v_snd_3946_, 1);
lean_inc_ref(v_persistentCache_3950_);
lean_dec(v_snd_3946_);
v_typeAnalysis_3951_ = lean_ctor_get(v___x_3948_, 1);
v_target_3952_ = lean_ctor_get(v___x_3948_, 2);
v_hypotheses_3953_ = lean_ctor_get(v___x_3948_, 3);
v_didChange_3954_ = lean_ctor_get_uint8(v___x_3948_, sizeof(void*)*4);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; 
v_unused_3965_ = lean_ctor_get(v___x_3948_, 0);
lean_dec(v_unused_3965_);
v___x_3956_ = v___x_3948_;
v_isShared_3957_ = v_isSharedCheck_3964_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_hypotheses_3953_);
lean_inc(v_target_3952_);
lean_inc(v_typeAnalysis_3951_);
lean_dec(v___x_3948_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3964_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3958_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3911_, v_persistentCache_3950_, v_caches_3949_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v___x_3958_);
v___x_3960_ = v___x_3956_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_typeAnalysis_3951_);
lean_ctor_set(v_reuseFailAlloc_3963_, 2, v_target_3952_);
lean_ctor_set(v_reuseFailAlloc_3963_, 3, v_hypotheses_3953_);
lean_ctor_set_uint8(v_reuseFailAlloc_3963_, sizeof(void*)*4, v_didChange_3954_);
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
lean_object* v___x_4038_; lean_object* v_caches_4039_; lean_object* v___x_4040_; lean_object* v_typeAnalysis_4041_; lean_object* v_target_4042_; lean_object* v_hypotheses_4043_; uint8_t v_didChange_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4090_; 
v___x_4038_ = lean_st_ref_get(v_a_4030_);
v_caches_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc_ref(v_caches_4039_);
lean_dec(v___x_4038_);
v___x_4040_ = lean_st_ref_take(v_a_4030_);
v_typeAnalysis_4041_ = lean_ctor_get(v___x_4040_, 1);
v_target_4042_ = lean_ctor_get(v___x_4040_, 2);
v_hypotheses_4043_ = lean_ctor_get(v___x_4040_, 3);
v_didChange_4044_ = lean_ctor_get_uint8(v___x_4040_, sizeof(void*)*4);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v___x_4040_, 0);
lean_dec(v_unused_4091_);
v___x_4046_ = v___x_4040_;
v_isShared_4047_ = v_isSharedCheck_4090_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_hypotheses_4043_);
lean_inc(v_target_4042_);
lean_inc(v_typeAnalysis_4041_);
lean_dec(v___x_4040_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4090_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
v___x_4048_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4026_, v_caches_4039_);
v___x_4049_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4050_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4026_, v___x_4049_, v_caches_4039_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 0, v___x_4050_);
v___x_4052_ = v___x_4046_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_typeAnalysis_4041_);
lean_ctor_set(v_reuseFailAlloc_4089_, 2, v_target_4042_);
lean_ctor_set(v_reuseFailAlloc_4089_, 3, v_hypotheses_4043_);
lean_ctor_set_uint8(v_reuseFailAlloc_4089_, sizeof(void*)*4, v_didChange_4044_);
v___x_4052_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; lean_object* v_type_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4053_ = lean_st_ref_put(v_a_4030_, v___x_4052_);
v_type_4054_ = lean_ctor_get(v_hyp_4029_, 1);
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
lean_ctor_set(v___x_4056_, 1, v___x_4048_);
lean_inc_ref(v_type_4054_);
v___x_4057_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4057_, 0, v_type_4054_);
v___x_4058_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4057_, v_methods_4027_, v_config_4028_, v___x_4056_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v_fst_4060_; lean_object* v_snd_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v_caches_4064_; lean_object* v_cache_4065_; lean_object* v_typeAnalysis_4066_; lean_object* v_target_4067_; lean_object* v_hypotheses_4068_; uint8_t v_didChange_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4079_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v_fst_4060_ = lean_ctor_get(v_a_4059_, 0);
lean_inc(v_fst_4060_);
v_snd_4061_ = lean_ctor_get(v_a_4059_, 1);
lean_inc(v_snd_4061_);
lean_dec(v_a_4059_);
v___x_4062_ = lean_st_ref_get(v_a_4030_);
v___x_4063_ = lean_st_ref_take(v_a_4030_);
v_caches_4064_ = lean_ctor_get(v___x_4062_, 0);
lean_inc_ref(v_caches_4064_);
lean_dec(v___x_4062_);
v_cache_4065_ = lean_ctor_get(v_snd_4061_, 1);
lean_inc_ref(v_cache_4065_);
lean_dec(v_snd_4061_);
v_typeAnalysis_4066_ = lean_ctor_get(v___x_4063_, 1);
v_target_4067_ = lean_ctor_get(v___x_4063_, 2);
v_hypotheses_4068_ = lean_ctor_get(v___x_4063_, 3);
v_didChange_4069_ = lean_ctor_get_uint8(v___x_4063_, sizeof(void*)*4);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4079_ == 0)
{
lean_object* v_unused_4080_; 
v_unused_4080_ = lean_ctor_get(v___x_4063_, 0);
lean_dec(v_unused_4080_);
v___x_4071_ = v___x_4063_;
v_isShared_4072_ = v_isSharedCheck_4079_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_hypotheses_4068_);
lean_inc(v_target_4067_);
lean_inc(v_typeAnalysis_4066_);
lean_dec(v___x_4063_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4079_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4073_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4026_, v_cache_4065_, v_caches_4064_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 0, v___x_4073_);
v___x_4075_ = v___x_4071_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v_typeAnalysis_4066_);
lean_ctor_set(v_reuseFailAlloc_4078_, 2, v_target_4067_);
lean_ctor_set(v_reuseFailAlloc_4078_, 3, v_hypotheses_4068_);
lean_ctor_set_uint8(v_reuseFailAlloc_4078_, sizeof(void*)*4, v_didChange_4069_);
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
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_caches_4194_);
lean_ctor_set(v_reuseFailAlloc_4206_, 1, v_typeAnalysis_4195_);
lean_ctor_set(v_reuseFailAlloc_4206_, 2, v_target_4196_);
lean_ctor_set(v_reuseFailAlloc_4206_, 3, v_hypotheses_4197_);
v___x_4202_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_ctor_set_uint8(v___x_4202_, sizeof(void*)*4, v___x_4178_);
v___x_4203_ = lean_st_ref_put(v___y_4182_, v___x_4202_);
v___x_4204_ = lean_box(0);
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
v___x_4205_ = lean_apply_13(v___f_4179_, v___x_4204_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, lean_box(0));
return v___x_4205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4208_, lean_object* v___f_4209_, lean_object* v_____r_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
uint8_t v___x_22107__boxed_4223_; lean_object* v_res_4224_; 
v___x_22107__boxed_4223_ = lean_unbox(v___x_4208_);
v_res_4224_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22107__boxed_4223_, v___f_4209_, v_____r_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
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
lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = lean_array_fget_borrowed(v_hypotheses_4226_, v_next_4235_);
lean_inc(v___x_4276_);
v___x_4277_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4227_, v_methods_4228_, v_config_4229_, v___x_4276_, v___y_4240_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v_snd_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4341_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
v_snd_4279_ = lean_ctor_get(v_acc_4236_, 1);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_acc_4236_);
if (v_isSharedCheck_4341_ == 0)
{
lean_object* v_unused_4342_; 
v_unused_4342_ = lean_ctor_get(v_acc_4236_, 0);
lean_dec(v_unused_4342_);
v___x_4281_ = v_acc_4236_;
v_isShared_4282_ = v_isSharedCheck_4341_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_snd_4279_);
lean_dec(v_acc_4236_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4341_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v_type_4283_; lean_object* v_value_4284_; uint8_t v___x_4285_; 
v_type_4283_ = lean_ctor_get(v_a_4278_, 1);
v_value_4284_ = lean_ctor_get(v_a_4278_, 2);
lean_inc_ref(v_type_4283_);
v___x_4285_ = l_Lean_Expr_isFalse(v_type_4283_);
if (v___x_4285_ == 0)
{
lean_object* v_type_4286_; lean_object* v___f_4287_; uint8_t v___x_4316_; 
lean_del_object(v___x_4281_);
v_type_4286_ = lean_ctor_get(v___x_4276_, 1);
lean_inc(v___x_4230_);
lean_inc(v_a_4278_);
lean_inc(v_snd_4279_);
v___f_4287_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4287_, 0, v_snd_4279_);
lean_closure_set(v___f_4287_, 1, v_a_4278_);
lean_closure_set(v___f_4287_, 2, v___x_4230_);
v___x_4316_ = lean_expr_eqv(v_type_4286_, v_type_4283_);
if (v___x_4316_ == 0)
{
lean_inc_ref(v_type_4283_);
lean_dec(v_snd_4279_);
lean_dec(v_a_4278_);
lean_dec(v___x_4230_);
goto v___jp_4291_;
}
else
{
if (v___x_4285_ == 0)
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
lean_dec_ref(v___f_4287_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
v___x_4317_ = lean_box(0);
v___x_4318_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4279_, v_a_4278_, v___x_4230_, v___x_4317_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
v___y_4252_ = v___x_4318_;
goto v___jp_4251_;
}
else
{
lean_inc_ref(v_type_4283_);
lean_dec(v_snd_4279_);
lean_dec(v_a_4278_);
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
lean_object* v_options_4292_; uint8_t v_hasTrace_4293_; 
v_options_4292_ = lean_ctor_get(v___y_4248_, 2);
v_hasTrace_4293_ = lean_ctor_get_uint8(v_options_4292_, sizeof(void*)*1);
if (v_hasTrace_4293_ == 0)
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
lean_object* v_inheritedTraceOptions_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; uint8_t v___x_4297_; 
v_inheritedTraceOptions_4294_ = lean_ctor_get(v___y_4248_, 13);
v___x_4295_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4296_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4297_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4294_, v_options_4292_, v___x_4296_);
if (v___x_4297_ == 0)
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
lean_object* v_type_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_22032__overap_4304_; lean_object* v___x_4305_; 
v_type_4298_ = lean_ctor_get(v___x_4276_, 1);
lean_inc_ref(v_type_4298_);
v___x_4299_ = l_Lean_MessageData_ofExpr(v_type_4298_);
v___x_4300_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l_Lean_MessageData_ofExpr(v_type_4283_);
v___x_4303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4301_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
v___x_22032__overap_4304_ = l_Lean_addTrace___redArg(v___x_4231_, v___x_4232_, v_toMonadRef_4233_, v___f_4234_, v___x_4295_, v___x_4303_);
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
v___x_4305_ = lean_apply_12(v___x_22032__overap_4304_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, lean_box(0));
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4307_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4305_, 1);
v___x_4307_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4274_, v___f_4287_, v_a_4306_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
v___y_4252_ = v___x_4307_;
goto v___jp_4251_;
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v___f_4287_);
lean_dec_ref(v_G_4238_);
v_a_4308_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4305_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4305_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4319_; 
lean_inc_ref(v_value_4284_);
lean_dec(v_a_4278_);
lean_dec_ref(v_G_4238_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
lean_dec(v___x_4230_);
v___x_4319_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4284_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
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
v___x_4323_ = lean_box(v___x_4274_);
v___x_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4324_);
v___x_4326_ = v___x_4281_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4324_);
lean_ctor_set(v_reuseFailAlloc_4330_, 1, v_snd_4279_);
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
lean_del_object(v___x_4281_);
lean_dec(v_snd_4279_);
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
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec_ref(v_G_4238_);
lean_dec_ref(v_acc_4236_);
lean_dec(v___f_4234_);
lean_dec_ref(v_toMonadRef_4233_);
lean_dec_ref(v___x_4232_);
lean_dec_ref(v___x_4231_);
lean_dec(v___x_4230_);
v_a_4343_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4277_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4277_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
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
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v_toMonadRef_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v_hypotheses_4445_; lean_object* v___f_4446_; lean_object* v___x_4447_; lean_object* v_newHyps_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___f_4452_; lean_object* v___x_4453_; lean_object* v___x_21814__overap_4454_; lean_object* v___x_4455_; 
v___x_4434_ = l_StateRefT_x27_instMonad___redArg(v___x_4433_);
v___x_4435_ = l_ReaderT_instMonad___redArg(v___x_4434_);
v___x_4436_ = l_StateRefT_x27_instMonad___redArg(v___x_4435_);
v___x_4437_ = l_ReaderT_instMonad___redArg(v___x_4436_);
v___x_4438_ = l_ReaderT_instMonad___redArg(v___x_4437_);
v___x_4439_ = l_StateRefT_x27_instMonad___redArg(v___x_4438_);
v___x_4440_ = l_ReaderT_instMonad___redArg(v___x_4439_);
v___x_4441_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4442_ = lean_ctor_get(v___x_4441_, 0);
v___x_4443_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4444_ = lean_st_ref_get(v_a_4383_);
v_hypotheses_4445_ = lean_ctor_get(v___x_4444_, 3);
lean_inc_ref(v_hypotheses_4445_);
lean_dec(v___x_4444_);
v___f_4446_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4447_ = lean_array_get_size(v_hypotheses_4445_);
v_newHyps_4448_ = lean_mk_empty_array_with_capacity(v___x_4447_);
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = lean_box(0);
v___x_4451_ = lean_box(v_cacheId_4379_);
lean_inc_ref(v_toMonadRef_4442_);
v___f_4452_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4452_, 0, v___x_4447_);
lean_closure_set(v___f_4452_, 1, v_hypotheses_4445_);
lean_closure_set(v___f_4452_, 2, v___x_4451_);
lean_closure_set(v___f_4452_, 3, v_methods_4380_);
lean_closure_set(v___f_4452_, 4, v_config_4381_);
lean_closure_set(v___f_4452_, 5, v___x_4450_);
lean_closure_set(v___f_4452_, 6, v___x_4440_);
lean_closure_set(v___f_4452_, 7, v___x_4443_);
lean_closure_set(v___f_4452_, 8, v_toMonadRef_4442_);
lean_closure_set(v___f_4452_, 9, v___f_4446_);
v___x_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4450_);
lean_ctor_set(v___x_4453_, 1, v_newHyps_4448_);
v___x_21814__overap_4454_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4452_, v___x_4449_, v___x_4453_, lean_box(0));
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
v___x_4455_ = lean_apply_12(v___x_21814__overap_4454_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, lean_box(0));
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
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = lean_array_fget_borrowed(v_hypotheses_4518_, v_next_4527_);
lean_inc(v___x_4568_);
v___x_4569_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4519_, v_methods_4520_, v_config_4521_, v___x_4568_, v___y_4532_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v_snd_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4633_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
lean_dec_ref_known(v___x_4569_, 1);
v_snd_4571_ = lean_ctor_get(v_acc_4528_, 1);
v_isSharedCheck_4633_ = !lean_is_exclusive(v_acc_4528_);
if (v_isSharedCheck_4633_ == 0)
{
lean_object* v_unused_4634_; 
v_unused_4634_ = lean_ctor_get(v_acc_4528_, 0);
lean_dec(v_unused_4634_);
v___x_4573_ = v_acc_4528_;
v_isShared_4574_ = v_isSharedCheck_4633_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_snd_4571_);
lean_dec(v_acc_4528_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4633_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v_type_4575_; lean_object* v_value_4576_; uint8_t v___x_4577_; 
v_type_4575_ = lean_ctor_get(v_a_4570_, 1);
v_value_4576_ = lean_ctor_get(v_a_4570_, 2);
lean_inc_ref(v_type_4575_);
v___x_4577_ = l_Lean_Expr_isFalse(v_type_4575_);
if (v___x_4577_ == 0)
{
lean_object* v_type_4578_; lean_object* v___f_4579_; uint8_t v___x_4608_; 
lean_del_object(v___x_4573_);
v_type_4578_ = lean_ctor_get(v___x_4568_, 1);
lean_inc(v___x_4522_);
lean_inc(v_a_4570_);
lean_inc(v_snd_4571_);
v___f_4579_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4579_, 0, v_snd_4571_);
lean_closure_set(v___f_4579_, 1, v_a_4570_);
lean_closure_set(v___f_4579_, 2, v___x_4522_);
v___x_4608_ = lean_expr_eqv(v_type_4578_, v_type_4575_);
if (v___x_4608_ == 0)
{
lean_inc_ref(v_type_4575_);
lean_dec(v_snd_4571_);
lean_dec(v_a_4570_);
lean_dec(v___x_4522_);
goto v___jp_4583_;
}
else
{
if (v___x_4577_ == 0)
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
lean_dec_ref(v___f_4579_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
v___x_4609_ = lean_box(0);
v___x_4610_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4571_, v_a_4570_, v___x_4522_, v___x_4609_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
v___y_4544_ = v___x_4610_;
goto v___jp_4543_;
}
else
{
lean_inc_ref(v_type_4575_);
lean_dec(v_snd_4571_);
lean_dec(v_a_4570_);
lean_dec(v___x_4522_);
goto v___jp_4583_;
}
}
v___jp_4580_:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4581_ = lean_box(0);
v___x_4582_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4566_, v___f_4579_, v___x_4581_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
v___y_4544_ = v___x_4582_;
goto v___jp_4543_;
}
v___jp_4583_:
{
lean_object* v_options_4584_; uint8_t v_hasTrace_4585_; 
v_options_4584_ = lean_ctor_get(v___y_4540_, 2);
v_hasTrace_4585_ = lean_ctor_get_uint8(v_options_4584_, sizeof(void*)*1);
if (v_hasTrace_4585_ == 0)
{
lean_dec_ref(v_type_4575_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
goto v___jp_4580_;
}
else
{
lean_object* v_inheritedTraceOptions_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; uint8_t v___x_4589_; 
v_inheritedTraceOptions_4586_ = lean_ctor_get(v___y_4540_, 13);
v___x_4587_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4588_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4589_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4586_, v_options_4584_, v___x_4588_);
if (v___x_4589_ == 0)
{
lean_dec_ref(v_type_4575_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
goto v___jp_4580_;
}
else
{
lean_object* v_type_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_22032__overap_4596_; lean_object* v___x_4597_; 
v_type_4590_ = lean_ctor_get(v___x_4568_, 1);
lean_inc_ref(v_type_4590_);
v___x_4591_ = l_Lean_MessageData_ofExpr(v_type_4590_);
v___x_4592_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = l_Lean_MessageData_ofExpr(v_type_4575_);
v___x_4595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4593_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
v___x_22032__overap_4596_ = l_Lean_addTrace___redArg(v___x_4523_, v___x_4524_, v_toMonadRef_4525_, v___f_4526_, v___x_4587_, v___x_4595_);
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
v___x_4597_ = lean_apply_12(v___x_22032__overap_4596_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, lean_box(0));
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
}
}
else
{
lean_object* v___x_4611_; 
lean_inc_ref(v_value_4576_);
lean_dec(v_a_4570_);
lean_dec_ref(v_G_4530_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec(v___x_4522_);
v___x_4611_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4576_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4623_; 
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4623_ == 0)
{
lean_object* v_unused_4624_; 
v_unused_4624_ = lean_ctor_get(v___x_4611_, 0);
lean_dec(v_unused_4624_);
v___x_4613_ = v___x_4611_;
v_isShared_4614_ = v_isSharedCheck_4623_;
goto v_resetjp_4612_;
}
else
{
lean_dec(v___x_4611_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4623_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
v___x_4615_ = lean_box(v___x_4566_);
v___x_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v___x_4616_);
v___x_4618_ = v___x_4573_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4616_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_snd_4571_);
v___x_4618_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4620_; 
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4618_);
v___x_4620_ = v___x_4613_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_del_object(v___x_4573_);
lean_dec(v_snd_4571_);
v_a_4625_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4611_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4611_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_dec_ref(v_G_4530_);
lean_dec_ref(v_acc_4528_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec(v___x_4522_);
v_a_4635_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4569_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4569_);
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
lean_object* v___x_4643_ = _args[0];
lean_object* v_hypotheses_4644_ = _args[1];
lean_object* v_cacheId_4645_ = _args[2];
lean_object* v_methods_4646_ = _args[3];
lean_object* v_config_4647_ = _args[4];
lean_object* v___x_4648_ = _args[5];
lean_object* v___x_4649_ = _args[6];
lean_object* v___x_4650_ = _args[7];
lean_object* v_toMonadRef_4651_ = _args[8];
lean_object* v___f_4652_ = _args[9];
lean_object* v_next_4653_ = _args[10];
lean_object* v_acc_4654_ = _args[11];
lean_object* v_h_4655_ = _args[12];
lean_object* v_G_4656_ = _args[13];
lean_object* v___y_4657_ = _args[14];
lean_object* v___y_4658_ = _args[15];
lean_object* v___y_4659_ = _args[16];
lean_object* v___y_4660_ = _args[17];
lean_object* v___y_4661_ = _args[18];
lean_object* v___y_4662_ = _args[19];
lean_object* v___y_4663_ = _args[20];
lean_object* v___y_4664_ = _args[21];
lean_object* v___y_4665_ = _args[22];
lean_object* v___y_4666_ = _args[23];
lean_object* v___y_4667_ = _args[24];
lean_object* v___y_4668_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4669_; lean_object* v_res_4670_; 
v_cacheId_boxed_4669_ = lean_unbox(v_cacheId_4645_);
v_res_4670_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4643_, v_hypotheses_4644_, v_cacheId_boxed_4669_, v_methods_4646_, v_config_4647_, v___x_4648_, v___x_4649_, v___x_4650_, v_toMonadRef_4651_, v___f_4652_, v_next_4653_, v_acc_4654_, v_h_4655_, v_G_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v_next_4653_);
lean_dec_ref(v_hypotheses_4644_);
lean_dec(v___x_4643_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4671_, lean_object* v_methods_4672_, lean_object* v_config_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v___x_4686_; lean_object* v_toApplicative_4687_; lean_object* v_toFunctor_4688_; lean_object* v_toSeq_4689_; lean_object* v_toSeqLeft_4690_; lean_object* v_toSeqRight_4691_; lean_object* v___f_4692_; lean_object* v___f_4693_; lean_object* v___f_4694_; lean_object* v___f_4695_; lean_object* v___x_4696_; lean_object* v___f_4697_; lean_object* v___f_4698_; lean_object* v___f_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v_toApplicative_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4790_; 
v___x_4686_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4687_ = lean_ctor_get(v___x_4686_, 0);
v_toFunctor_4688_ = lean_ctor_get(v_toApplicative_4687_, 0);
v_toSeq_4689_ = lean_ctor_get(v_toApplicative_4687_, 2);
v_toSeqLeft_4690_ = lean_ctor_get(v_toApplicative_4687_, 3);
v_toSeqRight_4691_ = lean_ctor_get(v_toApplicative_4687_, 4);
v___f_4692_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4693_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4688_, 2);
v___f_4694_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4694_, 0, v_toFunctor_4688_);
v___f_4695_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4695_, 0, v_toFunctor_4688_);
v___x_4696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4696_, 0, v___f_4694_);
lean_ctor_set(v___x_4696_, 1, v___f_4695_);
lean_inc(v_toSeqRight_4691_);
v___f_4697_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4697_, 0, v_toSeqRight_4691_);
lean_inc(v_toSeqLeft_4690_);
v___f_4698_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4698_, 0, v_toSeqLeft_4690_);
lean_inc(v_toSeq_4689_);
v___f_4699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4699_, 0, v_toSeq_4689_);
v___x_4700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4696_);
lean_ctor_set(v___x_4700_, 1, v___f_4692_);
lean_ctor_set(v___x_4700_, 2, v___f_4699_);
lean_ctor_set(v___x_4700_, 3, v___f_4698_);
lean_ctor_set(v___x_4700_, 4, v___f_4697_);
v___x_4701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4701_, 0, v___x_4700_);
lean_ctor_set(v___x_4701_, 1, v___f_4693_);
v___x_4702_ = l_StateRefT_x27_instMonad___redArg(v___x_4701_);
v_toApplicative_4703_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; 
v_unused_4791_ = lean_ctor_get(v___x_4702_, 1);
lean_dec(v_unused_4791_);
v___x_4705_ = v___x_4702_;
v_isShared_4706_ = v_isSharedCheck_4790_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_toApplicative_4703_);
lean_dec(v___x_4702_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4790_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v_toFunctor_4707_; lean_object* v_toSeq_4708_; lean_object* v_toSeqLeft_4709_; lean_object* v_toSeqRight_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4788_; 
v_toFunctor_4707_ = lean_ctor_get(v_toApplicative_4703_, 0);
v_toSeq_4708_ = lean_ctor_get(v_toApplicative_4703_, 2);
v_toSeqLeft_4709_ = lean_ctor_get(v_toApplicative_4703_, 3);
v_toSeqRight_4710_ = lean_ctor_get(v_toApplicative_4703_, 4);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_toApplicative_4703_);
if (v_isSharedCheck_4788_ == 0)
{
lean_object* v_unused_4789_; 
v_unused_4789_ = lean_ctor_get(v_toApplicative_4703_, 1);
lean_dec(v_unused_4789_);
v___x_4712_ = v_toApplicative_4703_;
v_isShared_4713_ = v_isSharedCheck_4788_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_toSeqRight_4710_);
lean_inc(v_toSeqLeft_4709_);
lean_inc(v_toSeq_4708_);
lean_inc(v_toFunctor_4707_);
lean_dec(v_toApplicative_4703_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4788_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___f_4714_; lean_object* v___f_4715_; lean_object* v___f_4716_; lean_object* v___f_4717_; lean_object* v___x_4718_; lean_object* v___f_4719_; lean_object* v___f_4720_; lean_object* v___f_4721_; lean_object* v___x_4723_; 
v___f_4714_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4715_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4707_);
v___f_4716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4716_, 0, v_toFunctor_4707_);
v___f_4717_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4717_, 0, v_toFunctor_4707_);
v___x_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4718_, 0, v___f_4716_);
lean_ctor_set(v___x_4718_, 1, v___f_4717_);
v___f_4719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4719_, 0, v_toSeqRight_4710_);
v___f_4720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4720_, 0, v_toSeqLeft_4709_);
v___f_4721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4721_, 0, v_toSeq_4708_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 4, v___f_4719_);
lean_ctor_set(v___x_4712_, 3, v___f_4720_);
lean_ctor_set(v___x_4712_, 2, v___f_4721_);
lean_ctor_set(v___x_4712_, 1, v___f_4714_);
lean_ctor_set(v___x_4712_, 0, v___x_4718_);
v___x_4723_ = v___x_4712_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v___f_4714_);
lean_ctor_set(v_reuseFailAlloc_4787_, 2, v___f_4721_);
lean_ctor_set(v_reuseFailAlloc_4787_, 3, v___f_4720_);
lean_ctor_set(v_reuseFailAlloc_4787_, 4, v___f_4719_);
v___x_4723_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4725_; 
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 1, v___f_4715_);
lean_ctor_set(v___x_4705_, 0, v___x_4723_);
v___x_4725_ = v___x_4705_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v___f_4715_);
v___x_4725_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v_toMonadRef_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v_hypotheses_4737_; lean_object* v___f_4738_; lean_object* v___x_4739_; lean_object* v_newHyps_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___f_4744_; lean_object* v___x_4745_; lean_object* v___x_21814__overap_4746_; lean_object* v___x_4747_; 
v___x_4726_ = l_StateRefT_x27_instMonad___redArg(v___x_4725_);
v___x_4727_ = l_ReaderT_instMonad___redArg(v___x_4726_);
v___x_4728_ = l_StateRefT_x27_instMonad___redArg(v___x_4727_);
v___x_4729_ = l_ReaderT_instMonad___redArg(v___x_4728_);
v___x_4730_ = l_ReaderT_instMonad___redArg(v___x_4729_);
v___x_4731_ = l_StateRefT_x27_instMonad___redArg(v___x_4730_);
v___x_4732_ = l_ReaderT_instMonad___redArg(v___x_4731_);
v___x_4733_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4734_ = lean_ctor_get(v___x_4733_, 0);
v___x_4735_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4736_ = lean_st_ref_get(v_a_4675_);
v_hypotheses_4737_ = lean_ctor_get(v___x_4736_, 3);
lean_inc_ref(v_hypotheses_4737_);
lean_dec(v___x_4736_);
v___f_4738_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4739_ = lean_array_get_size(v_hypotheses_4737_);
v_newHyps_4740_ = lean_mk_empty_array_with_capacity(v___x_4739_);
v___x_4741_ = lean_unsigned_to_nat(0u);
v___x_4742_ = lean_box(0);
v___x_4743_ = lean_box(v_cacheId_4671_);
lean_inc_ref(v_toMonadRef_4734_);
v___f_4744_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4744_, 0, v___x_4739_);
lean_closure_set(v___f_4744_, 1, v_hypotheses_4737_);
lean_closure_set(v___f_4744_, 2, v___x_4743_);
lean_closure_set(v___f_4744_, 3, v_methods_4672_);
lean_closure_set(v___f_4744_, 4, v_config_4673_);
lean_closure_set(v___f_4744_, 5, v___x_4742_);
lean_closure_set(v___f_4744_, 6, v___x_4732_);
lean_closure_set(v___f_4744_, 7, v___x_4735_);
lean_closure_set(v___f_4744_, 8, v_toMonadRef_4734_);
lean_closure_set(v___f_4744_, 9, v___f_4738_);
v___x_4745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4742_);
lean_ctor_set(v___x_4745_, 1, v_newHyps_4740_);
v___x_21814__overap_4746_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4744_, v___x_4741_, v___x_4745_, lean_box(0));
lean_inc(v_a_4684_);
lean_inc_ref(v_a_4683_);
lean_inc(v_a_4682_);
lean_inc_ref(v_a_4681_);
lean_inc(v_a_4680_);
lean_inc_ref(v_a_4679_);
lean_inc(v_a_4678_);
lean_inc_ref(v_a_4677_);
lean_inc(v_a_4676_);
lean_inc(v_a_4675_);
lean_inc_ref(v_a_4674_);
v___x_4747_ = lean_apply_12(v___x_21814__overap_4746_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, lean_box(0));
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4777_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4750_ = v___x_4747_;
v_isShared_4751_ = v_isSharedCheck_4777_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4747_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4777_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v_fst_4752_; 
v_fst_4752_ = lean_ctor_get(v_a_4748_, 0);
if (lean_obj_tag(v_fst_4752_) == 0)
{
lean_object* v_snd_4753_; lean_object* v___x_4754_; lean_object* v_caches_4755_; lean_object* v_typeAnalysis_4756_; lean_object* v_target_4757_; uint8_t v_didChange_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4771_; 
v_snd_4753_ = lean_ctor_get(v_a_4748_, 1);
lean_inc(v_snd_4753_);
lean_dec(v_a_4748_);
v___x_4754_ = lean_st_ref_take(v_a_4675_);
v_caches_4755_ = lean_ctor_get(v___x_4754_, 0);
v_typeAnalysis_4756_ = lean_ctor_get(v___x_4754_, 1);
v_target_4757_ = lean_ctor_get(v___x_4754_, 2);
v_didChange_4758_ = lean_ctor_get_uint8(v___x_4754_, sizeof(void*)*4);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4771_ == 0)
{
lean_object* v_unused_4772_; 
v_unused_4772_ = lean_ctor_get(v___x_4754_, 3);
lean_dec(v_unused_4772_);
v___x_4760_ = v___x_4754_;
v_isShared_4761_ = v_isSharedCheck_4771_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_target_4757_);
lean_inc(v_typeAnalysis_4756_);
lean_inc(v_caches_4755_);
lean_dec(v___x_4754_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4771_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
lean_ctor_set(v___x_4760_, 3, v_snd_4753_);
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_caches_4755_);
lean_ctor_set(v_reuseFailAlloc_4770_, 1, v_typeAnalysis_4756_);
lean_ctor_set(v_reuseFailAlloc_4770_, 2, v_target_4757_);
lean_ctor_set(v_reuseFailAlloc_4770_, 3, v_snd_4753_);
lean_ctor_set_uint8(v_reuseFailAlloc_4770_, sizeof(void*)*4, v_didChange_4758_);
v___x_4763_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4764_; uint8_t v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4768_; 
v___x_4764_ = lean_st_ref_put(v_a_4675_, v___x_4763_);
v___x_4765_ = 0;
v___x_4766_ = lean_box(v___x_4765_);
if (v_isShared_4751_ == 0)
{
lean_ctor_set(v___x_4750_, 0, v___x_4766_);
v___x_4768_ = v___x_4750_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4766_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
else
{
lean_object* v_val_4773_; lean_object* v___x_4775_; 
lean_inc_ref(v_fst_4752_);
lean_dec(v_a_4748_);
v_val_4773_ = lean_ctor_get(v_fst_4752_, 0);
lean_inc(v_val_4773_);
lean_dec_ref_known(v_fst_4752_, 1);
if (v_isShared_4751_ == 0)
{
lean_ctor_set(v___x_4750_, 0, v_val_4773_);
v___x_4775_ = v___x_4750_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_val_4773_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
v_a_4778_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4747_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4747_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4792_, lean_object* v_methods_4793_, lean_object* v_config_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_){
_start:
{
uint8_t v_cacheId_boxed_4807_; lean_object* v_res_4808_; 
v_cacheId_boxed_4807_ = lean_unbox(v_cacheId_4792_);
v_res_4808_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4807_, v_methods_4793_, v_config_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
lean_dec(v_a_4799_);
lean_dec_ref(v_a_4798_);
lean_dec(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v___x_4815_; lean_object* v_env_4816_; lean_object* v___x_4817_; lean_object* v_mctx_4818_; lean_object* v_lctx_4819_; lean_object* v_options_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4815_ = lean_st_ref_get(v___y_4813_);
v_env_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc_ref(v_env_4816_);
lean_dec(v___x_4815_);
v___x_4817_ = lean_st_ref_get(v___y_4811_);
v_mctx_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc_ref(v_mctx_4818_);
lean_dec(v___x_4817_);
v_lctx_4819_ = lean_ctor_get(v___y_4810_, 2);
v_options_4820_ = lean_ctor_get(v___y_4812_, 2);
lean_inc_ref(v_options_4820_);
lean_inc_ref(v_lctx_4819_);
v___x_4821_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4821_, 0, v_env_4816_);
lean_ctor_set(v___x_4821_, 1, v_mctx_4818_);
lean_ctor_set(v___x_4821_, 2, v_lctx_4819_);
lean_ctor_set(v___x_4821_, 3, v_options_4820_);
v___x_4822_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4821_);
lean_ctor_set(v___x_4822_, 1, v_msgData_4809_);
v___x_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4822_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
return v_res_4830_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4831_; double v___x_4832_; 
v___x_4831_ = lean_unsigned_to_nat(0u);
v___x_4832_ = lean_float_of_nat(v___x_4831_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4836_, lean_object* v_msg_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v_ref_4843_; lean_object* v___x_4844_; lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4889_; 
v_ref_4843_ = lean_ctor_get(v___y_4840_, 5);
v___x_4844_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4847_ = v___x_4844_;
v_isShared_4848_ = v_isSharedCheck_4889_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4844_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4889_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4849_; lean_object* v_traceState_4850_; lean_object* v_env_4851_; lean_object* v_nextMacroScope_4852_; lean_object* v_ngen_4853_; lean_object* v_auxDeclNGen_4854_; lean_object* v_cache_4855_; lean_object* v_messages_4856_; lean_object* v_infoState_4857_; lean_object* v_snapshotTasks_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4888_; 
v___x_4849_ = lean_st_ref_take(v___y_4841_);
v_traceState_4850_ = lean_ctor_get(v___x_4849_, 4);
v_env_4851_ = lean_ctor_get(v___x_4849_, 0);
v_nextMacroScope_4852_ = lean_ctor_get(v___x_4849_, 1);
v_ngen_4853_ = lean_ctor_get(v___x_4849_, 2);
v_auxDeclNGen_4854_ = lean_ctor_get(v___x_4849_, 3);
v_cache_4855_ = lean_ctor_get(v___x_4849_, 5);
v_messages_4856_ = lean_ctor_get(v___x_4849_, 6);
v_infoState_4857_ = lean_ctor_get(v___x_4849_, 7);
v_snapshotTasks_4858_ = lean_ctor_get(v___x_4849_, 8);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4860_ = v___x_4849_;
v_isShared_4861_ = v_isSharedCheck_4888_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_snapshotTasks_4858_);
lean_inc(v_infoState_4857_);
lean_inc(v_messages_4856_);
lean_inc(v_cache_4855_);
lean_inc(v_traceState_4850_);
lean_inc(v_auxDeclNGen_4854_);
lean_inc(v_ngen_4853_);
lean_inc(v_nextMacroScope_4852_);
lean_inc(v_env_4851_);
lean_dec(v___x_4849_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4888_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
uint64_t v_tid_4862_; lean_object* v_traces_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4887_; 
v_tid_4862_ = lean_ctor_get_uint64(v_traceState_4850_, sizeof(void*)*1);
v_traces_4863_ = lean_ctor_get(v_traceState_4850_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v_traceState_4850_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4865_ = v_traceState_4850_;
v_isShared_4866_ = v_isSharedCheck_4887_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_traces_4863_);
lean_dec(v_traceState_4850_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4887_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4867_; double v___x_4868_; uint8_t v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4877_; 
v___x_4867_ = lean_box(0);
v___x_4868_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4869_ = 0;
v___x_4870_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4871_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4871_, 0, v_cls_4836_);
lean_ctor_set(v___x_4871_, 1, v___x_4867_);
lean_ctor_set(v___x_4871_, 2, v___x_4870_);
lean_ctor_set_float(v___x_4871_, sizeof(void*)*3, v___x_4868_);
lean_ctor_set_float(v___x_4871_, sizeof(void*)*3 + 8, v___x_4868_);
lean_ctor_set_uint8(v___x_4871_, sizeof(void*)*3 + 16, v___x_4869_);
v___x_4872_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4873_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4871_);
lean_ctor_set(v___x_4873_, 1, v_a_4845_);
lean_ctor_set(v___x_4873_, 2, v___x_4872_);
lean_inc(v_ref_4843_);
v___x_4874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4874_, 0, v_ref_4843_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
v___x_4875_ = l_Lean_PersistentArray_push___redArg(v_traces_4863_, v___x_4874_);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 0, v___x_4875_);
v___x_4877_ = v___x_4865_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4875_);
lean_ctor_set_uint64(v_reuseFailAlloc_4886_, sizeof(void*)*1, v_tid_4862_);
v___x_4877_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
lean_object* v___x_4879_; 
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 4, v___x_4877_);
v___x_4879_ = v___x_4860_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_env_4851_);
lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_nextMacroScope_4852_);
lean_ctor_set(v_reuseFailAlloc_4885_, 2, v_ngen_4853_);
lean_ctor_set(v_reuseFailAlloc_4885_, 3, v_auxDeclNGen_4854_);
lean_ctor_set(v_reuseFailAlloc_4885_, 4, v___x_4877_);
lean_ctor_set(v_reuseFailAlloc_4885_, 5, v_cache_4855_);
lean_ctor_set(v_reuseFailAlloc_4885_, 6, v_messages_4856_);
lean_ctor_set(v_reuseFailAlloc_4885_, 7, v_infoState_4857_);
lean_ctor_set(v_reuseFailAlloc_4885_, 8, v_snapshotTasks_4858_);
v___x_4879_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4880_ = lean_st_ref_put(v___y_4841_, v___x_4879_);
v___x_4881_ = lean_box(0);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4881_);
v___x_4883_ = v___x_4847_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4890_, lean_object* v_msg_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4890_, v_msg_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_4898_, lean_object* v___f_4899_, lean_object* v_____r_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4914_; lean_object* v_caches_4915_; lean_object* v_typeAnalysis_4916_; lean_object* v_target_4917_; lean_object* v_hypotheses_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4928_; 
v___x_4914_ = lean_st_ref_take(v___y_4903_);
v_caches_4915_ = lean_ctor_get(v___x_4914_, 0);
v_typeAnalysis_4916_ = lean_ctor_get(v___x_4914_, 1);
v_target_4917_ = lean_ctor_get(v___x_4914_, 2);
v_hypotheses_4918_ = lean_ctor_get(v___x_4914_, 3);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4920_ = v___x_4914_;
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_hypotheses_4918_);
lean_inc(v_target_4917_);
lean_inc(v_typeAnalysis_4916_);
lean_inc(v_caches_4915_);
lean_dec(v___x_4914_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_caches_4915_);
lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_typeAnalysis_4916_);
lean_ctor_set(v_reuseFailAlloc_4927_, 2, v_target_4917_);
lean_ctor_set(v_reuseFailAlloc_4927_, 3, v_hypotheses_4918_);
v___x_4923_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
lean_ctor_set_uint8(v___x_4923_, sizeof(void*)*4, v___x_4898_);
v___x_4924_ = lean_st_ref_put(v___y_4903_, v___x_4923_);
v___x_4925_ = lean_box(0);
lean_inc(v___y_4912_);
lean_inc_ref(v___y_4911_);
lean_inc(v___y_4910_);
lean_inc_ref(v___y_4909_);
lean_inc(v___y_4908_);
lean_inc_ref(v___y_4907_);
lean_inc(v___y_4906_);
lean_inc_ref(v___y_4905_);
lean_inc(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
lean_inc(v___y_4901_);
v___x_4926_ = lean_apply_14(v___f_4899_, v___x_4925_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, lean_box(0));
return v___x_4926_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_4929_, lean_object* v___f_4930_, lean_object* v_____r_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
uint8_t v___x_35663__boxed_4945_; lean_object* v_res_4946_; 
v___x_35663__boxed_4945_ = lean_unbox(v___x_4929_);
v_res_4946_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35663__boxed_4945_, v___f_4930_, v_____r_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
lean_dec(v___y_4934_);
lean_dec_ref(v___y_4933_);
lean_dec(v___y_4932_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_4947_, lean_object* v_a_4948_, lean_object* v___x_4949_, lean_object* v_____r_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4964_ = lean_array_push(v_snd_4947_, v_a_4948_);
v___x_4965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4949_);
lean_ctor_set(v___x_4965_, 1, v___x_4964_);
v___x_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4965_);
v___x_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4966_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_4968_ = _args[0];
lean_object* v_a_4969_ = _args[1];
lean_object* v___x_4970_ = _args[2];
lean_object* v_____r_4971_ = _args[3];
lean_object* v___y_4972_ = _args[4];
lean_object* v___y_4973_ = _args[5];
lean_object* v___y_4974_ = _args[6];
lean_object* v___y_4975_ = _args[7];
lean_object* v___y_4976_ = _args[8];
lean_object* v___y_4977_ = _args[9];
lean_object* v___y_4978_ = _args[10];
lean_object* v___y_4979_ = _args[11];
lean_object* v___y_4980_ = _args[12];
lean_object* v___y_4981_ = _args[13];
lean_object* v___y_4982_ = _args[14];
lean_object* v___y_4983_ = _args[15];
lean_object* v___y_4984_ = _args[16];
_start:
{
lean_object* v_res_4985_; 
v_res_4985_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_4968_, v_a_4969_, v___x_4970_, v_____r_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
lean_dec(v___y_4972_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_4986_, lean_object* v___x_4987_, lean_object* v_methods_4988_, lean_object* v_config_4989_, lean_object* v_a_4990_, lean_object* v_b_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
lean_object* v___y_5006_; uint8_t v___x_5028_; 
v___x_5028_ = lean_nat_dec_lt(v_a_4990_, v_upperBound_4986_);
if (v___x_5028_ == 0)
{
lean_object* v___x_5029_; 
lean_dec(v_a_4990_);
lean_dec_ref(v_config_4989_);
lean_dec_ref(v_methods_4988_);
v___x_5029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5029_, 0, v_b_4991_);
return v___x_5029_;
}
else
{
lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v_type_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5030_ = lean_st_ref_take(v___y_4992_);
v___x_5031_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_5032_ = lean_st_ref_put(v___y_4992_, v___x_5031_);
v___x_5033_ = lean_array_fget_borrowed(v___x_4987_, v_a_4990_);
v_type_5034_ = lean_ctor_get(v___x_5033_, 1);
v___x_5035_ = lean_unsigned_to_nat(0u);
v___x_5036_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
lean_ctor_set(v___x_5036_, 1, v___x_5030_);
lean_ctor_set(v___x_5036_, 2, v___x_5031_);
lean_ctor_set(v___x_5036_, 3, v___x_5031_);
lean_inc_ref(v_type_5034_);
v___x_5037_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5037_, 0, v_type_5034_);
lean_inc_ref(v_config_4989_);
lean_inc_ref(v_methods_4988_);
v___x_5038_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5037_, v_methods_4988_, v_config_4989_, v___x_5036_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; lean_object* v_snd_5040_; lean_object* v_fst_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5121_; 
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5039_);
lean_dec_ref_known(v___x_5038_, 1);
v_snd_5040_ = lean_ctor_get(v_a_5039_, 1);
v_fst_5041_ = lean_ctor_get(v_a_5039_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v_a_5039_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5043_ = v_a_5039_;
v_isShared_5044_ = v_isSharedCheck_5121_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_snd_5040_);
lean_inc(v_fst_5041_);
lean_dec(v_a_5039_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5121_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v_persistentCache_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v_persistentCache_5045_ = lean_ctor_get(v_snd_5040_, 1);
lean_inc_ref(v_persistentCache_5045_);
lean_dec(v_snd_5040_);
v___x_5046_ = lean_st_ref_swap(v___y_4992_, v_persistentCache_5045_);
lean_dec(v___x_5046_);
lean_inc(v___x_5033_);
v___x_5047_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5033_, v_fst_5041_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v_snd_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5111_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
v_snd_5049_ = lean_ctor_get(v_b_4991_, 1);
v_isSharedCheck_5111_ = !lean_is_exclusive(v_b_4991_);
if (v_isSharedCheck_5111_ == 0)
{
lean_object* v_unused_5112_; 
v_unused_5112_ = lean_ctor_get(v_b_4991_, 0);
lean_dec(v_unused_5112_);
v___x_5051_ = v_b_4991_;
v_isShared_5052_ = v_isSharedCheck_5111_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_snd_5049_);
lean_dec(v_b_4991_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5111_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v_type_5053_; lean_object* v_value_5054_; uint8_t v___x_5055_; 
v_type_5053_ = lean_ctor_get(v_a_5048_, 1);
v_value_5054_ = lean_ctor_get(v_a_5048_, 2);
lean_inc_ref(v_type_5053_);
v___x_5055_ = l_Lean_Expr_isFalse(v_type_5053_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; lean_object* v___f_5057_; uint8_t v___x_5086_; 
lean_del_object(v___x_5051_);
v___x_5056_ = lean_box(0);
lean_inc(v_a_5048_);
lean_inc(v_snd_5049_);
v___f_5057_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5057_, 0, v_snd_5049_);
lean_closure_set(v___f_5057_, 1, v_a_5048_);
lean_closure_set(v___f_5057_, 2, v___x_5056_);
v___x_5086_ = lean_expr_eqv(v_type_5034_, v_type_5053_);
if (v___x_5086_ == 0)
{
lean_inc_ref(v_type_5053_);
lean_dec(v_snd_5049_);
lean_dec(v_a_5048_);
goto v___jp_5061_;
}
else
{
if (v___x_5055_ == 0)
{
lean_object* v___x_5087_; lean_object* v___x_5088_; 
lean_dec_ref(v___f_5057_);
lean_del_object(v___x_5043_);
v___x_5087_ = lean_box(0);
v___x_5088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5049_, v_a_5048_, v___x_5056_, v___x_5087_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
v___y_5006_ = v___x_5088_;
goto v___jp_5005_;
}
else
{
lean_inc_ref(v_type_5053_);
lean_dec(v_snd_5049_);
lean_dec(v_a_5048_);
goto v___jp_5061_;
}
}
v___jp_5058_:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = lean_box(0);
v___x_5060_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5028_, v___f_5057_, v___x_5059_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
v___y_5006_ = v___x_5060_;
goto v___jp_5005_;
}
v___jp_5061_:
{
lean_object* v_options_5062_; uint8_t v_hasTrace_5063_; 
v_options_5062_ = lean_ctor_get(v___y_5002_, 2);
v_hasTrace_5063_ = lean_ctor_get_uint8(v_options_5062_, sizeof(void*)*1);
if (v_hasTrace_5063_ == 0)
{
lean_dec_ref(v_type_5053_);
lean_del_object(v___x_5043_);
goto v___jp_5058_;
}
else
{
lean_object* v_inheritedTraceOptions_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; uint8_t v___x_5067_; 
v_inheritedTraceOptions_5064_ = lean_ctor_get(v___y_5002_, 13);
v___x_5065_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5066_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5064_, v_options_5062_, v___x_5066_);
if (v___x_5067_ == 0)
{
lean_dec_ref(v_type_5053_);
lean_del_object(v___x_5043_);
goto v___jp_5058_;
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5071_; 
lean_inc_ref(v_type_5034_);
v___x_5068_ = l_Lean_MessageData_ofExpr(v_type_5034_);
v___x_5069_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5044_ == 0)
{
lean_ctor_set_tag(v___x_5043_, 7);
lean_ctor_set(v___x_5043_, 1, v___x_5069_);
lean_ctor_set(v___x_5043_, 0, v___x_5068_);
v___x_5071_ = v___x_5043_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5072_ = l_Lean_MessageData_ofExpr(v_type_5053_);
v___x_5073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5071_);
lean_ctor_set(v___x_5073_, 1, v___x_5072_);
v___x_5074_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5065_, v___x_5073_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; lean_object* v___x_5076_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_a_5075_);
lean_dec_ref_known(v___x_5074_, 1);
v___x_5076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5028_, v___f_5057_, v_a_5075_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
v___y_5006_ = v___x_5076_;
goto v___jp_5005_;
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_dec_ref(v___f_5057_);
lean_dec(v_a_4990_);
lean_dec_ref(v_config_4989_);
lean_dec_ref(v_methods_4988_);
v_a_5077_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5074_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5074_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
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
lean_object* v___x_5089_; 
lean_inc_ref(v_value_5054_);
lean_dec(v_a_5048_);
lean_del_object(v___x_5043_);
lean_dec(v_a_4990_);
lean_dec_ref(v_config_4989_);
lean_dec_ref(v_methods_4988_);
v___x_5089_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5054_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5101_; 
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5101_ == 0)
{
lean_object* v_unused_5102_; 
v_unused_5102_ = lean_ctor_get(v___x_5089_, 0);
lean_dec(v_unused_5102_);
v___x_5091_ = v___x_5089_;
v_isShared_5092_ = v_isSharedCheck_5101_;
goto v_resetjp_5090_;
}
else
{
lean_dec(v___x_5089_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5101_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5096_; 
v___x_5093_ = lean_box(v___x_5028_);
v___x_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
if (v_isShared_5052_ == 0)
{
lean_ctor_set(v___x_5051_, 0, v___x_5094_);
v___x_5096_ = v___x_5051_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5094_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v_snd_5049_);
v___x_5096_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5098_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v___x_5096_);
v___x_5098_ = v___x_5091_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5096_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_del_object(v___x_5051_);
lean_dec(v_snd_5049_);
v_a_5103_ = lean_ctor_get(v___x_5089_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_5089_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5089_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_del_object(v___x_5043_);
lean_dec_ref(v_b_4991_);
lean_dec(v_a_4990_);
lean_dec_ref(v_config_4989_);
lean_dec_ref(v_methods_4988_);
v_a_5113_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5047_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5047_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
lean_dec_ref(v_b_4991_);
lean_dec(v_a_4990_);
lean_dec_ref(v_config_4989_);
lean_dec_ref(v_methods_4988_);
v_a_5122_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5038_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5038_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
}
}
v___jp_5005_:
{
if (lean_obj_tag(v___y_5006_) == 0)
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5019_; 
v_a_5007_ = lean_ctor_get(v___y_5006_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___y_5006_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5009_ = v___y_5006_;
v_isShared_5010_ = v_isSharedCheck_5019_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___y_5006_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5019_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
if (lean_obj_tag(v_a_5007_) == 0)
{
lean_object* v_a_5011_; lean_object* v___x_5013_; 
lean_dec(v_a_4990_);
lean_dec_ref(v_config_4989_);
lean_dec_ref(v_methods_4988_);
v_a_5011_ = lean_ctor_get(v_a_5007_, 0);
lean_inc(v_a_5011_);
lean_dec_ref_known(v_a_5007_, 1);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 0, v_a_5011_);
v___x_5013_ = v___x_5009_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5011_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
else
{
lean_object* v_a_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
lean_del_object(v___x_5009_);
v_a_5015_ = lean_ctor_get(v_a_5007_, 0);
lean_inc(v_a_5015_);
lean_dec_ref_known(v_a_5007_, 1);
v___x_5016_ = lean_unsigned_to_nat(1u);
v___x_5017_ = lean_nat_add(v_a_4990_, v___x_5016_);
lean_dec(v_a_4990_);
v_a_4990_ = v___x_5017_;
v_b_4991_ = v_a_5015_;
goto _start;
}
}
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec(v_a_4990_);
lean_dec_ref(v_config_4989_);
lean_dec_ref(v_methods_4988_);
v_a_5020_ = lean_ctor_get(v___y_5006_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___y_5006_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___y_5006_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___y_5006_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5130_ = _args[0];
lean_object* v___x_5131_ = _args[1];
lean_object* v_methods_5132_ = _args[2];
lean_object* v_config_5133_ = _args[3];
lean_object* v_a_5134_ = _args[4];
lean_object* v_b_5135_ = _args[5];
lean_object* v___y_5136_ = _args[6];
lean_object* v___y_5137_ = _args[7];
lean_object* v___y_5138_ = _args[8];
lean_object* v___y_5139_ = _args[9];
lean_object* v___y_5140_ = _args[10];
lean_object* v___y_5141_ = _args[11];
lean_object* v___y_5142_ = _args[12];
lean_object* v___y_5143_ = _args[13];
lean_object* v___y_5144_ = _args[14];
lean_object* v___y_5145_ = _args[15];
lean_object* v___y_5146_ = _args[16];
lean_object* v___y_5147_ = _args[17];
lean_object* v___y_5148_ = _args[18];
_start:
{
lean_object* v_res_5149_; 
v_res_5149_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5130_, v___x_5131_, v_methods_5132_, v_config_5133_, v_a_5134_, v_b_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
lean_dec(v___y_5147_);
lean_dec_ref(v___y_5146_);
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5137_);
lean_dec(v___y_5136_);
lean_dec_ref(v___x_5131_);
lean_dec(v_upperBound_5130_);
return v_res_5149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_5150_, lean_object* v_config_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_){
_start:
{
lean_object* v___x_5165_; lean_object* v_hypotheses_5166_; lean_object* v___x_5167_; lean_object* v_newHyps_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5165_ = lean_st_ref_get(v_a_5154_);
v_hypotheses_5166_ = lean_ctor_get(v___x_5165_, 3);
lean_inc_ref(v_hypotheses_5166_);
lean_dec(v___x_5165_);
v___x_5167_ = lean_array_get_size(v_hypotheses_5166_);
v_newHyps_5168_ = lean_mk_empty_array_with_capacity(v___x_5167_);
v___x_5169_ = lean_unsigned_to_nat(0u);
v___x_5170_ = lean_box(0);
v___x_5171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5170_);
lean_ctor_set(v___x_5171_, 1, v_newHyps_5168_);
v___x_5172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_5167_, v_hypotheses_5166_, v_methods_5150_, v_config_5151_, v___x_5169_, v___x_5171_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
lean_dec_ref(v_hypotheses_5166_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5202_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5175_ = v___x_5172_;
v_isShared_5176_ = v_isSharedCheck_5202_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5172_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5202_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v_fst_5177_; 
v_fst_5177_ = lean_ctor_get(v_a_5173_, 0);
if (lean_obj_tag(v_fst_5177_) == 0)
{
lean_object* v_snd_5178_; lean_object* v___x_5179_; lean_object* v_caches_5180_; lean_object* v_typeAnalysis_5181_; lean_object* v_target_5182_; uint8_t v_didChange_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5196_; 
v_snd_5178_ = lean_ctor_get(v_a_5173_, 1);
lean_inc(v_snd_5178_);
lean_dec(v_a_5173_);
v___x_5179_ = lean_st_ref_take(v_a_5154_);
v_caches_5180_ = lean_ctor_get(v___x_5179_, 0);
v_typeAnalysis_5181_ = lean_ctor_get(v___x_5179_, 1);
v_target_5182_ = lean_ctor_get(v___x_5179_, 2);
v_didChange_5183_ = lean_ctor_get_uint8(v___x_5179_, sizeof(void*)*4);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5196_ == 0)
{
lean_object* v_unused_5197_; 
v_unused_5197_ = lean_ctor_get(v___x_5179_, 3);
lean_dec(v_unused_5197_);
v___x_5185_ = v___x_5179_;
v_isShared_5186_ = v_isSharedCheck_5196_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_target_5182_);
lean_inc(v_typeAnalysis_5181_);
lean_inc(v_caches_5180_);
lean_dec(v___x_5179_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5196_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 3, v_snd_5178_);
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_caches_5180_);
lean_ctor_set(v_reuseFailAlloc_5195_, 1, v_typeAnalysis_5181_);
lean_ctor_set(v_reuseFailAlloc_5195_, 2, v_target_5182_);
lean_ctor_set(v_reuseFailAlloc_5195_, 3, v_snd_5178_);
lean_ctor_set_uint8(v_reuseFailAlloc_5195_, sizeof(void*)*4, v_didChange_5183_);
v___x_5188_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
lean_object* v___x_5189_; uint8_t v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5193_; 
v___x_5189_ = lean_st_ref_put(v_a_5154_, v___x_5188_);
v___x_5190_ = 0;
v___x_5191_ = lean_box(v___x_5190_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 0, v___x_5191_);
v___x_5193_ = v___x_5175_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v___x_5191_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
else
{
lean_object* v_val_5198_; lean_object* v___x_5200_; 
lean_inc_ref(v_fst_5177_);
lean_dec(v_a_5173_);
v_val_5198_ = lean_ctor_get(v_fst_5177_, 0);
lean_inc(v_val_5198_);
lean_dec_ref_known(v_fst_5177_, 1);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 0, v_val_5198_);
v___x_5200_ = v___x_5175_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_val_5198_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
v_a_5203_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5172_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5172_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5208_; 
if (v_isShared_5206_ == 0)
{
v___x_5208_ = v___x_5205_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5203_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_5211_, lean_object* v_config_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5211_, v_config_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec_ref(v_a_5221_);
lean_dec(v_a_5220_);
lean_dec_ref(v_a_5219_);
lean_dec(v_a_5218_);
lean_dec_ref(v_a_5217_);
lean_dec(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_5227_, lean_object* v_msg_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v___x_5242_; 
v___x_5242_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5227_, v_msg_5228_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_5243_, lean_object* v_msg_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5243_, v_msg_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_upperBound_5259_, lean_object* v___x_5260_, lean_object* v_methods_5261_, lean_object* v_config_5262_, lean_object* v_inst_5263_, lean_object* v_R_5264_, lean_object* v_a_5265_, lean_object* v_b_5266_, lean_object* v_c_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
lean_object* v___x_5281_; 
v___x_5281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5259_, v___x_5260_, v_methods_5261_, v_config_5262_, v_a_5265_, v_b_5266_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
return v___x_5281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5282_ = _args[0];
lean_object* v___x_5283_ = _args[1];
lean_object* v_methods_5284_ = _args[2];
lean_object* v_config_5285_ = _args[3];
lean_object* v_inst_5286_ = _args[4];
lean_object* v_R_5287_ = _args[5];
lean_object* v_a_5288_ = _args[6];
lean_object* v_b_5289_ = _args[7];
lean_object* v_c_5290_ = _args[8];
lean_object* v___y_5291_ = _args[9];
lean_object* v___y_5292_ = _args[10];
lean_object* v___y_5293_ = _args[11];
lean_object* v___y_5294_ = _args[12];
lean_object* v___y_5295_ = _args[13];
lean_object* v___y_5296_ = _args[14];
lean_object* v___y_5297_ = _args[15];
lean_object* v___y_5298_ = _args[16];
lean_object* v___y_5299_ = _args[17];
lean_object* v___y_5300_ = _args[18];
lean_object* v___y_5301_ = _args[19];
lean_object* v___y_5302_ = _args[20];
lean_object* v___y_5303_ = _args[21];
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5282_, v___x_5283_, v_methods_5284_, v_config_5285_, v_inst_5286_, v_R_5287_, v_a_5288_, v_b_5289_, v_c_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
lean_dec(v___y_5298_);
lean_dec_ref(v___y_5297_);
lean_dec(v___y_5296_);
lean_dec_ref(v___y_5295_);
lean_dec(v___y_5294_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___x_5283_);
lean_dec(v_upperBound_5282_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_5305_, lean_object* v_config_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_){
_start:
{
lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
v___x_5319_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_5320_ = lean_st_mk_ref(v___x_5319_);
v___x_5321_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5305_, v_config_5306_, v___x_5320_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5330_; 
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5324_ = v___x_5321_;
v_isShared_5325_ = v_isSharedCheck_5330_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5321_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5330_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5326_; lean_object* v___x_5328_; 
v___x_5326_ = lean_st_ref_get(v___x_5320_);
lean_dec(v___x_5320_);
lean_dec(v___x_5326_);
if (v_isShared_5325_ == 0)
{
v___x_5328_ = v___x_5324_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5322_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
}
else
{
lean_dec(v___x_5320_);
return v___x_5321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_5331_, lean_object* v_config_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_){
_start:
{
lean_object* v_res_5345_; 
v_res_5345_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5331_, v_config_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_);
lean_dec(v_a_5343_);
lean_dec_ref(v_a_5342_);
lean_dec(v_a_5341_);
lean_dec_ref(v_a_5340_);
lean_dec(v_a_5339_);
lean_dec_ref(v_a_5338_);
lean_dec(v_a_5337_);
lean_dec_ref(v_a_5336_);
lean_dec(v_a_5335_);
lean_dec(v_a_5334_);
lean_dec_ref(v_a_5333_);
return v_res_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_5346_, lean_object* v_msg_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
lean_object* v_ref_5353_; lean_object* v___x_5354_; lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5399_; 
v_ref_5353_ = lean_ctor_get(v___y_5350_, 5);
v___x_5354_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
v_a_5355_ = lean_ctor_get(v___x_5354_, 0);
v_isSharedCheck_5399_ = !lean_is_exclusive(v___x_5354_);
if (v_isSharedCheck_5399_ == 0)
{
v___x_5357_ = v___x_5354_;
v_isShared_5358_ = v_isSharedCheck_5399_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5354_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5399_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; lean_object* v_traceState_5360_; lean_object* v_env_5361_; lean_object* v_nextMacroScope_5362_; lean_object* v_ngen_5363_; lean_object* v_auxDeclNGen_5364_; lean_object* v_cache_5365_; lean_object* v_messages_5366_; lean_object* v_infoState_5367_; lean_object* v_snapshotTasks_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5398_; 
v___x_5359_ = lean_st_ref_take(v___y_5351_);
v_traceState_5360_ = lean_ctor_get(v___x_5359_, 4);
v_env_5361_ = lean_ctor_get(v___x_5359_, 0);
v_nextMacroScope_5362_ = lean_ctor_get(v___x_5359_, 1);
v_ngen_5363_ = lean_ctor_get(v___x_5359_, 2);
v_auxDeclNGen_5364_ = lean_ctor_get(v___x_5359_, 3);
v_cache_5365_ = lean_ctor_get(v___x_5359_, 5);
v_messages_5366_ = lean_ctor_get(v___x_5359_, 6);
v_infoState_5367_ = lean_ctor_get(v___x_5359_, 7);
v_snapshotTasks_5368_ = lean_ctor_get(v___x_5359_, 8);
v_isSharedCheck_5398_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5398_ == 0)
{
v___x_5370_ = v___x_5359_;
v_isShared_5371_ = v_isSharedCheck_5398_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_snapshotTasks_5368_);
lean_inc(v_infoState_5367_);
lean_inc(v_messages_5366_);
lean_inc(v_cache_5365_);
lean_inc(v_traceState_5360_);
lean_inc(v_auxDeclNGen_5364_);
lean_inc(v_ngen_5363_);
lean_inc(v_nextMacroScope_5362_);
lean_inc(v_env_5361_);
lean_dec(v___x_5359_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5398_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
uint64_t v_tid_5372_; lean_object* v_traces_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5397_; 
v_tid_5372_ = lean_ctor_get_uint64(v_traceState_5360_, sizeof(void*)*1);
v_traces_5373_ = lean_ctor_get(v_traceState_5360_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v_traceState_5360_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5375_ = v_traceState_5360_;
v_isShared_5376_ = v_isSharedCheck_5397_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_traces_5373_);
lean_dec(v_traceState_5360_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5397_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5377_; double v___x_5378_; uint8_t v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5387_; 
v___x_5377_ = lean_box(0);
v___x_5378_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5379_ = 0;
v___x_5380_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5381_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5381_, 0, v_cls_5346_);
lean_ctor_set(v___x_5381_, 1, v___x_5377_);
lean_ctor_set(v___x_5381_, 2, v___x_5380_);
lean_ctor_set_float(v___x_5381_, sizeof(void*)*3, v___x_5378_);
lean_ctor_set_float(v___x_5381_, sizeof(void*)*3 + 8, v___x_5378_);
lean_ctor_set_uint8(v___x_5381_, sizeof(void*)*3 + 16, v___x_5379_);
v___x_5382_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5383_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5381_);
lean_ctor_set(v___x_5383_, 1, v_a_5355_);
lean_ctor_set(v___x_5383_, 2, v___x_5382_);
lean_inc(v_ref_5353_);
v___x_5384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5384_, 0, v_ref_5353_);
lean_ctor_set(v___x_5384_, 1, v___x_5383_);
v___x_5385_ = l_Lean_PersistentArray_push___redArg(v_traces_5373_, v___x_5384_);
if (v_isShared_5376_ == 0)
{
lean_ctor_set(v___x_5375_, 0, v___x_5385_);
v___x_5387_ = v___x_5375_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v___x_5385_);
lean_ctor_set_uint64(v_reuseFailAlloc_5396_, sizeof(void*)*1, v_tid_5372_);
v___x_5387_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
lean_object* v___x_5389_; 
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 4, v___x_5387_);
v___x_5389_ = v___x_5370_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_env_5361_);
lean_ctor_set(v_reuseFailAlloc_5395_, 1, v_nextMacroScope_5362_);
lean_ctor_set(v_reuseFailAlloc_5395_, 2, v_ngen_5363_);
lean_ctor_set(v_reuseFailAlloc_5395_, 3, v_auxDeclNGen_5364_);
lean_ctor_set(v_reuseFailAlloc_5395_, 4, v___x_5387_);
lean_ctor_set(v_reuseFailAlloc_5395_, 5, v_cache_5365_);
lean_ctor_set(v_reuseFailAlloc_5395_, 6, v_messages_5366_);
lean_ctor_set(v_reuseFailAlloc_5395_, 7, v_infoState_5367_);
lean_ctor_set(v_reuseFailAlloc_5395_, 8, v_snapshotTasks_5368_);
v___x_5389_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5393_; 
v___x_5390_ = lean_st_ref_put(v___y_5351_, v___x_5389_);
v___x_5391_ = lean_box(0);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 0, v___x_5391_);
v___x_5393_ = v___x_5357_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v___x_5391_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5400_, lean_object* v_msg_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5400_, v_msg_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
lean_dec(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5408_, lean_object* v___x_5409_, lean_object* v_methods_5410_, lean_object* v_config_5411_, lean_object* v_a_5412_, lean_object* v_b_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_){
_start:
{
lean_object* v___y_5428_; uint8_t v___x_5450_; 
v___x_5450_ = lean_nat_dec_lt(v_a_5412_, v_upperBound_5408_);
if (v___x_5450_ == 0)
{
lean_object* v___x_5451_; 
lean_dec(v_a_5412_);
lean_dec_ref(v_config_5411_);
lean_dec_ref(v_methods_5410_);
v___x_5451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5451_, 0, v_b_5413_);
return v___x_5451_;
}
else
{
lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v_type_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___x_5452_ = lean_st_ref_take(v___y_5414_);
v___x_5453_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5454_ = lean_st_ref_put(v___y_5414_, v___x_5453_);
v___x_5455_ = lean_array_fget_borrowed(v___x_5409_, v_a_5412_);
v_type_5456_ = lean_ctor_get(v___x_5455_, 1);
v___x_5457_ = lean_unsigned_to_nat(0u);
v___x_5458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5458_, 0, v___x_5457_);
lean_ctor_set(v___x_5458_, 1, v___x_5452_);
lean_inc_ref(v_type_5456_);
v___x_5459_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5459_, 0, v_type_5456_);
lean_inc_ref(v_config_5411_);
lean_inc_ref(v_methods_5410_);
v___x_5460_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5459_, v_methods_5410_, v_config_5411_, v___x_5458_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; lean_object* v_snd_5462_; lean_object* v_fst_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5550_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_a_5461_);
lean_dec_ref_known(v___x_5460_, 1);
v_snd_5462_ = lean_ctor_get(v_a_5461_, 1);
v_fst_5463_ = lean_ctor_get(v_a_5461_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_a_5461_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5465_ = v_a_5461_;
v_isShared_5466_ = v_isSharedCheck_5550_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_snd_5462_);
lean_inc(v_fst_5463_);
lean_dec(v_a_5461_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5550_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v_cache_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5548_; 
v_cache_5467_ = lean_ctor_get(v_snd_5462_, 1);
v_isSharedCheck_5548_ = !lean_is_exclusive(v_snd_5462_);
if (v_isSharedCheck_5548_ == 0)
{
lean_object* v_unused_5549_; 
v_unused_5549_ = lean_ctor_get(v_snd_5462_, 0);
lean_dec(v_unused_5549_);
v___x_5469_ = v_snd_5462_;
v_isShared_5470_ = v_isSharedCheck_5548_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_cache_5467_);
lean_dec(v_snd_5462_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5548_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = lean_st_ref_swap(v___y_5414_, v_cache_5467_);
lean_dec(v___x_5471_);
lean_inc(v___x_5455_);
v___x_5472_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5455_, v_fst_5463_);
lean_dec(v_fst_5463_);
if (lean_obj_tag(v___x_5472_) == 0)
{
lean_object* v_a_5473_; lean_object* v_snd_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5538_; 
v_a_5473_ = lean_ctor_get(v___x_5472_, 0);
lean_inc(v_a_5473_);
lean_dec_ref_known(v___x_5472_, 1);
v_snd_5474_ = lean_ctor_get(v_b_5413_, 1);
v_isSharedCheck_5538_ = !lean_is_exclusive(v_b_5413_);
if (v_isSharedCheck_5538_ == 0)
{
lean_object* v_unused_5539_; 
v_unused_5539_ = lean_ctor_get(v_b_5413_, 0);
lean_dec(v_unused_5539_);
v___x_5476_ = v_b_5413_;
v_isShared_5477_ = v_isSharedCheck_5538_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_snd_5474_);
lean_dec(v_b_5413_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5538_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v_type_5478_; lean_object* v_value_5479_; uint8_t v___x_5480_; 
v_type_5478_ = lean_ctor_get(v_a_5473_, 1);
v_value_5479_ = lean_ctor_get(v_a_5473_, 2);
lean_inc_ref(v_type_5478_);
v___x_5480_ = l_Lean_Expr_isFalse(v_type_5478_);
if (v___x_5480_ == 0)
{
lean_object* v___x_5481_; lean_object* v___f_5482_; uint8_t v___x_5513_; 
lean_del_object(v___x_5476_);
v___x_5481_ = lean_box(0);
lean_inc(v_a_5473_);
lean_inc(v_snd_5474_);
v___f_5482_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5482_, 0, v_snd_5474_);
lean_closure_set(v___f_5482_, 1, v_a_5473_);
lean_closure_set(v___f_5482_, 2, v___x_5481_);
v___x_5513_ = lean_expr_eqv(v_type_5456_, v_type_5478_);
if (v___x_5513_ == 0)
{
lean_inc_ref(v_type_5478_);
lean_dec(v_snd_5474_);
lean_dec(v_a_5473_);
goto v___jp_5486_;
}
else
{
if (v___x_5480_ == 0)
{
lean_object* v___x_5514_; lean_object* v___x_5515_; 
lean_dec_ref(v___f_5482_);
lean_del_object(v___x_5469_);
lean_del_object(v___x_5465_);
v___x_5514_ = lean_box(0);
v___x_5515_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5474_, v_a_5473_, v___x_5481_, v___x_5514_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
v___y_5428_ = v___x_5515_;
goto v___jp_5427_;
}
else
{
lean_inc_ref(v_type_5478_);
lean_dec(v_snd_5474_);
lean_dec(v_a_5473_);
goto v___jp_5486_;
}
}
v___jp_5483_:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5484_ = lean_box(0);
v___x_5485_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5450_, v___f_5482_, v___x_5484_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
v___y_5428_ = v___x_5485_;
goto v___jp_5427_;
}
v___jp_5486_:
{
lean_object* v_options_5487_; uint8_t v_hasTrace_5488_; 
v_options_5487_ = lean_ctor_get(v___y_5424_, 2);
v_hasTrace_5488_ = lean_ctor_get_uint8(v_options_5487_, sizeof(void*)*1);
if (v_hasTrace_5488_ == 0)
{
lean_dec_ref(v_type_5478_);
lean_del_object(v___x_5469_);
lean_del_object(v___x_5465_);
goto v___jp_5483_;
}
else
{
lean_object* v_inheritedTraceOptions_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; uint8_t v___x_5492_; 
v_inheritedTraceOptions_5489_ = lean_ctor_get(v___y_5424_, 13);
v___x_5490_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5491_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5492_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5489_, v_options_5487_, v___x_5491_);
if (v___x_5492_ == 0)
{
lean_dec_ref(v_type_5478_);
lean_del_object(v___x_5469_);
lean_del_object(v___x_5465_);
goto v___jp_5483_;
}
else
{
lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5496_; 
lean_inc_ref(v_type_5456_);
v___x_5493_ = l_Lean_MessageData_ofExpr(v_type_5456_);
v___x_5494_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5470_ == 0)
{
lean_ctor_set_tag(v___x_5469_, 7);
lean_ctor_set(v___x_5469_, 1, v___x_5494_);
lean_ctor_set(v___x_5469_, 0, v___x_5493_);
v___x_5496_ = v___x_5469_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v___x_5493_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v___x_5494_);
v___x_5496_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
lean_object* v___x_5497_; lean_object* v___x_5499_; 
v___x_5497_ = l_Lean_MessageData_ofExpr(v_type_5478_);
if (v_isShared_5466_ == 0)
{
lean_ctor_set_tag(v___x_5465_, 7);
lean_ctor_set(v___x_5465_, 1, v___x_5497_);
lean_ctor_set(v___x_5465_, 0, v___x_5496_);
v___x_5499_ = v___x_5465_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v___x_5496_);
lean_ctor_set(v_reuseFailAlloc_5511_, 1, v___x_5497_);
v___x_5499_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5500_; 
v___x_5500_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5490_, v___x_5499_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v___x_5502_; 
v_a_5501_ = lean_ctor_get(v___x_5500_, 0);
lean_inc(v_a_5501_);
lean_dec_ref_known(v___x_5500_, 1);
v___x_5502_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5450_, v___f_5482_, v_a_5501_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
v___y_5428_ = v___x_5502_;
goto v___jp_5427_;
}
else
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
lean_dec_ref(v___f_5482_);
lean_dec(v_a_5412_);
lean_dec_ref(v_config_5411_);
lean_dec_ref(v_methods_5410_);
v_a_5503_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5505_ = v___x_5500_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v___x_5500_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
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
lean_object* v___x_5516_; 
lean_inc_ref(v_value_5479_);
lean_dec(v_a_5473_);
lean_del_object(v___x_5469_);
lean_del_object(v___x_5465_);
lean_dec(v_a_5412_);
lean_dec_ref(v_config_5411_);
lean_dec_ref(v_methods_5410_);
v___x_5516_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5479_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5528_; 
v_isSharedCheck_5528_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5528_ == 0)
{
lean_object* v_unused_5529_; 
v_unused_5529_ = lean_ctor_get(v___x_5516_, 0);
lean_dec(v_unused_5529_);
v___x_5518_ = v___x_5516_;
v_isShared_5519_ = v_isSharedCheck_5528_;
goto v_resetjp_5517_;
}
else
{
lean_dec(v___x_5516_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5528_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5523_; 
v___x_5520_ = lean_box(v___x_5450_);
v___x_5521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5521_, 0, v___x_5520_);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v___x_5521_);
v___x_5523_ = v___x_5476_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v___x_5521_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v_snd_5474_);
v___x_5523_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
lean_object* v___x_5525_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 0, v___x_5523_);
v___x_5525_ = v___x_5518_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v___x_5523_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
return v___x_5525_;
}
}
}
}
else
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5537_; 
lean_del_object(v___x_5476_);
lean_dec(v_snd_5474_);
v_a_5530_ = lean_ctor_get(v___x_5516_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5532_ = v___x_5516_;
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5516_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5535_; 
if (v_isShared_5533_ == 0)
{
v___x_5535_ = v___x_5532_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
return v___x_5535_;
}
}
}
}
}
}
else
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_del_object(v___x_5469_);
lean_del_object(v___x_5465_);
lean_dec_ref(v_b_5413_);
lean_dec(v_a_5412_);
lean_dec_ref(v_config_5411_);
lean_dec_ref(v_methods_5410_);
v_a_5540_ = lean_ctor_get(v___x_5472_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5472_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5472_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
}
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_dec_ref(v_b_5413_);
lean_dec(v_a_5412_);
lean_dec_ref(v_config_5411_);
lean_dec_ref(v_methods_5410_);
v_a_5551_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5460_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5460_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
v___jp_5427_:
{
if (lean_obj_tag(v___y_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5441_; 
v_a_5429_ = lean_ctor_get(v___y_5428_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___y_5428_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5431_ = v___y_5428_;
v_isShared_5432_ = v_isSharedCheck_5441_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___y_5428_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5441_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
if (lean_obj_tag(v_a_5429_) == 0)
{
lean_object* v_a_5433_; lean_object* v___x_5435_; 
lean_dec(v_a_5412_);
lean_dec_ref(v_config_5411_);
lean_dec_ref(v_methods_5410_);
v_a_5433_ = lean_ctor_get(v_a_5429_, 0);
lean_inc(v_a_5433_);
lean_dec_ref_known(v_a_5429_, 1);
if (v_isShared_5432_ == 0)
{
lean_ctor_set(v___x_5431_, 0, v_a_5433_);
v___x_5435_ = v___x_5431_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_a_5433_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
else
{
lean_object* v_a_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
lean_del_object(v___x_5431_);
v_a_5437_ = lean_ctor_get(v_a_5429_, 0);
lean_inc(v_a_5437_);
lean_dec_ref_known(v_a_5429_, 1);
v___x_5438_ = lean_unsigned_to_nat(1u);
v___x_5439_ = lean_nat_add(v_a_5412_, v___x_5438_);
lean_dec(v_a_5412_);
v_a_5412_ = v___x_5439_;
v_b_5413_ = v_a_5437_;
goto _start;
}
}
}
else
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5449_; 
lean_dec(v_a_5412_);
lean_dec_ref(v_config_5411_);
lean_dec_ref(v_methods_5410_);
v_a_5442_ = lean_ctor_get(v___y_5428_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___y_5428_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5444_ = v___y_5428_;
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___y_5428_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v___x_5447_; 
if (v_isShared_5445_ == 0)
{
v___x_5447_ = v___x_5444_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_a_5442_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5559_ = _args[0];
lean_object* v___x_5560_ = _args[1];
lean_object* v_methods_5561_ = _args[2];
lean_object* v_config_5562_ = _args[3];
lean_object* v_a_5563_ = _args[4];
lean_object* v_b_5564_ = _args[5];
lean_object* v___y_5565_ = _args[6];
lean_object* v___y_5566_ = _args[7];
lean_object* v___y_5567_ = _args[8];
lean_object* v___y_5568_ = _args[9];
lean_object* v___y_5569_ = _args[10];
lean_object* v___y_5570_ = _args[11];
lean_object* v___y_5571_ = _args[12];
lean_object* v___y_5572_ = _args[13];
lean_object* v___y_5573_ = _args[14];
lean_object* v___y_5574_ = _args[15];
lean_object* v___y_5575_ = _args[16];
lean_object* v___y_5576_ = _args[17];
lean_object* v___y_5577_ = _args[18];
_start:
{
lean_object* v_res_5578_; 
v_res_5578_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5559_, v___x_5560_, v_methods_5561_, v_config_5562_, v_a_5563_, v_b_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
lean_dec(v___y_5576_);
lean_dec_ref(v___y_5575_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec(v___y_5572_);
lean_dec_ref(v___y_5571_);
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
lean_dec(v___y_5565_);
lean_dec_ref(v___x_5560_);
lean_dec(v_upperBound_5559_);
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5579_, lean_object* v_config_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_){
_start:
{
lean_object* v___x_5594_; lean_object* v_hypotheses_5595_; lean_object* v___x_5596_; lean_object* v_newHyps_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; 
v___x_5594_ = lean_st_ref_get(v_a_5583_);
v_hypotheses_5595_ = lean_ctor_get(v___x_5594_, 3);
lean_inc_ref(v_hypotheses_5595_);
lean_dec(v___x_5594_);
v___x_5596_ = lean_array_get_size(v_hypotheses_5595_);
v_newHyps_5597_ = lean_mk_empty_array_with_capacity(v___x_5596_);
v___x_5598_ = lean_unsigned_to_nat(0u);
v___x_5599_ = lean_box(0);
v___x_5600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5600_, 0, v___x_5599_);
lean_ctor_set(v___x_5600_, 1, v_newHyps_5597_);
v___x_5601_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5596_, v_hypotheses_5595_, v_methods_5579_, v_config_5580_, v___x_5598_, v___x_5600_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_);
lean_dec_ref(v_hypotheses_5595_);
if (lean_obj_tag(v___x_5601_) == 0)
{
lean_object* v_a_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5631_; 
v_a_5602_ = lean_ctor_get(v___x_5601_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5601_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5604_ = v___x_5601_;
v_isShared_5605_ = v_isSharedCheck_5631_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_a_5602_);
lean_dec(v___x_5601_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5631_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v_fst_5606_; 
v_fst_5606_ = lean_ctor_get(v_a_5602_, 0);
if (lean_obj_tag(v_fst_5606_) == 0)
{
lean_object* v_snd_5607_; lean_object* v___x_5608_; lean_object* v_caches_5609_; lean_object* v_typeAnalysis_5610_; lean_object* v_target_5611_; uint8_t v_didChange_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5625_; 
v_snd_5607_ = lean_ctor_get(v_a_5602_, 1);
lean_inc(v_snd_5607_);
lean_dec(v_a_5602_);
v___x_5608_ = lean_st_ref_take(v_a_5583_);
v_caches_5609_ = lean_ctor_get(v___x_5608_, 0);
v_typeAnalysis_5610_ = lean_ctor_get(v___x_5608_, 1);
v_target_5611_ = lean_ctor_get(v___x_5608_, 2);
v_didChange_5612_ = lean_ctor_get_uint8(v___x_5608_, sizeof(void*)*4);
v_isSharedCheck_5625_ = !lean_is_exclusive(v___x_5608_);
if (v_isSharedCheck_5625_ == 0)
{
lean_object* v_unused_5626_; 
v_unused_5626_ = lean_ctor_get(v___x_5608_, 3);
lean_dec(v_unused_5626_);
v___x_5614_ = v___x_5608_;
v_isShared_5615_ = v_isSharedCheck_5625_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_target_5611_);
lean_inc(v_typeAnalysis_5610_);
lean_inc(v_caches_5609_);
lean_dec(v___x_5608_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5625_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
lean_ctor_set(v___x_5614_, 3, v_snd_5607_);
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_caches_5609_);
lean_ctor_set(v_reuseFailAlloc_5624_, 1, v_typeAnalysis_5610_);
lean_ctor_set(v_reuseFailAlloc_5624_, 2, v_target_5611_);
lean_ctor_set(v_reuseFailAlloc_5624_, 3, v_snd_5607_);
lean_ctor_set_uint8(v_reuseFailAlloc_5624_, sizeof(void*)*4, v_didChange_5612_);
v___x_5617_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
lean_object* v___x_5618_; uint8_t v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5622_; 
v___x_5618_ = lean_st_ref_put(v_a_5583_, v___x_5617_);
v___x_5619_ = 0;
v___x_5620_ = lean_box(v___x_5619_);
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 0, v___x_5620_);
v___x_5622_ = v___x_5604_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5620_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
else
{
lean_object* v_val_5627_; lean_object* v___x_5629_; 
lean_inc_ref(v_fst_5606_);
lean_dec(v_a_5602_);
v_val_5627_ = lean_ctor_get(v_fst_5606_, 0);
lean_inc(v_val_5627_);
lean_dec_ref_known(v_fst_5606_, 1);
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 0, v_val_5627_);
v___x_5629_ = v___x_5604_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_val_5627_);
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
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
v_a_5632_ = lean_ctor_get(v___x_5601_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5601_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5601_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5601_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5640_, lean_object* v_config_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_){
_start:
{
lean_object* v_res_5655_; 
v_res_5655_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5640_, v_config_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_);
lean_dec(v_a_5653_);
lean_dec_ref(v_a_5652_);
lean_dec(v_a_5651_);
lean_dec_ref(v_a_5650_);
lean_dec(v_a_5649_);
lean_dec_ref(v_a_5648_);
lean_dec(v_a_5647_);
lean_dec_ref(v_a_5646_);
lean_dec(v_a_5645_);
lean_dec(v_a_5644_);
lean_dec_ref(v_a_5643_);
lean_dec(v_a_5642_);
return v_res_5655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5656_, lean_object* v_msg_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_){
_start:
{
lean_object* v___x_5671_; 
v___x_5671_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5656_, v_msg_5657_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_);
return v___x_5671_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5672_, lean_object* v_msg_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_){
_start:
{
lean_object* v_res_5687_; 
v_res_5687_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5672_, v_msg_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec(v___y_5676_);
lean_dec_ref(v___y_5675_);
lean_dec(v___y_5674_);
return v_res_5687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5688_, lean_object* v___x_5689_, lean_object* v_methods_5690_, lean_object* v_config_5691_, lean_object* v_inst_5692_, lean_object* v_R_5693_, lean_object* v_a_5694_, lean_object* v_b_5695_, lean_object* v_c_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_){
_start:
{
lean_object* v___x_5710_; 
v___x_5710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5688_, v___x_5689_, v_methods_5690_, v_config_5691_, v_a_5694_, v_b_5695_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
return v___x_5710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5711_ = _args[0];
lean_object* v___x_5712_ = _args[1];
lean_object* v_methods_5713_ = _args[2];
lean_object* v_config_5714_ = _args[3];
lean_object* v_inst_5715_ = _args[4];
lean_object* v_R_5716_ = _args[5];
lean_object* v_a_5717_ = _args[6];
lean_object* v_b_5718_ = _args[7];
lean_object* v_c_5719_ = _args[8];
lean_object* v___y_5720_ = _args[9];
lean_object* v___y_5721_ = _args[10];
lean_object* v___y_5722_ = _args[11];
lean_object* v___y_5723_ = _args[12];
lean_object* v___y_5724_ = _args[13];
lean_object* v___y_5725_ = _args[14];
lean_object* v___y_5726_ = _args[15];
lean_object* v___y_5727_ = _args[16];
lean_object* v___y_5728_ = _args[17];
lean_object* v___y_5729_ = _args[18];
lean_object* v___y_5730_ = _args[19];
lean_object* v___y_5731_ = _args[20];
lean_object* v___y_5732_ = _args[21];
_start:
{
lean_object* v_res_5733_; 
v_res_5733_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5711_, v___x_5712_, v_methods_5713_, v_config_5714_, v_inst_5715_, v_R_5716_, v_a_5717_, v_b_5718_, v_c_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v___y_5726_);
lean_dec(v___y_5725_);
lean_dec_ref(v___y_5724_);
lean_dec(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec(v___y_5720_);
lean_dec_ref(v___x_5712_);
lean_dec(v_upperBound_5711_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5734_, lean_object* v_config_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_){
_start:
{
lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; 
v___x_5748_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5749_ = lean_st_mk_ref(v___x_5748_);
v___x_5750_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5734_, v_config_5735_, v___x_5749_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_);
if (lean_obj_tag(v___x_5750_) == 0)
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5759_; 
v_a_5751_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5759_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5759_ == 0)
{
v___x_5753_ = v___x_5750_;
v_isShared_5754_ = v_isSharedCheck_5759_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5750_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5759_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5755_; lean_object* v___x_5757_; 
v___x_5755_ = lean_st_ref_get(v___x_5749_);
lean_dec(v___x_5749_);
lean_dec(v___x_5755_);
if (v_isShared_5754_ == 0)
{
v___x_5757_ = v___x_5753_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_a_5751_);
v___x_5757_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
return v___x_5757_;
}
}
}
else
{
lean_dec(v___x_5749_);
return v___x_5750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5760_, lean_object* v_config_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_){
_start:
{
lean_object* v_res_5774_; 
v_res_5774_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5760_, v_config_5761_, v_a_5762_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_);
lean_dec(v_a_5772_);
lean_dec_ref(v_a_5771_);
lean_dec(v_a_5770_);
lean_dec_ref(v_a_5769_);
lean_dec(v_a_5768_);
lean_dec_ref(v_a_5767_);
lean_dec(v_a_5766_);
lean_dec_ref(v_a_5765_);
lean_dec(v_a_5764_);
lean_dec(v_a_5763_);
lean_dec_ref(v_a_5762_);
return v_res_5774_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5776_; lean_object* v___x_5777_; 
v___x_5776_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5777_ = l_Lean_stringToMessageData(v___x_5776_);
return v___x_5777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5778_, lean_object* v_x_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_){
_start:
{
lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5792_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5793_ = l_Lean_MessageData_ofName(v_name_5778_);
v___x_5794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5794_, 0, v___x_5792_);
lean_ctor_set(v___x_5794_, 1, v___x_5793_);
v___x_5795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5795_, 0, v___x_5794_);
return v___x_5795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5796_, lean_object* v_x_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_){
_start:
{
lean_object* v_res_5810_; 
v_res_5810_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5796_, v_x_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
lean_dec(v___y_5808_);
lean_dec_ref(v___y_5807_);
lean_dec(v___y_5806_);
lean_dec_ref(v___y_5805_);
lean_dec(v___y_5804_);
lean_dec_ref(v___y_5803_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
lean_dec(v___y_5800_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec_ref(v_x_5797_);
return v_res_5810_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5811_; 
v___x_5811_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_5811_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5812_; lean_object* v___x_5813_; 
v___x_5812_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5813_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5812_);
return v___x_5813_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5814_; lean_object* v___x_5815_; 
v___x_5814_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5815_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5814_);
return v___x_5815_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5816_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5817_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5816_);
return v___x_5817_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; 
v___x_5818_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5819_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5818_);
return v___x_5819_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5821_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5820_);
return v___x_5821_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5823_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5822_);
return v___x_5823_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5824_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5825_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5824_);
return v___x_5825_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5826_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5827_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5826_);
return v___x_5827_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5828_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5829_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5828_);
return v___x_5829_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; 
v___x_5830_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5831_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5830_);
return v___x_5831_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5833_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5832_);
return v___x_5833_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5835_; double v___x_5836_; 
v___x_5835_ = lean_unsigned_to_nat(1000000000u);
v___x_5836_ = lean_float_of_nat(v___x_5835_);
return v___x_5836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_){
_start:
{
lean_object* v___x_5850_; lean_object* v_toApplicative_5851_; lean_object* v_toFunctor_5852_; lean_object* v_toSeq_5853_; lean_object* v_toSeqLeft_5854_; lean_object* v_toSeqRight_5855_; lean_object* v___f_5856_; lean_object* v___f_5857_; lean_object* v___f_5858_; lean_object* v___f_5859_; lean_object* v___x_5860_; lean_object* v___f_5861_; lean_object* v___f_5862_; lean_object* v___f_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v_toApplicative_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_6009_; 
v___x_5850_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5851_ = lean_ctor_get(v___x_5850_, 0);
v_toFunctor_5852_ = lean_ctor_get(v_toApplicative_5851_, 0);
v_toSeq_5853_ = lean_ctor_get(v_toApplicative_5851_, 2);
v_toSeqLeft_5854_ = lean_ctor_get(v_toApplicative_5851_, 3);
v_toSeqRight_5855_ = lean_ctor_get(v_toApplicative_5851_, 4);
v___f_5856_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5857_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5852_, 2);
v___f_5858_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5858_, 0, v_toFunctor_5852_);
v___f_5859_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5859_, 0, v_toFunctor_5852_);
v___x_5860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5860_, 0, v___f_5858_);
lean_ctor_set(v___x_5860_, 1, v___f_5859_);
lean_inc(v_toSeqRight_5855_);
v___f_5861_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5861_, 0, v_toSeqRight_5855_);
lean_inc(v_toSeqLeft_5854_);
v___f_5862_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5862_, 0, v_toSeqLeft_5854_);
lean_inc(v_toSeq_5853_);
v___f_5863_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5863_, 0, v_toSeq_5853_);
v___x_5864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5860_);
lean_ctor_set(v___x_5864_, 1, v___f_5856_);
lean_ctor_set(v___x_5864_, 2, v___f_5863_);
lean_ctor_set(v___x_5864_, 3, v___f_5862_);
lean_ctor_set(v___x_5864_, 4, v___f_5861_);
v___x_5865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5864_);
lean_ctor_set(v___x_5865_, 1, v___f_5857_);
v___x_5866_ = l_StateRefT_x27_instMonad___redArg(v___x_5865_);
v_toApplicative_5867_ = lean_ctor_get(v___x_5866_, 0);
v_isSharedCheck_6009_ = !lean_is_exclusive(v___x_5866_);
if (v_isSharedCheck_6009_ == 0)
{
lean_object* v_unused_6010_; 
v_unused_6010_ = lean_ctor_get(v___x_5866_, 1);
lean_dec(v_unused_6010_);
v___x_5869_ = v___x_5866_;
v_isShared_5870_ = v_isSharedCheck_6009_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_toApplicative_5867_);
lean_dec(v___x_5866_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_6009_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
lean_object* v_toFunctor_5871_; lean_object* v_toSeq_5872_; lean_object* v_toSeqLeft_5873_; lean_object* v_toSeqRight_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_6007_; 
v_toFunctor_5871_ = lean_ctor_get(v_toApplicative_5867_, 0);
v_toSeq_5872_ = lean_ctor_get(v_toApplicative_5867_, 2);
v_toSeqLeft_5873_ = lean_ctor_get(v_toApplicative_5867_, 3);
v_toSeqRight_5874_ = lean_ctor_get(v_toApplicative_5867_, 4);
v_isSharedCheck_6007_ = !lean_is_exclusive(v_toApplicative_5867_);
if (v_isSharedCheck_6007_ == 0)
{
lean_object* v_unused_6008_; 
v_unused_6008_ = lean_ctor_get(v_toApplicative_5867_, 1);
lean_dec(v_unused_6008_);
v___x_5876_ = v_toApplicative_5867_;
v_isShared_5877_ = v_isSharedCheck_6007_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_toSeqRight_5874_);
lean_inc(v_toSeqLeft_5873_);
lean_inc(v_toSeq_5872_);
lean_inc(v_toFunctor_5871_);
lean_dec(v_toApplicative_5867_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_6007_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___f_5878_; lean_object* v___f_5879_; lean_object* v___f_5880_; lean_object* v___f_5881_; lean_object* v___x_5882_; lean_object* v___f_5883_; lean_object* v___f_5884_; lean_object* v___f_5885_; lean_object* v___x_5887_; 
v___f_5878_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5879_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5871_);
v___f_5880_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5880_, 0, v_toFunctor_5871_);
v___f_5881_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5881_, 0, v_toFunctor_5871_);
v___x_5882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5882_, 0, v___f_5880_);
lean_ctor_set(v___x_5882_, 1, v___f_5881_);
v___f_5883_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5883_, 0, v_toSeqRight_5874_);
v___f_5884_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5884_, 0, v_toSeqLeft_5873_);
v___f_5885_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5885_, 0, v_toSeq_5872_);
if (v_isShared_5877_ == 0)
{
lean_ctor_set(v___x_5876_, 4, v___f_5883_);
lean_ctor_set(v___x_5876_, 3, v___f_5884_);
lean_ctor_set(v___x_5876_, 2, v___f_5885_);
lean_ctor_set(v___x_5876_, 1, v___f_5878_);
lean_ctor_set(v___x_5876_, 0, v___x_5882_);
v___x_5887_ = v___x_5876_;
goto v_reusejp_5886_;
}
else
{
lean_object* v_reuseFailAlloc_6006_; 
v_reuseFailAlloc_6006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6006_, 0, v___x_5882_);
lean_ctor_set(v_reuseFailAlloc_6006_, 1, v___f_5878_);
lean_ctor_set(v_reuseFailAlloc_6006_, 2, v___f_5885_);
lean_ctor_set(v_reuseFailAlloc_6006_, 3, v___f_5884_);
lean_ctor_set(v_reuseFailAlloc_6006_, 4, v___f_5883_);
v___x_5887_ = v_reuseFailAlloc_6006_;
goto v_reusejp_5886_;
}
v_reusejp_5886_:
{
lean_object* v___x_5889_; 
if (v_isShared_5870_ == 0)
{
lean_ctor_set(v___x_5869_, 1, v___f_5879_);
lean_ctor_set(v___x_5869_, 0, v___x_5887_);
v___x_5889_ = v___x_5869_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_6005_; 
v_reuseFailAlloc_6005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6005_, 0, v___x_5887_);
lean_ctor_set(v_reuseFailAlloc_6005_, 1, v___f_5879_);
v___x_5889_ = v_reuseFailAlloc_6005_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v_toMonadRef_5899_; lean_object* v___x_5900_; lean_object* v_name_5901_; lean_object* v_run_x27_5902_; lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_6004_; 
v___x_5890_ = l_StateRefT_x27_instMonad___redArg(v___x_5889_);
v___x_5891_ = l_ReaderT_instMonad___redArg(v___x_5890_);
v___x_5892_ = l_StateRefT_x27_instMonad___redArg(v___x_5891_);
v___x_5893_ = l_ReaderT_instMonad___redArg(v___x_5892_);
v___x_5894_ = l_ReaderT_instMonad___redArg(v___x_5893_);
v___x_5895_ = l_StateRefT_x27_instMonad___redArg(v___x_5894_);
v___x_5896_ = l_ReaderT_instMonad___redArg(v___x_5895_);
v___x_5897_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5898_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_5899_ = lean_ctor_get(v___x_5898_, 0);
v___x_5900_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_name_5901_ = lean_ctor_get(v_pass_5837_, 0);
v_run_x27_5902_ = lean_ctor_get(v_pass_5837_, 1);
v_isSharedCheck_6004_ = !lean_is_exclusive(v_pass_5837_);
if (v_isSharedCheck_6004_ == 0)
{
v___x_5904_ = v_pass_5837_;
v_isShared_5905_ = v_isSharedCheck_6004_;
goto v_resetjp_5903_;
}
else
{
lean_inc(v_run_x27_5902_);
lean_inc(v_name_5901_);
lean_dec(v_pass_5837_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_6004_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v___x_5906_; lean_object* v_options_5907_; uint8_t v_hasTrace_5908_; 
v___x_5906_ = l_Lean_KVMap_instValueBool;
v_options_5907_ = lean_ctor_get(v_a_5847_, 2);
v_hasTrace_5908_ = lean_ctor_get_uint8(v_options_5907_, sizeof(void*)*1);
if (v_hasTrace_5908_ == 0)
{
lean_object* v___x_5909_; 
lean_del_object(v___x_5904_);
lean_dec(v_name_5901_);
lean_dec_ref(v___x_5896_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc_ref(v_a_5843_);
lean_inc(v_a_5842_);
lean_inc_ref(v_a_5841_);
lean_inc(v_a_5840_);
lean_inc(v_a_5839_);
lean_inc_ref(v_a_5838_);
v___x_5909_ = lean_apply_12(v_run_x27_5902_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, lean_box(0));
return v___x_5909_;
}
else
{
lean_object* v_inheritedTraceOptions_5910_; lean_object* v___f_5911_; lean_object* v___f_5912_; lean_object* v___f_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; uint8_t v___x_5917_; lean_object* v___y_5919_; lean_object* v___y_5920_; lean_object* v_a_5921_; lean_object* v___y_5937_; lean_object* v___y_5938_; lean_object* v_a_5939_; 
v_inheritedTraceOptions_5910_ = lean_ctor_get(v_a_5847_, 13);
v___f_5911_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5911_, 0, v_name_5901_);
v___f_5912_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_5913_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5914_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5915_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5916_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5910_, v_options_5907_, v___x_5916_);
if (v___x_5917_ == 0)
{
lean_object* v___x_6000_; lean_object* v___x_6001_; uint8_t v___x_6002_; 
v___x_6000_ = l_Lean_trace_profiler;
v___x_6001_ = l_Lean_Option_get___redArg(v___x_5906_, v_options_5907_, v___x_6000_);
v___x_6002_ = lean_unbox(v___x_6001_);
lean_dec(v___x_6001_);
if (v___x_6002_ == 0)
{
lean_object* v___x_6003_; 
lean_dec_ref(v___f_5911_);
lean_del_object(v___x_5904_);
lean_dec_ref(v___x_5896_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc_ref(v_a_5843_);
lean_inc(v_a_5842_);
lean_inc_ref(v_a_5841_);
lean_inc(v_a_5840_);
lean_inc(v_a_5839_);
lean_inc_ref(v_a_5838_);
v___x_6003_ = lean_apply_12(v_run_x27_5902_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, lean_box(0));
return v___x_6003_;
}
else
{
goto v___jp_5949_;
}
}
else
{
goto v___jp_5949_;
}
v___jp_5918_:
{
lean_object* v___x_5922_; double v___x_5923_; double v___x_5924_; double v___x_5925_; double v___x_5926_; double v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5931_; 
v___x_5922_ = lean_io_mono_nanos_now();
v___x_5923_ = lean_float_of_nat(v___y_5919_);
v___x_5924_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5925_ = lean_float_div(v___x_5923_, v___x_5924_);
v___x_5926_ = lean_float_of_nat(v___x_5922_);
v___x_5927_ = lean_float_div(v___x_5926_, v___x_5924_);
v___x_5928_ = lean_box_float(v___x_5925_);
v___x_5929_ = lean_box_float(v___x_5927_);
if (v_isShared_5905_ == 0)
{
lean_ctor_set(v___x_5904_, 1, v___x_5929_);
lean_ctor_set(v___x_5904_, 0, v___x_5928_);
v___x_5931_ = v___x_5904_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v___x_5928_);
lean_ctor_set(v_reuseFailAlloc_5935_, 1, v___x_5929_);
v___x_5931_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
lean_object* v___x_5932_; lean_object* v___x_28807__overap_5933_; lean_object* v___x_5934_; 
v___x_5932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5932_, 0, v_a_5921_);
lean_ctor_set(v___x_5932_, 1, v___x_5931_);
lean_inc_ref(v_toMonadRef_5899_);
v___x_28807__overap_5933_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5896_, v___x_5897_, v_toMonadRef_5899_, v___f_5912_, lean_box(0), v___x_5900_, v___f_5913_, v___x_5914_, v_hasTrace_5908_, v___x_5915_, v_options_5907_, v___x_5917_, v___y_5920_, v___f_5911_, v___x_5932_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc_ref(v_a_5843_);
lean_inc(v_a_5842_);
lean_inc_ref(v_a_5841_);
lean_inc(v_a_5840_);
lean_inc(v_a_5839_);
lean_inc_ref(v_a_5838_);
v___x_5934_ = lean_apply_12(v___x_28807__overap_5933_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, lean_box(0));
return v___x_5934_;
}
}
v___jp_5936_:
{
lean_object* v___x_5940_; double v___x_5941_; double v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_28828__overap_5947_; lean_object* v___x_5948_; 
v___x_5940_ = lean_io_get_num_heartbeats();
v___x_5941_ = lean_float_of_nat(v___y_5938_);
v___x_5942_ = lean_float_of_nat(v___x_5940_);
v___x_5943_ = lean_box_float(v___x_5941_);
v___x_5944_ = lean_box_float(v___x_5942_);
v___x_5945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5943_);
lean_ctor_set(v___x_5945_, 1, v___x_5944_);
v___x_5946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5946_, 0, v_a_5939_);
lean_ctor_set(v___x_5946_, 1, v___x_5945_);
lean_inc_ref(v_toMonadRef_5899_);
v___x_28828__overap_5947_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5896_, v___x_5897_, v_toMonadRef_5899_, v___f_5912_, lean_box(0), v___x_5900_, v___f_5913_, v___x_5914_, v_hasTrace_5908_, v___x_5915_, v_options_5907_, v___x_5917_, v___y_5937_, v___f_5911_, v___x_5946_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc_ref(v_a_5843_);
lean_inc(v_a_5842_);
lean_inc_ref(v_a_5841_);
lean_inc(v_a_5840_);
lean_inc(v_a_5839_);
lean_inc_ref(v_a_5838_);
v___x_5948_ = lean_apply_12(v___x_28828__overap_5947_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, lean_box(0));
return v___x_5948_;
}
v___jp_5949_:
{
lean_object* v___x_28785__overap_5950_; lean_object* v___x_5951_; 
lean_inc_ref(v___x_5896_);
v___x_28785__overap_5950_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5896_, v___x_5897_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc_ref(v_a_5843_);
lean_inc(v_a_5842_);
lean_inc_ref(v_a_5841_);
lean_inc(v_a_5840_);
lean_inc(v_a_5839_);
lean_inc_ref(v_a_5838_);
v___x_5951_ = lean_apply_12(v___x_28785__overap_5950_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, lean_box(0));
if (lean_obj_tag(v___x_5951_) == 0)
{
lean_object* v_a_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; uint8_t v___x_5955_; 
v_a_5952_ = lean_ctor_get(v___x_5951_, 0);
lean_inc(v_a_5952_);
lean_dec_ref_known(v___x_5951_, 1);
v___x_5953_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5954_ = l_Lean_Option_get___redArg(v___x_5906_, v_options_5907_, v___x_5953_);
v___x_5955_ = lean_unbox(v___x_5954_);
lean_dec(v___x_5954_);
if (v___x_5955_ == 0)
{
lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5956_ = lean_io_mono_nanos_now();
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc_ref(v_a_5843_);
lean_inc(v_a_5842_);
lean_inc_ref(v_a_5841_);
lean_inc(v_a_5840_);
lean_inc(v_a_5839_);
lean_inc_ref(v_a_5838_);
v___x_5957_ = lean_apply_12(v_run_x27_5902_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, lean_box(0));
if (lean_obj_tag(v___x_5957_) == 0)
{
lean_object* v_a_5958_; lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_5965_; 
v_a_5958_ = lean_ctor_get(v___x_5957_, 0);
v_isSharedCheck_5965_ = !lean_is_exclusive(v___x_5957_);
if (v_isSharedCheck_5965_ == 0)
{
v___x_5960_ = v___x_5957_;
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
else
{
lean_inc(v_a_5958_);
lean_dec(v___x_5957_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v___x_5963_; 
if (v_isShared_5961_ == 0)
{
lean_ctor_set_tag(v___x_5960_, 1);
v___x_5963_ = v___x_5960_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5964_; 
v_reuseFailAlloc_5964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5964_, 0, v_a_5958_);
v___x_5963_ = v_reuseFailAlloc_5964_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
v___y_5919_ = v___x_5956_;
v___y_5920_ = v_a_5952_;
v_a_5921_ = v___x_5963_;
goto v___jp_5918_;
}
}
}
else
{
lean_object* v_a_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5973_; 
v_a_5966_ = lean_ctor_get(v___x_5957_, 0);
v_isSharedCheck_5973_ = !lean_is_exclusive(v___x_5957_);
if (v_isSharedCheck_5973_ == 0)
{
v___x_5968_ = v___x_5957_;
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_a_5966_);
lean_dec(v___x_5957_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5971_; 
if (v_isShared_5969_ == 0)
{
lean_ctor_set_tag(v___x_5968_, 0);
v___x_5971_ = v___x_5968_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_a_5966_);
v___x_5971_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
v___y_5919_ = v___x_5956_;
v___y_5920_ = v_a_5952_;
v_a_5921_ = v___x_5971_;
goto v___jp_5918_;
}
}
}
}
else
{
lean_object* v___x_5974_; lean_object* v___x_5975_; 
lean_del_object(v___x_5904_);
v___x_5974_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc_ref(v_a_5843_);
lean_inc(v_a_5842_);
lean_inc_ref(v_a_5841_);
lean_inc(v_a_5840_);
lean_inc(v_a_5839_);
lean_inc_ref(v_a_5838_);
v___x_5975_ = lean_apply_12(v_run_x27_5902_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, lean_box(0));
if (lean_obj_tag(v___x_5975_) == 0)
{
lean_object* v_a_5976_; lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_5983_; 
v_a_5976_ = lean_ctor_get(v___x_5975_, 0);
v_isSharedCheck_5983_ = !lean_is_exclusive(v___x_5975_);
if (v_isSharedCheck_5983_ == 0)
{
v___x_5978_ = v___x_5975_;
v_isShared_5979_ = v_isSharedCheck_5983_;
goto v_resetjp_5977_;
}
else
{
lean_inc(v_a_5976_);
lean_dec(v___x_5975_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_5983_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5981_; 
if (v_isShared_5979_ == 0)
{
lean_ctor_set_tag(v___x_5978_, 1);
v___x_5981_ = v___x_5978_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_a_5976_);
v___x_5981_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
v___y_5937_ = v_a_5952_;
v___y_5938_ = v___x_5974_;
v_a_5939_ = v___x_5981_;
goto v___jp_5936_;
}
}
}
else
{
lean_object* v_a_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5991_; 
v_a_5984_ = lean_ctor_get(v___x_5975_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v___x_5975_);
if (v_isSharedCheck_5991_ == 0)
{
v___x_5986_ = v___x_5975_;
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_a_5984_);
lean_dec(v___x_5975_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5989_; 
if (v_isShared_5987_ == 0)
{
lean_ctor_set_tag(v___x_5986_, 0);
v___x_5989_ = v___x_5986_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
v___x_5989_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
v___y_5937_ = v_a_5952_;
v___y_5938_ = v___x_5974_;
v_a_5939_ = v___x_5989_;
goto v___jp_5936_;
}
}
}
}
}
else
{
lean_object* v_a_5992_; lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_5999_; 
lean_dec_ref(v___f_5911_);
lean_del_object(v___x_5904_);
lean_dec_ref(v_run_x27_5902_);
lean_dec_ref(v___x_5896_);
v_a_5992_ = lean_ctor_get(v___x_5951_, 0);
v_isSharedCheck_5999_ = !lean_is_exclusive(v___x_5951_);
if (v_isSharedCheck_5999_ == 0)
{
v___x_5994_ = v___x_5951_;
v_isShared_5995_ = v_isSharedCheck_5999_;
goto v_resetjp_5993_;
}
else
{
lean_inc(v_a_5992_);
lean_dec(v___x_5951_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_5999_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
lean_object* v___x_5997_; 
if (v_isShared_5995_ == 0)
{
v___x_5997_ = v___x_5994_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_5998_; 
v_reuseFailAlloc_5998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_a_5992_);
v___x_5997_ = v_reuseFailAlloc_5998_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
return v___x_5997_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_, lean_object* v_a_6014_, lean_object* v_a_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_){
_start:
{
lean_object* v_res_6024_; 
v_res_6024_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6011_, v_a_6012_, v_a_6013_, v_a_6014_, v_a_6015_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_);
lean_dec(v_a_6022_);
lean_dec_ref(v_a_6021_);
lean_dec(v_a_6020_);
lean_dec_ref(v_a_6019_);
lean_dec(v_a_6018_);
lean_dec_ref(v_a_6017_);
lean_dec(v_a_6016_);
lean_dec_ref(v_a_6015_);
lean_dec(v_a_6014_);
lean_dec(v_a_6013_);
lean_dec_ref(v_a_6012_);
return v_res_6024_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; 
v___x_6025_ = lean_unsigned_to_nat(32u);
v___x_6026_ = lean_mk_empty_array_with_capacity(v___x_6025_);
v___x_6027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
return v___x_6027_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; 
v___x_6028_ = ((size_t)5ULL);
v___x_6029_ = lean_unsigned_to_nat(0u);
v___x_6030_ = lean_unsigned_to_nat(32u);
v___x_6031_ = lean_mk_empty_array_with_capacity(v___x_6030_);
v___x_6032_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6033_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6033_, 0, v___x_6032_);
lean_ctor_set(v___x_6033_, 1, v___x_6031_);
lean_ctor_set(v___x_6033_, 2, v___x_6029_);
lean_ctor_set(v___x_6033_, 3, v___x_6029_);
lean_ctor_set_usize(v___x_6033_, 4, v___x_6028_);
return v___x_6033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6034_){
_start:
{
lean_object* v___x_6036_; lean_object* v_traceState_6037_; lean_object* v_traces_6038_; lean_object* v___x_6039_; lean_object* v_traceState_6040_; lean_object* v_env_6041_; lean_object* v_nextMacroScope_6042_; lean_object* v_ngen_6043_; lean_object* v_auxDeclNGen_6044_; lean_object* v_cache_6045_; lean_object* v_messages_6046_; lean_object* v_infoState_6047_; lean_object* v_snapshotTasks_6048_; lean_object* v___x_6050_; uint8_t v_isShared_6051_; uint8_t v_isSharedCheck_6067_; 
v___x_6036_ = lean_st_ref_get(v___y_6034_);
v_traceState_6037_ = lean_ctor_get(v___x_6036_, 4);
lean_inc_ref(v_traceState_6037_);
lean_dec(v___x_6036_);
v_traces_6038_ = lean_ctor_get(v_traceState_6037_, 0);
lean_inc_ref(v_traces_6038_);
lean_dec_ref(v_traceState_6037_);
v___x_6039_ = lean_st_ref_take(v___y_6034_);
v_traceState_6040_ = lean_ctor_get(v___x_6039_, 4);
v_env_6041_ = lean_ctor_get(v___x_6039_, 0);
v_nextMacroScope_6042_ = lean_ctor_get(v___x_6039_, 1);
v_ngen_6043_ = lean_ctor_get(v___x_6039_, 2);
v_auxDeclNGen_6044_ = lean_ctor_get(v___x_6039_, 3);
v_cache_6045_ = lean_ctor_get(v___x_6039_, 5);
v_messages_6046_ = lean_ctor_get(v___x_6039_, 6);
v_infoState_6047_ = lean_ctor_get(v___x_6039_, 7);
v_snapshotTasks_6048_ = lean_ctor_get(v___x_6039_, 8);
v_isSharedCheck_6067_ = !lean_is_exclusive(v___x_6039_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_6050_ = v___x_6039_;
v_isShared_6051_ = v_isSharedCheck_6067_;
goto v_resetjp_6049_;
}
else
{
lean_inc(v_snapshotTasks_6048_);
lean_inc(v_infoState_6047_);
lean_inc(v_messages_6046_);
lean_inc(v_cache_6045_);
lean_inc(v_traceState_6040_);
lean_inc(v_auxDeclNGen_6044_);
lean_inc(v_ngen_6043_);
lean_inc(v_nextMacroScope_6042_);
lean_inc(v_env_6041_);
lean_dec(v___x_6039_);
v___x_6050_ = lean_box(0);
v_isShared_6051_ = v_isSharedCheck_6067_;
goto v_resetjp_6049_;
}
v_resetjp_6049_:
{
uint64_t v_tid_6052_; lean_object* v___x_6054_; uint8_t v_isShared_6055_; uint8_t v_isSharedCheck_6065_; 
v_tid_6052_ = lean_ctor_get_uint64(v_traceState_6040_, sizeof(void*)*1);
v_isSharedCheck_6065_ = !lean_is_exclusive(v_traceState_6040_);
if (v_isSharedCheck_6065_ == 0)
{
lean_object* v_unused_6066_; 
v_unused_6066_ = lean_ctor_get(v_traceState_6040_, 0);
lean_dec(v_unused_6066_);
v___x_6054_ = v_traceState_6040_;
v_isShared_6055_ = v_isSharedCheck_6065_;
goto v_resetjp_6053_;
}
else
{
lean_dec(v_traceState_6040_);
v___x_6054_ = lean_box(0);
v_isShared_6055_ = v_isSharedCheck_6065_;
goto v_resetjp_6053_;
}
v_resetjp_6053_:
{
lean_object* v___x_6056_; lean_object* v___x_6058_; 
v___x_6056_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6055_ == 0)
{
lean_ctor_set(v___x_6054_, 0, v___x_6056_);
v___x_6058_ = v___x_6054_;
goto v_reusejp_6057_;
}
else
{
lean_object* v_reuseFailAlloc_6064_; 
v_reuseFailAlloc_6064_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6064_, 0, v___x_6056_);
lean_ctor_set_uint64(v_reuseFailAlloc_6064_, sizeof(void*)*1, v_tid_6052_);
v___x_6058_ = v_reuseFailAlloc_6064_;
goto v_reusejp_6057_;
}
v_reusejp_6057_:
{
lean_object* v___x_6060_; 
if (v_isShared_6051_ == 0)
{
lean_ctor_set(v___x_6050_, 4, v___x_6058_);
v___x_6060_ = v___x_6050_;
goto v_reusejp_6059_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v_env_6041_);
lean_ctor_set(v_reuseFailAlloc_6063_, 1, v_nextMacroScope_6042_);
lean_ctor_set(v_reuseFailAlloc_6063_, 2, v_ngen_6043_);
lean_ctor_set(v_reuseFailAlloc_6063_, 3, v_auxDeclNGen_6044_);
lean_ctor_set(v_reuseFailAlloc_6063_, 4, v___x_6058_);
lean_ctor_set(v_reuseFailAlloc_6063_, 5, v_cache_6045_);
lean_ctor_set(v_reuseFailAlloc_6063_, 6, v_messages_6046_);
lean_ctor_set(v_reuseFailAlloc_6063_, 7, v_infoState_6047_);
lean_ctor_set(v_reuseFailAlloc_6063_, 8, v_snapshotTasks_6048_);
v___x_6060_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6059_;
}
v_reusejp_6059_:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6061_ = lean_st_ref_put(v___y_6034_, v___x_6060_);
v___x_6062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6062_, 0, v_traces_6038_);
return v___x_6062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6068_, lean_object* v___y_6069_){
_start:
{
lean_object* v_res_6070_; 
v_res_6070_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6068_);
lean_dec(v___y_6068_);
return v_res_6070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_){
_start:
{
lean_object* v___x_6083_; 
v___x_6083_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6081_);
return v___x_6083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_){
_start:
{
lean_object* v_res_6096_; 
v_res_6096_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_);
lean_dec(v___y_6094_);
lean_dec_ref(v___y_6093_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec(v___y_6088_);
lean_dec_ref(v___y_6087_);
lean_dec(v___y_6086_);
lean_dec(v___y_6085_);
lean_dec_ref(v___y_6084_);
return v_res_6096_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6097_, lean_object* v_opt_6098_){
_start:
{
lean_object* v_name_6099_; lean_object* v_defValue_6100_; lean_object* v_map_6101_; lean_object* v___x_6102_; 
v_name_6099_ = lean_ctor_get(v_opt_6098_, 0);
v_defValue_6100_ = lean_ctor_get(v_opt_6098_, 1);
v_map_6101_ = lean_ctor_get(v_opts_6097_, 0);
v___x_6102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6101_, v_name_6099_);
if (lean_obj_tag(v___x_6102_) == 0)
{
uint8_t v___x_6103_; 
v___x_6103_ = lean_unbox(v_defValue_6100_);
return v___x_6103_;
}
else
{
lean_object* v_val_6104_; 
v_val_6104_ = lean_ctor_get(v___x_6102_, 0);
lean_inc(v_val_6104_);
lean_dec_ref_known(v___x_6102_, 1);
if (lean_obj_tag(v_val_6104_) == 1)
{
uint8_t v_v_6105_; 
v_v_6105_ = lean_ctor_get_uint8(v_val_6104_, 0);
lean_dec_ref_known(v_val_6104_, 0);
return v_v_6105_;
}
else
{
uint8_t v___x_6106_; 
lean_dec(v_val_6104_);
v___x_6106_ = lean_unbox(v_defValue_6100_);
return v___x_6106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6107_, lean_object* v_opt_6108_){
_start:
{
uint8_t v_res_6109_; lean_object* v_r_6110_; 
v_res_6109_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6107_, v_opt_6108_);
lean_dec_ref(v_opt_6108_);
lean_dec_ref(v_opts_6107_);
v_r_6110_ = lean_box(v_res_6109_);
return v_r_6110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6111_, lean_object* v_msg_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_){
_start:
{
lean_object* v_ref_6118_; lean_object* v___x_6119_; lean_object* v_a_6120_; lean_object* v___x_6122_; uint8_t v_isShared_6123_; uint8_t v_isSharedCheck_6164_; 
v_ref_6118_ = lean_ctor_get(v___y_6115_, 5);
v___x_6119_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_);
v_a_6120_ = lean_ctor_get(v___x_6119_, 0);
v_isSharedCheck_6164_ = !lean_is_exclusive(v___x_6119_);
if (v_isSharedCheck_6164_ == 0)
{
v___x_6122_ = v___x_6119_;
v_isShared_6123_ = v_isSharedCheck_6164_;
goto v_resetjp_6121_;
}
else
{
lean_inc(v_a_6120_);
lean_dec(v___x_6119_);
v___x_6122_ = lean_box(0);
v_isShared_6123_ = v_isSharedCheck_6164_;
goto v_resetjp_6121_;
}
v_resetjp_6121_:
{
lean_object* v___x_6124_; lean_object* v_traceState_6125_; lean_object* v_env_6126_; lean_object* v_nextMacroScope_6127_; lean_object* v_ngen_6128_; lean_object* v_auxDeclNGen_6129_; lean_object* v_cache_6130_; lean_object* v_messages_6131_; lean_object* v_infoState_6132_; lean_object* v_snapshotTasks_6133_; lean_object* v___x_6135_; uint8_t v_isShared_6136_; uint8_t v_isSharedCheck_6163_; 
v___x_6124_ = lean_st_ref_take(v___y_6116_);
v_traceState_6125_ = lean_ctor_get(v___x_6124_, 4);
v_env_6126_ = lean_ctor_get(v___x_6124_, 0);
v_nextMacroScope_6127_ = lean_ctor_get(v___x_6124_, 1);
v_ngen_6128_ = lean_ctor_get(v___x_6124_, 2);
v_auxDeclNGen_6129_ = lean_ctor_get(v___x_6124_, 3);
v_cache_6130_ = lean_ctor_get(v___x_6124_, 5);
v_messages_6131_ = lean_ctor_get(v___x_6124_, 6);
v_infoState_6132_ = lean_ctor_get(v___x_6124_, 7);
v_snapshotTasks_6133_ = lean_ctor_get(v___x_6124_, 8);
v_isSharedCheck_6163_ = !lean_is_exclusive(v___x_6124_);
if (v_isSharedCheck_6163_ == 0)
{
v___x_6135_ = v___x_6124_;
v_isShared_6136_ = v_isSharedCheck_6163_;
goto v_resetjp_6134_;
}
else
{
lean_inc(v_snapshotTasks_6133_);
lean_inc(v_infoState_6132_);
lean_inc(v_messages_6131_);
lean_inc(v_cache_6130_);
lean_inc(v_traceState_6125_);
lean_inc(v_auxDeclNGen_6129_);
lean_inc(v_ngen_6128_);
lean_inc(v_nextMacroScope_6127_);
lean_inc(v_env_6126_);
lean_dec(v___x_6124_);
v___x_6135_ = lean_box(0);
v_isShared_6136_ = v_isSharedCheck_6163_;
goto v_resetjp_6134_;
}
v_resetjp_6134_:
{
uint64_t v_tid_6137_; lean_object* v_traces_6138_; lean_object* v___x_6140_; uint8_t v_isShared_6141_; uint8_t v_isSharedCheck_6162_; 
v_tid_6137_ = lean_ctor_get_uint64(v_traceState_6125_, sizeof(void*)*1);
v_traces_6138_ = lean_ctor_get(v_traceState_6125_, 0);
v_isSharedCheck_6162_ = !lean_is_exclusive(v_traceState_6125_);
if (v_isSharedCheck_6162_ == 0)
{
v___x_6140_ = v_traceState_6125_;
v_isShared_6141_ = v_isSharedCheck_6162_;
goto v_resetjp_6139_;
}
else
{
lean_inc(v_traces_6138_);
lean_dec(v_traceState_6125_);
v___x_6140_ = lean_box(0);
v_isShared_6141_ = v_isSharedCheck_6162_;
goto v_resetjp_6139_;
}
v_resetjp_6139_:
{
lean_object* v___x_6142_; double v___x_6143_; uint8_t v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6152_; 
v___x_6142_ = lean_box(0);
v___x_6143_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6144_ = 0;
v___x_6145_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6146_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6146_, 0, v_cls_6111_);
lean_ctor_set(v___x_6146_, 1, v___x_6142_);
lean_ctor_set(v___x_6146_, 2, v___x_6145_);
lean_ctor_set_float(v___x_6146_, sizeof(void*)*3, v___x_6143_);
lean_ctor_set_float(v___x_6146_, sizeof(void*)*3 + 8, v___x_6143_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*3 + 16, v___x_6144_);
v___x_6147_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6148_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6146_);
lean_ctor_set(v___x_6148_, 1, v_a_6120_);
lean_ctor_set(v___x_6148_, 2, v___x_6147_);
lean_inc(v_ref_6118_);
v___x_6149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6149_, 0, v_ref_6118_);
lean_ctor_set(v___x_6149_, 1, v___x_6148_);
v___x_6150_ = l_Lean_PersistentArray_push___redArg(v_traces_6138_, v___x_6149_);
if (v_isShared_6141_ == 0)
{
lean_ctor_set(v___x_6140_, 0, v___x_6150_);
v___x_6152_ = v___x_6140_;
goto v_reusejp_6151_;
}
else
{
lean_object* v_reuseFailAlloc_6161_; 
v_reuseFailAlloc_6161_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6161_, 0, v___x_6150_);
lean_ctor_set_uint64(v_reuseFailAlloc_6161_, sizeof(void*)*1, v_tid_6137_);
v___x_6152_ = v_reuseFailAlloc_6161_;
goto v_reusejp_6151_;
}
v_reusejp_6151_:
{
lean_object* v___x_6154_; 
if (v_isShared_6136_ == 0)
{
lean_ctor_set(v___x_6135_, 4, v___x_6152_);
v___x_6154_ = v___x_6135_;
goto v_reusejp_6153_;
}
else
{
lean_object* v_reuseFailAlloc_6160_; 
v_reuseFailAlloc_6160_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6160_, 0, v_env_6126_);
lean_ctor_set(v_reuseFailAlloc_6160_, 1, v_nextMacroScope_6127_);
lean_ctor_set(v_reuseFailAlloc_6160_, 2, v_ngen_6128_);
lean_ctor_set(v_reuseFailAlloc_6160_, 3, v_auxDeclNGen_6129_);
lean_ctor_set(v_reuseFailAlloc_6160_, 4, v___x_6152_);
lean_ctor_set(v_reuseFailAlloc_6160_, 5, v_cache_6130_);
lean_ctor_set(v_reuseFailAlloc_6160_, 6, v_messages_6131_);
lean_ctor_set(v_reuseFailAlloc_6160_, 7, v_infoState_6132_);
lean_ctor_set(v_reuseFailAlloc_6160_, 8, v_snapshotTasks_6133_);
v___x_6154_ = v_reuseFailAlloc_6160_;
goto v_reusejp_6153_;
}
v_reusejp_6153_:
{
lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6158_; 
v___x_6155_ = lean_st_ref_put(v___y_6116_, v___x_6154_);
v___x_6156_ = lean_box(0);
if (v_isShared_6123_ == 0)
{
lean_ctor_set(v___x_6122_, 0, v___x_6156_);
v___x_6158_ = v___x_6122_;
goto v_reusejp_6157_;
}
else
{
lean_object* v_reuseFailAlloc_6159_; 
v_reuseFailAlloc_6159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6159_, 0, v___x_6156_);
v___x_6158_ = v_reuseFailAlloc_6159_;
goto v_reusejp_6157_;
}
v_reusejp_6157_:
{
return v___x_6158_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6165_, lean_object* v_msg_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_){
_start:
{
lean_object* v_res_6172_; 
v_res_6172_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6165_, v_msg_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_);
lean_dec(v___y_6170_);
lean_dec_ref(v___y_6169_);
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
return v_res_6172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6173_){
_start:
{
if (lean_obj_tag(v_e_6173_) == 0)
{
uint8_t v___x_6174_; 
v___x_6174_ = 2;
return v___x_6174_;
}
else
{
lean_object* v_a_6175_; uint8_t v___x_6176_; 
v_a_6175_ = lean_ctor_get(v_e_6173_, 0);
v___x_6176_ = lean_unbox(v_a_6175_);
if (v___x_6176_ == 0)
{
uint8_t v___x_6177_; 
v___x_6177_ = 1;
return v___x_6177_;
}
else
{
uint8_t v___x_6178_; 
v___x_6178_ = 0;
return v___x_6178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6179_){
_start:
{
uint8_t v_res_6180_; lean_object* v_r_6181_; 
v_res_6180_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6179_);
lean_dec_ref(v_e_6179_);
v_r_6181_ = lean_box(v_res_6180_);
return v_r_6181_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6182_){
_start:
{
if (lean_obj_tag(v_x_6182_) == 0)
{
lean_object* v_a_6184_; lean_object* v___x_6186_; uint8_t v_isShared_6187_; uint8_t v_isSharedCheck_6191_; 
v_a_6184_ = lean_ctor_get(v_x_6182_, 0);
v_isSharedCheck_6191_ = !lean_is_exclusive(v_x_6182_);
if (v_isSharedCheck_6191_ == 0)
{
v___x_6186_ = v_x_6182_;
v_isShared_6187_ = v_isSharedCheck_6191_;
goto v_resetjp_6185_;
}
else
{
lean_inc(v_a_6184_);
lean_dec(v_x_6182_);
v___x_6186_ = lean_box(0);
v_isShared_6187_ = v_isSharedCheck_6191_;
goto v_resetjp_6185_;
}
v_resetjp_6185_:
{
lean_object* v___x_6189_; 
if (v_isShared_6187_ == 0)
{
lean_ctor_set_tag(v___x_6186_, 1);
v___x_6189_ = v___x_6186_;
goto v_reusejp_6188_;
}
else
{
lean_object* v_reuseFailAlloc_6190_; 
v_reuseFailAlloc_6190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6190_, 0, v_a_6184_);
v___x_6189_ = v_reuseFailAlloc_6190_;
goto v_reusejp_6188_;
}
v_reusejp_6188_:
{
return v___x_6189_;
}
}
}
else
{
lean_object* v_a_6192_; lean_object* v___x_6194_; uint8_t v_isShared_6195_; uint8_t v_isSharedCheck_6199_; 
v_a_6192_ = lean_ctor_get(v_x_6182_, 0);
v_isSharedCheck_6199_ = !lean_is_exclusive(v_x_6182_);
if (v_isSharedCheck_6199_ == 0)
{
v___x_6194_ = v_x_6182_;
v_isShared_6195_ = v_isSharedCheck_6199_;
goto v_resetjp_6193_;
}
else
{
lean_inc(v_a_6192_);
lean_dec(v_x_6182_);
v___x_6194_ = lean_box(0);
v_isShared_6195_ = v_isSharedCheck_6199_;
goto v_resetjp_6193_;
}
v_resetjp_6193_:
{
lean_object* v___x_6197_; 
if (v_isShared_6195_ == 0)
{
lean_ctor_set_tag(v___x_6194_, 0);
v___x_6197_ = v___x_6194_;
goto v_reusejp_6196_;
}
else
{
lean_object* v_reuseFailAlloc_6198_; 
v_reuseFailAlloc_6198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_a_6192_);
v___x_6197_ = v_reuseFailAlloc_6198_;
goto v_reusejp_6196_;
}
v_reusejp_6196_:
{
return v___x_6197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6200_, lean_object* v___y_6201_){
_start:
{
lean_object* v_res_6202_; 
v_res_6202_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6200_);
return v_res_6202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6203_, lean_object* v_opt_6204_){
_start:
{
lean_object* v_name_6205_; lean_object* v_defValue_6206_; lean_object* v_map_6207_; lean_object* v___x_6208_; 
v_name_6205_ = lean_ctor_get(v_opt_6204_, 0);
v_defValue_6206_ = lean_ctor_get(v_opt_6204_, 1);
v_map_6207_ = lean_ctor_get(v_opts_6203_, 0);
v___x_6208_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6207_, v_name_6205_);
if (lean_obj_tag(v___x_6208_) == 0)
{
lean_inc(v_defValue_6206_);
return v_defValue_6206_;
}
else
{
lean_object* v_val_6209_; 
v_val_6209_ = lean_ctor_get(v___x_6208_, 0);
lean_inc(v_val_6209_);
lean_dec_ref_known(v___x_6208_, 1);
if (lean_obj_tag(v_val_6209_) == 3)
{
lean_object* v_v_6210_; 
v_v_6210_ = lean_ctor_get(v_val_6209_, 0);
lean_inc(v_v_6210_);
lean_dec_ref_known(v_val_6209_, 1);
return v_v_6210_;
}
else
{
lean_dec(v_val_6209_);
lean_inc(v_defValue_6206_);
return v_defValue_6206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6211_, lean_object* v_opt_6212_){
_start:
{
lean_object* v_res_6213_; 
v_res_6213_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6211_, v_opt_6212_);
lean_dec_ref(v_opt_6212_);
lean_dec_ref(v_opts_6211_);
return v_res_6213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6214_, size_t v_i_6215_, lean_object* v_bs_6216_){
_start:
{
uint8_t v___x_6217_; 
v___x_6217_ = lean_usize_dec_lt(v_i_6215_, v_sz_6214_);
if (v___x_6217_ == 0)
{
return v_bs_6216_;
}
else
{
lean_object* v_v_6218_; lean_object* v_msg_6219_; lean_object* v___x_6220_; lean_object* v_bs_x27_6221_; size_t v___x_6222_; size_t v___x_6223_; lean_object* v___x_6224_; 
v_v_6218_ = lean_array_uget_borrowed(v_bs_6216_, v_i_6215_);
v_msg_6219_ = lean_ctor_get(v_v_6218_, 1);
lean_inc_ref(v_msg_6219_);
v___x_6220_ = lean_unsigned_to_nat(0u);
v_bs_x27_6221_ = lean_array_uset(v_bs_6216_, v_i_6215_, v___x_6220_);
v___x_6222_ = ((size_t)1ULL);
v___x_6223_ = lean_usize_add(v_i_6215_, v___x_6222_);
v___x_6224_ = lean_array_uset(v_bs_x27_6221_, v_i_6215_, v_msg_6219_);
v_i_6215_ = v___x_6223_;
v_bs_6216_ = v___x_6224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6226_, lean_object* v_i_6227_, lean_object* v_bs_6228_){
_start:
{
size_t v_sz_boxed_6229_; size_t v_i_boxed_6230_; lean_object* v_res_6231_; 
v_sz_boxed_6229_ = lean_unbox_usize(v_sz_6226_);
lean_dec(v_sz_6226_);
v_i_boxed_6230_ = lean_unbox_usize(v_i_6227_);
lean_dec(v_i_6227_);
v_res_6231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6229_, v_i_boxed_6230_, v_bs_6228_);
return v_res_6231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6232_, lean_object* v_data_6233_, lean_object* v_ref_6234_, lean_object* v_msg_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_){
_start:
{
lean_object* v_fileName_6241_; lean_object* v_fileMap_6242_; lean_object* v_options_6243_; lean_object* v_currRecDepth_6244_; lean_object* v_maxRecDepth_6245_; lean_object* v_ref_6246_; lean_object* v_currNamespace_6247_; lean_object* v_openDecls_6248_; lean_object* v_initHeartbeats_6249_; lean_object* v_maxHeartbeats_6250_; lean_object* v_quotContext_6251_; lean_object* v_currMacroScope_6252_; uint8_t v_diag_6253_; lean_object* v_cancelTk_x3f_6254_; uint8_t v_suppressElabErrors_6255_; lean_object* v_inheritedTraceOptions_6256_; lean_object* v___x_6257_; lean_object* v_traceState_6258_; lean_object* v_traces_6259_; lean_object* v_ref_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; size_t v_sz_6263_; size_t v___x_6264_; lean_object* v___x_6265_; lean_object* v_msg_6266_; lean_object* v___x_6267_; lean_object* v_a_6268_; lean_object* v___x_6270_; uint8_t v_isShared_6271_; uint8_t v_isSharedCheck_6305_; 
v_fileName_6241_ = lean_ctor_get(v___y_6238_, 0);
v_fileMap_6242_ = lean_ctor_get(v___y_6238_, 1);
v_options_6243_ = lean_ctor_get(v___y_6238_, 2);
v_currRecDepth_6244_ = lean_ctor_get(v___y_6238_, 3);
v_maxRecDepth_6245_ = lean_ctor_get(v___y_6238_, 4);
v_ref_6246_ = lean_ctor_get(v___y_6238_, 5);
v_currNamespace_6247_ = lean_ctor_get(v___y_6238_, 6);
v_openDecls_6248_ = lean_ctor_get(v___y_6238_, 7);
v_initHeartbeats_6249_ = lean_ctor_get(v___y_6238_, 8);
v_maxHeartbeats_6250_ = lean_ctor_get(v___y_6238_, 9);
v_quotContext_6251_ = lean_ctor_get(v___y_6238_, 10);
v_currMacroScope_6252_ = lean_ctor_get(v___y_6238_, 11);
v_diag_6253_ = lean_ctor_get_uint8(v___y_6238_, sizeof(void*)*14);
v_cancelTk_x3f_6254_ = lean_ctor_get(v___y_6238_, 12);
v_suppressElabErrors_6255_ = lean_ctor_get_uint8(v___y_6238_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_6256_ = lean_ctor_get(v___y_6238_, 13);
v___x_6257_ = lean_st_ref_get(v___y_6239_);
v_traceState_6258_ = lean_ctor_get(v___x_6257_, 4);
lean_inc_ref(v_traceState_6258_);
lean_dec(v___x_6257_);
v_traces_6259_ = lean_ctor_get(v_traceState_6258_, 0);
lean_inc_ref(v_traces_6259_);
lean_dec_ref(v_traceState_6258_);
v_ref_6260_ = l_Lean_replaceRef(v_ref_6234_, v_ref_6246_);
lean_inc_ref(v_inheritedTraceOptions_6256_);
lean_inc(v_cancelTk_x3f_6254_);
lean_inc(v_currMacroScope_6252_);
lean_inc(v_quotContext_6251_);
lean_inc(v_maxHeartbeats_6250_);
lean_inc(v_initHeartbeats_6249_);
lean_inc(v_openDecls_6248_);
lean_inc(v_currNamespace_6247_);
lean_inc(v_maxRecDepth_6245_);
lean_inc(v_currRecDepth_6244_);
lean_inc_ref(v_options_6243_);
lean_inc_ref(v_fileMap_6242_);
lean_inc_ref(v_fileName_6241_);
v___x_6261_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_6261_, 0, v_fileName_6241_);
lean_ctor_set(v___x_6261_, 1, v_fileMap_6242_);
lean_ctor_set(v___x_6261_, 2, v_options_6243_);
lean_ctor_set(v___x_6261_, 3, v_currRecDepth_6244_);
lean_ctor_set(v___x_6261_, 4, v_maxRecDepth_6245_);
lean_ctor_set(v___x_6261_, 5, v_ref_6260_);
lean_ctor_set(v___x_6261_, 6, v_currNamespace_6247_);
lean_ctor_set(v___x_6261_, 7, v_openDecls_6248_);
lean_ctor_set(v___x_6261_, 8, v_initHeartbeats_6249_);
lean_ctor_set(v___x_6261_, 9, v_maxHeartbeats_6250_);
lean_ctor_set(v___x_6261_, 10, v_quotContext_6251_);
lean_ctor_set(v___x_6261_, 11, v_currMacroScope_6252_);
lean_ctor_set(v___x_6261_, 12, v_cancelTk_x3f_6254_);
lean_ctor_set(v___x_6261_, 13, v_inheritedTraceOptions_6256_);
lean_ctor_set_uint8(v___x_6261_, sizeof(void*)*14, v_diag_6253_);
lean_ctor_set_uint8(v___x_6261_, sizeof(void*)*14 + 1, v_suppressElabErrors_6255_);
v___x_6262_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6259_);
lean_dec_ref(v_traces_6259_);
v_sz_6263_ = lean_array_size(v___x_6262_);
v___x_6264_ = ((size_t)0ULL);
v___x_6265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6263_, v___x_6264_, v___x_6262_);
v_msg_6266_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6266_, 0, v_data_6233_);
lean_ctor_set(v_msg_6266_, 1, v_msg_6235_);
lean_ctor_set(v_msg_6266_, 2, v___x_6265_);
v___x_6267_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6266_, v___y_6236_, v___y_6237_, v___x_6261_, v___y_6239_);
lean_dec_ref_known(v___x_6261_, 14);
v_a_6268_ = lean_ctor_get(v___x_6267_, 0);
v_isSharedCheck_6305_ = !lean_is_exclusive(v___x_6267_);
if (v_isSharedCheck_6305_ == 0)
{
v___x_6270_ = v___x_6267_;
v_isShared_6271_ = v_isSharedCheck_6305_;
goto v_resetjp_6269_;
}
else
{
lean_inc(v_a_6268_);
lean_dec(v___x_6267_);
v___x_6270_ = lean_box(0);
v_isShared_6271_ = v_isSharedCheck_6305_;
goto v_resetjp_6269_;
}
v_resetjp_6269_:
{
lean_object* v___x_6272_; lean_object* v_traceState_6273_; lean_object* v_env_6274_; lean_object* v_nextMacroScope_6275_; lean_object* v_ngen_6276_; lean_object* v_auxDeclNGen_6277_; lean_object* v_cache_6278_; lean_object* v_messages_6279_; lean_object* v_infoState_6280_; lean_object* v_snapshotTasks_6281_; lean_object* v___x_6283_; uint8_t v_isShared_6284_; uint8_t v_isSharedCheck_6304_; 
v___x_6272_ = lean_st_ref_take(v___y_6239_);
v_traceState_6273_ = lean_ctor_get(v___x_6272_, 4);
v_env_6274_ = lean_ctor_get(v___x_6272_, 0);
v_nextMacroScope_6275_ = lean_ctor_get(v___x_6272_, 1);
v_ngen_6276_ = lean_ctor_get(v___x_6272_, 2);
v_auxDeclNGen_6277_ = lean_ctor_get(v___x_6272_, 3);
v_cache_6278_ = lean_ctor_get(v___x_6272_, 5);
v_messages_6279_ = lean_ctor_get(v___x_6272_, 6);
v_infoState_6280_ = lean_ctor_get(v___x_6272_, 7);
v_snapshotTasks_6281_ = lean_ctor_get(v___x_6272_, 8);
v_isSharedCheck_6304_ = !lean_is_exclusive(v___x_6272_);
if (v_isSharedCheck_6304_ == 0)
{
v___x_6283_ = v___x_6272_;
v_isShared_6284_ = v_isSharedCheck_6304_;
goto v_resetjp_6282_;
}
else
{
lean_inc(v_snapshotTasks_6281_);
lean_inc(v_infoState_6280_);
lean_inc(v_messages_6279_);
lean_inc(v_cache_6278_);
lean_inc(v_traceState_6273_);
lean_inc(v_auxDeclNGen_6277_);
lean_inc(v_ngen_6276_);
lean_inc(v_nextMacroScope_6275_);
lean_inc(v_env_6274_);
lean_dec(v___x_6272_);
v___x_6283_ = lean_box(0);
v_isShared_6284_ = v_isSharedCheck_6304_;
goto v_resetjp_6282_;
}
v_resetjp_6282_:
{
uint64_t v_tid_6285_; lean_object* v___x_6287_; uint8_t v_isShared_6288_; uint8_t v_isSharedCheck_6302_; 
v_tid_6285_ = lean_ctor_get_uint64(v_traceState_6273_, sizeof(void*)*1);
v_isSharedCheck_6302_ = !lean_is_exclusive(v_traceState_6273_);
if (v_isSharedCheck_6302_ == 0)
{
lean_object* v_unused_6303_; 
v_unused_6303_ = lean_ctor_get(v_traceState_6273_, 0);
lean_dec(v_unused_6303_);
v___x_6287_ = v_traceState_6273_;
v_isShared_6288_ = v_isSharedCheck_6302_;
goto v_resetjp_6286_;
}
else
{
lean_dec(v_traceState_6273_);
v___x_6287_ = lean_box(0);
v_isShared_6288_ = v_isSharedCheck_6302_;
goto v_resetjp_6286_;
}
v_resetjp_6286_:
{
lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6292_; 
v___x_6289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6289_, 0, v_ref_6234_);
lean_ctor_set(v___x_6289_, 1, v_a_6268_);
v___x_6290_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6232_, v___x_6289_);
if (v_isShared_6288_ == 0)
{
lean_ctor_set(v___x_6287_, 0, v___x_6290_);
v___x_6292_ = v___x_6287_;
goto v_reusejp_6291_;
}
else
{
lean_object* v_reuseFailAlloc_6301_; 
v_reuseFailAlloc_6301_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6301_, 0, v___x_6290_);
lean_ctor_set_uint64(v_reuseFailAlloc_6301_, sizeof(void*)*1, v_tid_6285_);
v___x_6292_ = v_reuseFailAlloc_6301_;
goto v_reusejp_6291_;
}
v_reusejp_6291_:
{
lean_object* v___x_6294_; 
if (v_isShared_6284_ == 0)
{
lean_ctor_set(v___x_6283_, 4, v___x_6292_);
v___x_6294_ = v___x_6283_;
goto v_reusejp_6293_;
}
else
{
lean_object* v_reuseFailAlloc_6300_; 
v_reuseFailAlloc_6300_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6300_, 0, v_env_6274_);
lean_ctor_set(v_reuseFailAlloc_6300_, 1, v_nextMacroScope_6275_);
lean_ctor_set(v_reuseFailAlloc_6300_, 2, v_ngen_6276_);
lean_ctor_set(v_reuseFailAlloc_6300_, 3, v_auxDeclNGen_6277_);
lean_ctor_set(v_reuseFailAlloc_6300_, 4, v___x_6292_);
lean_ctor_set(v_reuseFailAlloc_6300_, 5, v_cache_6278_);
lean_ctor_set(v_reuseFailAlloc_6300_, 6, v_messages_6279_);
lean_ctor_set(v_reuseFailAlloc_6300_, 7, v_infoState_6280_);
lean_ctor_set(v_reuseFailAlloc_6300_, 8, v_snapshotTasks_6281_);
v___x_6294_ = v_reuseFailAlloc_6300_;
goto v_reusejp_6293_;
}
v_reusejp_6293_:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6298_; 
v___x_6295_ = lean_st_ref_put(v___y_6239_, v___x_6294_);
v___x_6296_ = lean_box(0);
if (v_isShared_6271_ == 0)
{
lean_ctor_set(v___x_6270_, 0, v___x_6296_);
v___x_6298_ = v___x_6270_;
goto v_reusejp_6297_;
}
else
{
lean_object* v_reuseFailAlloc_6299_; 
v_reuseFailAlloc_6299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6299_, 0, v___x_6296_);
v___x_6298_ = v_reuseFailAlloc_6299_;
goto v_reusejp_6297_;
}
v_reusejp_6297_:
{
return v___x_6298_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6306_, lean_object* v_data_6307_, lean_object* v_ref_6308_, lean_object* v_msg_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_){
_start:
{
lean_object* v_res_6315_; 
v_res_6315_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6306_, v_data_6307_, v_ref_6308_, v_msg_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_);
lean_dec(v___y_6313_);
lean_dec_ref(v___y_6312_);
lean_dec(v___y_6311_);
lean_dec_ref(v___y_6310_);
return v_res_6315_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6317_; lean_object* v___x_6318_; 
v___x_6317_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6318_ = l_Lean_stringToMessageData(v___x_6317_);
return v___x_6318_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6319_; double v___x_6320_; 
v___x_6319_ = lean_unsigned_to_nat(1000u);
v___x_6320_ = lean_float_of_nat(v___x_6319_);
return v___x_6320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6321_, uint8_t v_collapsed_6322_, lean_object* v_tag_6323_, lean_object* v_opts_6324_, uint8_t v_clsEnabled_6325_, lean_object* v_oldTraces_6326_, lean_object* v_msg_6327_, lean_object* v_resStartStop_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_){
_start:
{
lean_object* v_fst_6341_; lean_object* v_snd_6342_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v_data_6346_; lean_object* v_fst_6357_; lean_object* v_snd_6358_; lean_object* v___x_6359_; uint8_t v___x_6360_; lean_object* v___y_6362_; lean_object* v_a_6363_; uint8_t v___y_6378_; double v___y_6409_; 
v_fst_6341_ = lean_ctor_get(v_resStartStop_6328_, 0);
lean_inc(v_fst_6341_);
v_snd_6342_ = lean_ctor_get(v_resStartStop_6328_, 1);
lean_inc(v_snd_6342_);
lean_dec_ref(v_resStartStop_6328_);
v_fst_6357_ = lean_ctor_get(v_snd_6342_, 0);
lean_inc(v_fst_6357_);
v_snd_6358_ = lean_ctor_get(v_snd_6342_, 1);
lean_inc(v_snd_6358_);
lean_dec(v_snd_6342_);
v___x_6359_ = l_Lean_trace_profiler;
v___x_6360_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6324_, v___x_6359_);
if (v___x_6360_ == 0)
{
v___y_6378_ = v___x_6360_;
goto v___jp_6377_;
}
else
{
lean_object* v___x_6414_; uint8_t v___x_6415_; 
v___x_6414_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6415_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6324_, v___x_6414_);
if (v___x_6415_ == 0)
{
lean_object* v___x_6416_; lean_object* v___x_6417_; double v___x_6418_; double v___x_6419_; double v___x_6420_; 
v___x_6416_ = l_Lean_trace_profiler_threshold;
v___x_6417_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6324_, v___x_6416_);
v___x_6418_ = lean_float_of_nat(v___x_6417_);
v___x_6419_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6420_ = lean_float_div(v___x_6418_, v___x_6419_);
v___y_6409_ = v___x_6420_;
goto v___jp_6408_;
}
else
{
lean_object* v___x_6421_; lean_object* v___x_6422_; double v___x_6423_; 
v___x_6421_ = l_Lean_trace_profiler_threshold;
v___x_6422_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6324_, v___x_6421_);
v___x_6423_ = lean_float_of_nat(v___x_6422_);
v___y_6409_ = v___x_6423_;
goto v___jp_6408_;
}
}
v___jp_6343_:
{
lean_object* v___x_6347_; 
lean_inc(v___y_6345_);
v___x_6347_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6326_, v_data_6346_, v___y_6345_, v___y_6344_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_);
if (lean_obj_tag(v___x_6347_) == 0)
{
lean_object* v___x_6348_; 
lean_dec_ref_known(v___x_6347_, 1);
v___x_6348_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6341_);
return v___x_6348_;
}
else
{
lean_object* v_a_6349_; lean_object* v___x_6351_; uint8_t v_isShared_6352_; uint8_t v_isSharedCheck_6356_; 
lean_dec(v_fst_6341_);
v_a_6349_ = lean_ctor_get(v___x_6347_, 0);
v_isSharedCheck_6356_ = !lean_is_exclusive(v___x_6347_);
if (v_isSharedCheck_6356_ == 0)
{
v___x_6351_ = v___x_6347_;
v_isShared_6352_ = v_isSharedCheck_6356_;
goto v_resetjp_6350_;
}
else
{
lean_inc(v_a_6349_);
lean_dec(v___x_6347_);
v___x_6351_ = lean_box(0);
v_isShared_6352_ = v_isSharedCheck_6356_;
goto v_resetjp_6350_;
}
v_resetjp_6350_:
{
lean_object* v___x_6354_; 
if (v_isShared_6352_ == 0)
{
v___x_6354_ = v___x_6351_;
goto v_reusejp_6353_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_a_6349_);
v___x_6354_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6353_;
}
v_reusejp_6353_:
{
return v___x_6354_;
}
}
}
}
v___jp_6361_:
{
uint8_t v_result_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; double v___x_6367_; lean_object* v_data_6368_; 
v_result_6364_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6341_);
v___x_6365_ = lean_box(v_result_6364_);
v___x_6366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6366_, 0, v___x_6365_);
v___x_6367_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6323_);
lean_inc_ref(v___x_6366_);
lean_inc(v_cls_6321_);
v_data_6368_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6368_, 0, v_cls_6321_);
lean_ctor_set(v_data_6368_, 1, v___x_6366_);
lean_ctor_set(v_data_6368_, 2, v_tag_6323_);
lean_ctor_set_float(v_data_6368_, sizeof(void*)*3, v___x_6367_);
lean_ctor_set_float(v_data_6368_, sizeof(void*)*3 + 8, v___x_6367_);
lean_ctor_set_uint8(v_data_6368_, sizeof(void*)*3 + 16, v_collapsed_6322_);
if (v___x_6360_ == 0)
{
lean_dec_ref_known(v___x_6366_, 1);
lean_dec(v_snd_6358_);
lean_dec(v_fst_6357_);
lean_dec_ref(v_tag_6323_);
lean_dec(v_cls_6321_);
v___y_6344_ = v_a_6363_;
v___y_6345_ = v___y_6362_;
v_data_6346_ = v_data_6368_;
goto v___jp_6343_;
}
else
{
lean_object* v_data_6369_; double v___x_6370_; double v___x_6371_; 
lean_dec_ref_known(v_data_6368_, 3);
v_data_6369_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6369_, 0, v_cls_6321_);
lean_ctor_set(v_data_6369_, 1, v___x_6366_);
lean_ctor_set(v_data_6369_, 2, v_tag_6323_);
v___x_6370_ = lean_unbox_float(v_fst_6357_);
lean_dec(v_fst_6357_);
lean_ctor_set_float(v_data_6369_, sizeof(void*)*3, v___x_6370_);
v___x_6371_ = lean_unbox_float(v_snd_6358_);
lean_dec(v_snd_6358_);
lean_ctor_set_float(v_data_6369_, sizeof(void*)*3 + 8, v___x_6371_);
lean_ctor_set_uint8(v_data_6369_, sizeof(void*)*3 + 16, v_collapsed_6322_);
v___y_6344_ = v_a_6363_;
v___y_6345_ = v___y_6362_;
v_data_6346_ = v_data_6369_;
goto v___jp_6343_;
}
}
v___jp_6372_:
{
lean_object* v_ref_6373_; lean_object* v___x_6374_; 
v_ref_6373_ = lean_ctor_get(v___y_6338_, 5);
lean_inc(v___y_6339_);
lean_inc_ref(v___y_6338_);
lean_inc(v___y_6337_);
lean_inc_ref(v___y_6336_);
lean_inc(v___y_6335_);
lean_inc_ref(v___y_6334_);
lean_inc(v___y_6333_);
lean_inc_ref(v___y_6332_);
lean_inc(v___y_6331_);
lean_inc(v___y_6330_);
lean_inc_ref(v___y_6329_);
lean_inc(v_fst_6341_);
v___x_6374_ = lean_apply_13(v_msg_6327_, v_fst_6341_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_, lean_box(0));
if (lean_obj_tag(v___x_6374_) == 0)
{
lean_object* v_a_6375_; 
v_a_6375_ = lean_ctor_get(v___x_6374_, 0);
lean_inc(v_a_6375_);
lean_dec_ref_known(v___x_6374_, 1);
v___y_6362_ = v_ref_6373_;
v_a_6363_ = v_a_6375_;
goto v___jp_6361_;
}
else
{
lean_object* v___x_6376_; 
lean_dec_ref_known(v___x_6374_, 1);
v___x_6376_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6362_ = v_ref_6373_;
v_a_6363_ = v___x_6376_;
goto v___jp_6361_;
}
}
v___jp_6377_:
{
if (v_clsEnabled_6325_ == 0)
{
if (v___y_6378_ == 0)
{
lean_object* v___x_6379_; lean_object* v_traceState_6380_; lean_object* v_env_6381_; lean_object* v_nextMacroScope_6382_; lean_object* v_ngen_6383_; lean_object* v_auxDeclNGen_6384_; lean_object* v_cache_6385_; lean_object* v_messages_6386_; lean_object* v_infoState_6387_; lean_object* v_snapshotTasks_6388_; lean_object* v___x_6390_; uint8_t v_isShared_6391_; uint8_t v_isSharedCheck_6407_; 
lean_dec(v_snd_6358_);
lean_dec(v_fst_6357_);
lean_dec_ref(v_msg_6327_);
lean_dec_ref(v_tag_6323_);
lean_dec(v_cls_6321_);
v___x_6379_ = lean_st_ref_take(v___y_6339_);
v_traceState_6380_ = lean_ctor_get(v___x_6379_, 4);
v_env_6381_ = lean_ctor_get(v___x_6379_, 0);
v_nextMacroScope_6382_ = lean_ctor_get(v___x_6379_, 1);
v_ngen_6383_ = lean_ctor_get(v___x_6379_, 2);
v_auxDeclNGen_6384_ = lean_ctor_get(v___x_6379_, 3);
v_cache_6385_ = lean_ctor_get(v___x_6379_, 5);
v_messages_6386_ = lean_ctor_get(v___x_6379_, 6);
v_infoState_6387_ = lean_ctor_get(v___x_6379_, 7);
v_snapshotTasks_6388_ = lean_ctor_get(v___x_6379_, 8);
v_isSharedCheck_6407_ = !lean_is_exclusive(v___x_6379_);
if (v_isSharedCheck_6407_ == 0)
{
v___x_6390_ = v___x_6379_;
v_isShared_6391_ = v_isSharedCheck_6407_;
goto v_resetjp_6389_;
}
else
{
lean_inc(v_snapshotTasks_6388_);
lean_inc(v_infoState_6387_);
lean_inc(v_messages_6386_);
lean_inc(v_cache_6385_);
lean_inc(v_traceState_6380_);
lean_inc(v_auxDeclNGen_6384_);
lean_inc(v_ngen_6383_);
lean_inc(v_nextMacroScope_6382_);
lean_inc(v_env_6381_);
lean_dec(v___x_6379_);
v___x_6390_ = lean_box(0);
v_isShared_6391_ = v_isSharedCheck_6407_;
goto v_resetjp_6389_;
}
v_resetjp_6389_:
{
uint64_t v_tid_6392_; lean_object* v_traces_6393_; lean_object* v___x_6395_; uint8_t v_isShared_6396_; uint8_t v_isSharedCheck_6406_; 
v_tid_6392_ = lean_ctor_get_uint64(v_traceState_6380_, sizeof(void*)*1);
v_traces_6393_ = lean_ctor_get(v_traceState_6380_, 0);
v_isSharedCheck_6406_ = !lean_is_exclusive(v_traceState_6380_);
if (v_isSharedCheck_6406_ == 0)
{
v___x_6395_ = v_traceState_6380_;
v_isShared_6396_ = v_isSharedCheck_6406_;
goto v_resetjp_6394_;
}
else
{
lean_inc(v_traces_6393_);
lean_dec(v_traceState_6380_);
v___x_6395_ = lean_box(0);
v_isShared_6396_ = v_isSharedCheck_6406_;
goto v_resetjp_6394_;
}
v_resetjp_6394_:
{
lean_object* v___x_6397_; lean_object* v___x_6399_; 
v___x_6397_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6326_, v_traces_6393_);
lean_dec_ref(v_traces_6393_);
if (v_isShared_6396_ == 0)
{
lean_ctor_set(v___x_6395_, 0, v___x_6397_);
v___x_6399_ = v___x_6395_;
goto v_reusejp_6398_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v___x_6397_);
lean_ctor_set_uint64(v_reuseFailAlloc_6405_, sizeof(void*)*1, v_tid_6392_);
v___x_6399_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6398_;
}
v_reusejp_6398_:
{
lean_object* v___x_6401_; 
if (v_isShared_6391_ == 0)
{
lean_ctor_set(v___x_6390_, 4, v___x_6399_);
v___x_6401_ = v___x_6390_;
goto v_reusejp_6400_;
}
else
{
lean_object* v_reuseFailAlloc_6404_; 
v_reuseFailAlloc_6404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6404_, 0, v_env_6381_);
lean_ctor_set(v_reuseFailAlloc_6404_, 1, v_nextMacroScope_6382_);
lean_ctor_set(v_reuseFailAlloc_6404_, 2, v_ngen_6383_);
lean_ctor_set(v_reuseFailAlloc_6404_, 3, v_auxDeclNGen_6384_);
lean_ctor_set(v_reuseFailAlloc_6404_, 4, v___x_6399_);
lean_ctor_set(v_reuseFailAlloc_6404_, 5, v_cache_6385_);
lean_ctor_set(v_reuseFailAlloc_6404_, 6, v_messages_6386_);
lean_ctor_set(v_reuseFailAlloc_6404_, 7, v_infoState_6387_);
lean_ctor_set(v_reuseFailAlloc_6404_, 8, v_snapshotTasks_6388_);
v___x_6401_ = v_reuseFailAlloc_6404_;
goto v_reusejp_6400_;
}
v_reusejp_6400_:
{
lean_object* v___x_6402_; lean_object* v___x_6403_; 
v___x_6402_ = lean_st_ref_put(v___y_6339_, v___x_6401_);
v___x_6403_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6341_);
return v___x_6403_;
}
}
}
}
}
else
{
goto v___jp_6372_;
}
}
else
{
goto v___jp_6372_;
}
}
v___jp_6408_:
{
double v___x_6410_; double v___x_6411_; double v___x_6412_; uint8_t v___x_6413_; 
v___x_6410_ = lean_unbox_float(v_snd_6358_);
v___x_6411_ = lean_unbox_float(v_fst_6357_);
v___x_6412_ = lean_float_sub(v___x_6410_, v___x_6411_);
v___x_6413_ = lean_float_decLt(v___y_6409_, v___x_6412_);
v___y_6378_ = v___x_6413_;
goto v___jp_6377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6424_ = _args[0];
lean_object* v_collapsed_6425_ = _args[1];
lean_object* v_tag_6426_ = _args[2];
lean_object* v_opts_6427_ = _args[3];
lean_object* v_clsEnabled_6428_ = _args[4];
lean_object* v_oldTraces_6429_ = _args[5];
lean_object* v_msg_6430_ = _args[6];
lean_object* v_resStartStop_6431_ = _args[7];
lean_object* v___y_6432_ = _args[8];
lean_object* v___y_6433_ = _args[9];
lean_object* v___y_6434_ = _args[10];
lean_object* v___y_6435_ = _args[11];
lean_object* v___y_6436_ = _args[12];
lean_object* v___y_6437_ = _args[13];
lean_object* v___y_6438_ = _args[14];
lean_object* v___y_6439_ = _args[15];
lean_object* v___y_6440_ = _args[16];
lean_object* v___y_6441_ = _args[17];
lean_object* v___y_6442_ = _args[18];
lean_object* v___y_6443_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6444_; uint8_t v_clsEnabled_boxed_6445_; lean_object* v_res_6446_; 
v_collapsed_boxed_6444_ = lean_unbox(v_collapsed_6425_);
v_clsEnabled_boxed_6445_ = lean_unbox(v_clsEnabled_6428_);
v_res_6446_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6424_, v_collapsed_boxed_6444_, v_tag_6426_, v_opts_6427_, v_clsEnabled_boxed_6445_, v_oldTraces_6429_, v_msg_6430_, v_resStartStop_6431_, v___y_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_);
lean_dec(v___y_6442_);
lean_dec_ref(v___y_6441_);
lean_dec(v___y_6440_);
lean_dec_ref(v___y_6439_);
lean_dec(v___y_6438_);
lean_dec_ref(v___y_6437_);
lean_dec(v___y_6436_);
lean_dec_ref(v___y_6435_);
lean_dec(v___y_6434_);
lean_dec(v___y_6433_);
lean_dec_ref(v___y_6432_);
lean_dec_ref(v_opts_6427_);
return v_res_6446_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6451_; lean_object* v___x_6452_; 
v___x_6451_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6452_ = l_Lean_stringToMessageData(v___x_6451_);
return v___x_6452_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6453_, lean_object* v_b_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_){
_start:
{
if (lean_obj_tag(v_as_x27_6453_) == 0)
{
lean_object* v___x_6467_; 
v___x_6467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6467_, 0, v_b_6454_);
return v___x_6467_;
}
else
{
lean_object* v_head_6468_; lean_object* v_options_6469_; lean_object* v_tail_6470_; lean_object* v_name_6471_; lean_object* v_run_x27_6472_; lean_object* v_inheritedTraceOptions_6473_; uint8_t v_hasTrace_6474_; lean_object* v___x_6475_; uint8_t v___y_6477_; lean_object* v___x_6482_; lean_object* v___y_6484_; 
lean_dec_ref(v_b_6454_);
v_head_6468_ = lean_ctor_get(v_as_x27_6453_, 0);
v_options_6469_ = lean_ctor_get(v___y_6464_, 2);
v_tail_6470_ = lean_ctor_get(v_as_x27_6453_, 1);
v_name_6471_ = lean_ctor_get(v_head_6468_, 0);
v_run_x27_6472_ = lean_ctor_get(v_head_6468_, 1);
v_inheritedTraceOptions_6473_ = lean_ctor_get(v___y_6464_, 13);
v_hasTrace_6474_ = lean_ctor_get_uint8(v_options_6469_, sizeof(void*)*1);
v___x_6475_ = lean_box(0);
v___x_6482_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6474_ == 0)
{
lean_object* v___x_6512_; 
lean_inc_ref(v_run_x27_6472_);
lean_inc(v___y_6465_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6463_);
lean_inc_ref(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
lean_inc(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc_ref(v___y_6455_);
v___x_6512_ = lean_apply_12(v_run_x27_6472_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, lean_box(0));
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
lean_inc(v___y_6465_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6463_);
lean_inc_ref(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
lean_inc(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc_ref(v___y_6455_);
v___x_6588_ = lean_apply_12(v_run_x27_6472_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, lean_box(0));
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
v___x_6523_ = lean_float_of_nat(v___y_6520_);
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
v___x_6532_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6514_, v_hasTrace_6474_, v___x_6515_, v_options_6469_, v___x_6517_, v___y_6519_, v___f_6513_, v___x_6531_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
v___y_6484_ = v___x_6532_;
goto v___jp_6483_;
}
v___jp_6533_:
{
lean_object* v___x_6537_; double v___x_6538_; double v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; 
v___x_6537_ = lean_io_get_num_heartbeats();
v___x_6538_ = lean_float_of_nat(v___y_6535_);
v___x_6539_ = lean_float_of_nat(v___x_6537_);
v___x_6540_ = lean_box_float(v___x_6538_);
v___x_6541_ = lean_box_float(v___x_6539_);
v___x_6542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6542_, 0, v___x_6540_);
lean_ctor_set(v___x_6542_, 1, v___x_6541_);
v___x_6543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6543_, 0, v_a_6536_);
lean_ctor_set(v___x_6543_, 1, v___x_6542_);
v___x_6544_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6514_, v_hasTrace_6474_, v___x_6515_, v_options_6469_, v___x_6517_, v___y_6534_, v___f_6513_, v___x_6543_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
v___y_6484_ = v___x_6544_;
goto v___jp_6483_;
}
v___jp_6545_:
{
lean_object* v___x_6546_; lean_object* v_a_6547_; lean_object* v___x_6548_; uint8_t v___x_6549_; 
v___x_6546_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6465_);
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
lean_inc(v___y_6465_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6463_);
lean_inc_ref(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
lean_inc(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc_ref(v___y_6455_);
v___x_6551_ = lean_apply_12(v_run_x27_6472_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, lean_box(0));
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
v___y_6519_ = v_a_6547_;
v___y_6520_ = v___x_6550_;
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
v___y_6519_ = v_a_6547_;
v___y_6520_ = v___x_6550_;
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
lean_inc(v___y_6465_);
lean_inc_ref(v___y_6464_);
lean_inc(v___y_6463_);
lean_inc_ref(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
lean_inc(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc_ref(v___y_6455_);
v___x_6569_ = lean_apply_12(v_run_x27_6472_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, lean_box(0));
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
v___y_6534_ = v_a_6547_;
v___y_6535_ = v___x_6568_;
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
v___y_6534_ = v_a_6547_;
v___y_6535_ = v___x_6568_;
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
v_as_x27_6453_ = v_tail_6470_;
v_b_6454_ = v___x_6482_;
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
v___x_6494_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6489_, v___x_6493_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
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
lean_object* v___x_6626_; lean_object* v_caches_6627_; lean_object* v_typeAnalysis_6628_; lean_object* v_target_6629_; lean_object* v_hypotheses_6630_; lean_object* v___x_6632_; uint8_t v_isShared_6633_; uint8_t v_isSharedCheck_6713_; 
lean_dec_ref_known(v___x_6625_, 1);
v___x_6626_ = lean_st_ref_take(v_a_6613_);
v_caches_6627_ = lean_ctor_get(v___x_6626_, 0);
v_typeAnalysis_6628_ = lean_ctor_get(v___x_6626_, 1);
v_target_6629_ = lean_ctor_get(v___x_6626_, 2);
v_hypotheses_6630_ = lean_ctor_get(v___x_6626_, 3);
v_isSharedCheck_6713_ = !lean_is_exclusive(v___x_6626_);
if (v_isSharedCheck_6713_ == 0)
{
v___x_6632_ = v___x_6626_;
v_isShared_6633_ = v_isSharedCheck_6713_;
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
v_isShared_6633_ = v_isSharedCheck_6713_;
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
lean_object* v_reuseFailAlloc_6712_; 
v_reuseFailAlloc_6712_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_caches_6627_);
lean_ctor_set(v_reuseFailAlloc_6712_, 1, v_typeAnalysis_6628_);
lean_ctor_set(v_reuseFailAlloc_6712_, 2, v_target_6629_);
lean_ctor_set(v_reuseFailAlloc_6712_, 3, v_hypotheses_6630_);
v___x_6636_ = v_reuseFailAlloc_6712_;
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
lean_object* v_a_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6703_; 
v_a_6640_ = lean_ctor_get(v___x_6639_, 0);
v_isSharedCheck_6703_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6703_ == 0)
{
v___x_6642_ = v___x_6639_;
v_isShared_6643_ = v_isSharedCheck_6703_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_a_6640_);
lean_dec(v___x_6639_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6703_;
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
lean_object* v_options_6647_; uint8_t v_hasTrace_6648_; 
v_options_6647_ = lean_ctor_get(v_a_6621_, 2);
v_hasTrace_6648_ = lean_ctor_get_uint8(v_options_6647_, sizeof(void*)*1);
if (v_hasTrace_6648_ == 0)
{
lean_object* v___x_6649_; lean_object* v___x_6651_; 
v___x_6649_ = lean_box(v_didChange_6646_);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v___x_6649_);
v___x_6651_ = v___x_6642_;
goto v_reusejp_6650_;
}
else
{
lean_object* v_reuseFailAlloc_6652_; 
v_reuseFailAlloc_6652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6652_, 0, v___x_6649_);
v___x_6651_ = v_reuseFailAlloc_6652_;
goto v_reusejp_6650_;
}
v_reusejp_6650_:
{
return v___x_6651_;
}
}
else
{
lean_object* v_inheritedTraceOptions_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; uint8_t v___x_6656_; 
v_inheritedTraceOptions_6653_ = lean_ctor_get(v_a_6621_, 13);
v___x_6654_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6655_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6656_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6653_, v_options_6647_, v___x_6655_);
if (v___x_6656_ == 0)
{
lean_object* v___x_6657_; lean_object* v___x_6659_; 
v___x_6657_ = lean_box(v_didChange_6646_);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v___x_6657_);
v___x_6659_ = v___x_6642_;
goto v_reusejp_6658_;
}
else
{
lean_object* v_reuseFailAlloc_6660_; 
v_reuseFailAlloc_6660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6660_, 0, v___x_6657_);
v___x_6659_ = v_reuseFailAlloc_6660_;
goto v_reusejp_6658_;
}
v_reusejp_6658_:
{
return v___x_6659_;
}
}
else
{
lean_object* v___x_6661_; lean_object* v___x_6662_; 
lean_del_object(v___x_6642_);
v___x_6661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6662_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6654_, v___x_6661_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_);
if (lean_obj_tag(v___x_6662_) == 0)
{
lean_object* v___x_6664_; uint8_t v_isShared_6665_; uint8_t v_isSharedCheck_6670_; 
v_isSharedCheck_6670_ = !lean_is_exclusive(v___x_6662_);
if (v_isSharedCheck_6670_ == 0)
{
lean_object* v_unused_6671_; 
v_unused_6671_ = lean_ctor_get(v___x_6662_, 0);
lean_dec(v_unused_6671_);
v___x_6664_ = v___x_6662_;
v_isShared_6665_ = v_isSharedCheck_6670_;
goto v_resetjp_6663_;
}
else
{
lean_dec(v___x_6662_);
v___x_6664_ = lean_box(0);
v_isShared_6665_ = v_isSharedCheck_6670_;
goto v_resetjp_6663_;
}
v_resetjp_6663_:
{
lean_object* v___x_6666_; lean_object* v___x_6668_; 
v___x_6666_ = lean_box(v_didChange_6646_);
if (v_isShared_6665_ == 0)
{
lean_ctor_set(v___x_6664_, 0, v___x_6666_);
v___x_6668_ = v___x_6664_;
goto v_reusejp_6667_;
}
else
{
lean_object* v_reuseFailAlloc_6669_; 
v_reuseFailAlloc_6669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6669_, 0, v___x_6666_);
v___x_6668_ = v_reuseFailAlloc_6669_;
goto v_reusejp_6667_;
}
v_reusejp_6667_:
{
return v___x_6668_;
}
}
}
else
{
lean_object* v_a_6672_; lean_object* v___x_6674_; uint8_t v_isShared_6675_; uint8_t v_isSharedCheck_6679_; 
v_a_6672_ = lean_ctor_get(v___x_6662_, 0);
v_isSharedCheck_6679_ = !lean_is_exclusive(v___x_6662_);
if (v_isSharedCheck_6679_ == 0)
{
v___x_6674_ = v___x_6662_;
v_isShared_6675_ = v_isSharedCheck_6679_;
goto v_resetjp_6673_;
}
else
{
lean_inc(v_a_6672_);
lean_dec(v___x_6662_);
v___x_6674_ = lean_box(0);
v_isShared_6675_ = v_isSharedCheck_6679_;
goto v_resetjp_6673_;
}
v_resetjp_6673_:
{
lean_object* v___x_6677_; 
if (v_isShared_6675_ == 0)
{
v___x_6677_ = v___x_6674_;
goto v_reusejp_6676_;
}
else
{
lean_object* v_reuseFailAlloc_6678_; 
v_reuseFailAlloc_6678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6678_, 0, v_a_6672_);
v___x_6677_ = v_reuseFailAlloc_6678_;
goto v_reusejp_6676_;
}
v_reusejp_6676_:
{
return v___x_6677_;
}
}
}
}
}
}
else
{
lean_object* v_options_6680_; uint8_t v_hasTrace_6681_; 
lean_del_object(v___x_6642_);
v_options_6680_ = lean_ctor_get(v_a_6621_, 2);
v_hasTrace_6681_ = lean_ctor_get_uint8(v_options_6680_, sizeof(void*)*1);
if (v_hasTrace_6681_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; uint8_t v___x_6686_; 
v_inheritedTraceOptions_6683_ = lean_ctor_get(v_a_6621_, 13);
v___x_6684_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6685_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6686_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6683_, v_options_6680_, v___x_6685_);
if (v___x_6686_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6688_; lean_object* v___x_6689_; 
v___x_6688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6689_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6684_, v___x_6688_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_);
if (lean_obj_tag(v___x_6689_) == 0)
{
lean_dec_ref_known(v___x_6689_, 1);
goto _start;
}
else
{
lean_object* v_a_6691_; lean_object* v___x_6693_; uint8_t v_isShared_6694_; uint8_t v_isSharedCheck_6698_; 
v_a_6691_ = lean_ctor_get(v___x_6689_, 0);
v_isSharedCheck_6698_ = !lean_is_exclusive(v___x_6689_);
if (v_isSharedCheck_6698_ == 0)
{
v___x_6693_ = v___x_6689_;
v_isShared_6694_ = v_isSharedCheck_6698_;
goto v_resetjp_6692_;
}
else
{
lean_inc(v_a_6691_);
lean_dec(v___x_6689_);
v___x_6693_ = lean_box(0);
v_isShared_6694_ = v_isSharedCheck_6698_;
goto v_resetjp_6692_;
}
v_resetjp_6692_:
{
lean_object* v___x_6696_; 
if (v_isShared_6694_ == 0)
{
v___x_6696_ = v___x_6693_;
goto v_reusejp_6695_;
}
else
{
lean_object* v_reuseFailAlloc_6697_; 
v_reuseFailAlloc_6697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6697_, 0, v_a_6691_);
v___x_6696_ = v_reuseFailAlloc_6697_;
goto v_reusejp_6695_;
}
v_reusejp_6695_:
{
return v___x_6696_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_6699_; lean_object* v___x_6701_; 
v_val_6699_ = lean_ctor_get(v_fst_6644_, 0);
lean_inc(v_val_6699_);
lean_dec_ref_known(v_fst_6644_, 1);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v_val_6699_);
v___x_6701_ = v___x_6642_;
goto v_reusejp_6700_;
}
else
{
lean_object* v_reuseFailAlloc_6702_; 
v_reuseFailAlloc_6702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_val_6699_);
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
else
{
lean_object* v_a_6704_; lean_object* v___x_6706_; uint8_t v_isShared_6707_; uint8_t v_isSharedCheck_6711_; 
v_a_6704_ = lean_ctor_get(v___x_6639_, 0);
v_isSharedCheck_6711_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6711_ == 0)
{
v___x_6706_ = v___x_6639_;
v_isShared_6707_ = v_isSharedCheck_6711_;
goto v_resetjp_6705_;
}
else
{
lean_inc(v_a_6704_);
lean_dec(v___x_6639_);
v___x_6706_ = lean_box(0);
v_isShared_6707_ = v_isSharedCheck_6711_;
goto v_resetjp_6705_;
}
v_resetjp_6705_:
{
lean_object* v___x_6709_; 
if (v_isShared_6707_ == 0)
{
v___x_6709_ = v___x_6706_;
goto v_reusejp_6708_;
}
else
{
lean_object* v_reuseFailAlloc_6710_; 
v_reuseFailAlloc_6710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6710_, 0, v_a_6704_);
v___x_6709_ = v_reuseFailAlloc_6710_;
goto v_reusejp_6708_;
}
v_reusejp_6708_:
{
return v___x_6709_;
}
}
}
}
}
}
else
{
lean_object* v_a_6714_; lean_object* v___x_6716_; uint8_t v_isShared_6717_; uint8_t v_isSharedCheck_6721_; 
v_a_6714_ = lean_ctor_get(v___x_6625_, 0);
v_isSharedCheck_6721_ = !lean_is_exclusive(v___x_6625_);
if (v_isSharedCheck_6721_ == 0)
{
v___x_6716_ = v___x_6625_;
v_isShared_6717_ = v_isSharedCheck_6721_;
goto v_resetjp_6715_;
}
else
{
lean_inc(v_a_6714_);
lean_dec(v___x_6625_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6722_, lean_object* v_a_6723_, lean_object* v_a_6724_, lean_object* v_a_6725_, lean_object* v_a_6726_, lean_object* v_a_6727_, lean_object* v_a_6728_, lean_object* v_a_6729_, lean_object* v_a_6730_, lean_object* v_a_6731_, lean_object* v_a_6732_, lean_object* v_a_6733_, lean_object* v_a_6734_){
_start:
{
lean_object* v_res_6735_; 
v_res_6735_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6722_, v_a_6723_, v_a_6724_, v_a_6725_, v_a_6726_, v_a_6727_, v_a_6728_, v_a_6729_, v_a_6730_, v_a_6731_, v_a_6732_, v_a_6733_);
lean_dec(v_a_6733_);
lean_dec_ref(v_a_6732_);
lean_dec(v_a_6731_);
lean_dec_ref(v_a_6730_);
lean_dec(v_a_6729_);
lean_dec_ref(v_a_6728_);
lean_dec(v_a_6727_);
lean_dec_ref(v_a_6726_);
lean_dec(v_a_6725_);
lean_dec(v_a_6724_);
lean_dec_ref(v_a_6723_);
lean_dec(v_passes_6722_);
return v_res_6735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6736_, lean_object* v_msg_6737_, lean_object* v___y_6738_, lean_object* v___y_6739_, lean_object* v___y_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_, lean_object* v___y_6744_, lean_object* v___y_6745_, lean_object* v___y_6746_, lean_object* v___y_6747_, lean_object* v___y_6748_){
_start:
{
lean_object* v___x_6750_; 
v___x_6750_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6736_, v_msg_6737_, v___y_6745_, v___y_6746_, v___y_6747_, v___y_6748_);
return v___x_6750_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6751_, lean_object* v_msg_6752_, lean_object* v___y_6753_, lean_object* v___y_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_, lean_object* v___y_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_, lean_object* v___y_6761_, lean_object* v___y_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_){
_start:
{
lean_object* v_res_6765_; 
v_res_6765_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6751_, v_msg_6752_, v___y_6753_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_);
lean_dec(v___y_6763_);
lean_dec_ref(v___y_6762_);
lean_dec(v___y_6761_);
lean_dec_ref(v___y_6760_);
lean_dec(v___y_6759_);
lean_dec_ref(v___y_6758_);
lean_dec(v___y_6757_);
lean_dec_ref(v___y_6756_);
lean_dec(v___y_6755_);
lean_dec(v___y_6754_);
lean_dec_ref(v___y_6753_);
return v_res_6765_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6766_, lean_object* v_x_6767_, lean_object* v___y_6768_, lean_object* v___y_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_, lean_object* v___y_6772_, lean_object* v___y_6773_, lean_object* v___y_6774_, lean_object* v___y_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_){
_start:
{
lean_object* v___x_6780_; 
v___x_6780_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6767_);
return v___x_6780_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6781_, lean_object* v_x_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_, lean_object* v___y_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_){
_start:
{
lean_object* v_res_6795_; 
v_res_6795_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6781_, v_x_6782_, v___y_6783_, v___y_6784_, v___y_6785_, v___y_6786_, v___y_6787_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_);
lean_dec(v___y_6793_);
lean_dec_ref(v___y_6792_);
lean_dec(v___y_6791_);
lean_dec_ref(v___y_6790_);
lean_dec(v___y_6789_);
lean_dec_ref(v___y_6788_);
lean_dec(v___y_6787_);
lean_dec_ref(v___y_6786_);
lean_dec(v___y_6785_);
lean_dec(v___y_6784_);
lean_dec_ref(v___y_6783_);
return v_res_6795_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6796_, lean_object* v_as_x27_6797_, lean_object* v_b_6798_, lean_object* v_a_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_, lean_object* v___y_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_, lean_object* v___y_6809_, lean_object* v___y_6810_){
_start:
{
lean_object* v___x_6812_; 
v___x_6812_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6797_, v_b_6798_, v___y_6800_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_);
return v___x_6812_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6813_, lean_object* v_as_x27_6814_, lean_object* v_b_6815_, lean_object* v_a_6816_, lean_object* v___y_6817_, lean_object* v___y_6818_, lean_object* v___y_6819_, lean_object* v___y_6820_, lean_object* v___y_6821_, lean_object* v___y_6822_, lean_object* v___y_6823_, lean_object* v___y_6824_, lean_object* v___y_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_){
_start:
{
lean_object* v_res_6829_; 
v_res_6829_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6813_, v_as_x27_6814_, v_b_6815_, v_a_6816_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_, v___y_6821_, v___y_6822_, v___y_6823_, v___y_6824_, v___y_6825_, v___y_6826_, v___y_6827_);
lean_dec(v___y_6827_);
lean_dec_ref(v___y_6826_);
lean_dec(v___y_6825_);
lean_dec_ref(v___y_6824_);
lean_dec(v___y_6823_);
lean_dec_ref(v___y_6822_);
lean_dec(v___y_6821_);
lean_dec_ref(v___y_6820_);
lean_dec(v___y_6819_);
lean_dec(v___y_6818_);
lean_dec_ref(v___y_6817_);
lean_dec(v_as_x27_6814_);
lean_dec(v_as_6813_);
return v_res_6829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6830_, lean_object* v_data_6831_, lean_object* v_ref_6832_, lean_object* v_msg_6833_, lean_object* v___y_6834_, lean_object* v___y_6835_, lean_object* v___y_6836_, lean_object* v___y_6837_, lean_object* v___y_6838_, lean_object* v___y_6839_, lean_object* v___y_6840_, lean_object* v___y_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_){
_start:
{
lean_object* v___x_6846_; 
v___x_6846_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6830_, v_data_6831_, v_ref_6832_, v_msg_6833_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_);
return v___x_6846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6847_, lean_object* v_data_6848_, lean_object* v_ref_6849_, lean_object* v_msg_6850_, lean_object* v___y_6851_, lean_object* v___y_6852_, lean_object* v___y_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_){
_start:
{
lean_object* v_res_6863_; 
v_res_6863_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6847_, v_data_6848_, v_ref_6849_, v_msg_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_, v___y_6861_);
lean_dec(v___y_6861_);
lean_dec_ref(v___y_6860_);
lean_dec(v___y_6859_);
lean_dec_ref(v___y_6858_);
lean_dec(v___y_6857_);
lean_dec_ref(v___y_6856_);
lean_dec(v___y_6855_);
lean_dec_ref(v___y_6854_);
lean_dec(v___y_6853_);
lean_dec(v___y_6852_);
lean_dec_ref(v___y_6851_);
return v_res_6863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6864_, lean_object* v_a_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_){
_start:
{
lean_object* v___x_6877_; 
v___x_6877_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6864_, v_a_6865_, v_a_6866_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_, v_a_6872_, v_a_6873_, v_a_6874_, v_a_6875_);
if (lean_obj_tag(v___x_6877_) == 0)
{
lean_object* v_a_6878_; lean_object* v___x_6879_; lean_object* v___x_6881_; uint8_t v_isShared_6882_; uint8_t v_isSharedCheck_6886_; 
v_a_6878_ = lean_ctor_get(v___x_6877_, 0);
lean_inc(v_a_6878_);
lean_dec_ref_known(v___x_6877_, 1);
v___x_6879_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_6865_, v_a_6866_);
v_isSharedCheck_6886_ = !lean_is_exclusive(v___x_6879_);
if (v_isSharedCheck_6886_ == 0)
{
lean_object* v_unused_6887_; 
v_unused_6887_ = lean_ctor_get(v___x_6879_, 0);
lean_dec(v_unused_6887_);
v___x_6881_ = v___x_6879_;
v_isShared_6882_ = v_isSharedCheck_6886_;
goto v_resetjp_6880_;
}
else
{
lean_dec(v___x_6879_);
v___x_6881_ = lean_box(0);
v_isShared_6882_ = v_isSharedCheck_6886_;
goto v_resetjp_6880_;
}
v_resetjp_6880_:
{
lean_object* v___x_6884_; 
if (v_isShared_6882_ == 0)
{
lean_ctor_set(v___x_6881_, 0, v_a_6878_);
v___x_6884_ = v___x_6881_;
goto v_reusejp_6883_;
}
else
{
lean_object* v_reuseFailAlloc_6885_; 
v_reuseFailAlloc_6885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6885_, 0, v_a_6878_);
v___x_6884_ = v_reuseFailAlloc_6885_;
goto v_reusejp_6883_;
}
v_reusejp_6883_:
{
return v___x_6884_;
}
}
}
else
{
return v___x_6877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6888_, lean_object* v_a_6889_, lean_object* v_a_6890_, lean_object* v_a_6891_, lean_object* v_a_6892_, lean_object* v_a_6893_, lean_object* v_a_6894_, lean_object* v_a_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_){
_start:
{
lean_object* v_res_6901_; 
v_res_6901_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6888_, v_a_6889_, v_a_6890_, v_a_6891_, v_a_6892_, v_a_6893_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_, v_a_6898_, v_a_6899_);
lean_dec(v_a_6899_);
lean_dec_ref(v_a_6898_);
lean_dec(v_a_6897_);
lean_dec_ref(v_a_6896_);
lean_dec(v_a_6895_);
lean_dec_ref(v_a_6894_);
lean_dec(v_a_6893_);
lean_dec_ref(v_a_6892_);
lean_dec(v_a_6891_);
lean_dec(v_a_6890_);
lean_dec_ref(v_a_6889_);
lean_dec(v_passes_6888_);
return v_res_6901_;
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
