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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17(void){
_start:
{
lean_object* v_cls_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v_cls_2643_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_2644_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16));
v___x_2645_ = l_Lean_Name_append(v___x_2644_, v_cls_2643_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2649_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2650_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2651_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2650_, v___x_2649_, v___x_2648_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___f_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; 
v___x_2652_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___f_2653_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2654_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_2655_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2654_, v___f_2653_, v___x_2652_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2656_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v___x_2657_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2658_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2659_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2658_, v___x_2657_, v___x_2656_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___f_2661_; lean_object* v___f_2662_; lean_object* v___x_2663_; 
v___x_2660_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22);
v___f_2661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2662_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_2663_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2662_, v___f_2661_, v___x_2660_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2664_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_2665_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2666_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2667_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2666_, v___x_2665_, v___x_2664_);
return v___x_2667_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25(void){
_start:
{
lean_object* v___x_2668_; lean_object* v___f_2669_; lean_object* v___f_2670_; lean_object* v___x_2671_; 
v___x_2668_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24);
v___f_2669_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2670_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_2671_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2670_, v___f_2669_, v___x_2668_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___x_2675_; 
v___x_2672_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25);
v___f_2673_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2674_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_2675_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2674_, v___f_2673_, v___x_2672_);
return v___x_2675_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2676_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26);
v___x_2677_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2678_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2679_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2678_, v___x_2677_, v___x_2676_);
return v___x_2679_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___f_2681_; lean_object* v___f_2682_; lean_object* v___x_2683_; 
v___x_2680_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27);
v___f_2681_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2682_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_2683_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2682_, v___f_2681_, v___x_2680_);
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
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v_options_2788_; uint8_t v_hasTrace_2789_; 
v___x_2780_ = l_StateRefT_x27_instMonad___redArg(v___x_2779_);
v___x_2781_ = l_ReaderT_instMonad___redArg(v___x_2780_);
v___x_2782_ = l_StateRefT_x27_instMonad___redArg(v___x_2781_);
v___x_2783_ = l_ReaderT_instMonad___redArg(v___x_2782_);
v___x_2784_ = l_ReaderT_instMonad___redArg(v___x_2783_);
v___x_2785_ = l_StateRefT_x27_instMonad___redArg(v___x_2784_);
v___x_2786_ = l_ReaderT_instMonad___redArg(v___x_2785_);
v___x_2787_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v_options_2788_ = lean_ctor_get(v_a_2718_, 2);
v_hasTrace_2789_ = lean_ctor_get_uint8(v_options_2788_, sizeof(void*)*1);
if (v_hasTrace_2789_ == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_object* v_inheritedTraceOptions_2790_; lean_object* v_cls_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v_inheritedTraceOptions_2790_ = lean_ctor_get(v_a_2718_, 13);
v_cls_2791_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_2792_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_2793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2790_, v_options_2788_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_object* v___x_2794_; lean_object* v_toMonadRef_2795_; lean_object* v_type_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_6452__overap_2801_; lean_object* v___x_2802_; 
v___x_2794_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_2795_ = lean_ctor_get(v___x_2794_, 0);
v_type_2796_ = lean_ctor_get(v_hyp_2708_, 1);
v___f_2797_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_2798_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_2796_);
v___x_2799_ = l_Lean_MessageData_ofExpr(v_type_2796_);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
lean_inc_ref(v_toMonadRef_2795_);
v___x_6452__overap_2801_ = l_Lean_addTrace___redArg(v___x_2786_, v___x_2787_, v_toMonadRef_2795_, v___f_2797_, v_cls_2791_, v___x_2800_);
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
v___x_2802_ = lean_apply_12(v___x_6452__overap_2801_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2823_, lean_object* v___f_2824_, lean_object* v___x_2825_, lean_object* v___f_2826_, lean_object* v___x_2827_, lean_object* v___f_2828_, lean_object* v___f_2829_, lean_object* v___x_2830_, lean_object* v___f_2831_, lean_object* v___x_2832_, lean_object* v___x_2833_, lean_object* v_x_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_options_2851_; uint8_t v_hasTrace_2852_; 
v_options_2851_ = lean_ctor_get(v___y_2845_, 2);
v_hasTrace_2852_ = lean_ctor_get_uint8(v_options_2851_, sizeof(void*)*1);
if (v_hasTrace_2852_ == 0)
{
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___x_2833_);
lean_dec_ref(v___x_2832_);
lean_dec(v___f_2831_);
lean_dec(v___x_2830_);
lean_dec(v___f_2829_);
lean_dec(v___f_2828_);
lean_dec(v___x_2827_);
lean_dec(v___f_2826_);
lean_dec(v___x_2825_);
lean_dec(v___f_2824_);
lean_dec(v___x_2823_);
goto v___jp_2848_;
}
else
{
lean_object* v_inheritedTraceOptions_2853_; lean_object* v_cls_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v_inheritedTraceOptions_2853_ = lean_ctor_get(v___y_2845_, 13);
v_cls_2854_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_2855_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_2856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2853_, v_options_2851_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___x_2833_);
lean_dec_ref(v___x_2832_);
lean_dec(v___f_2831_);
lean_dec(v___x_2830_);
lean_dec(v___f_2829_);
lean_dec(v___f_2828_);
lean_dec(v___x_2827_);
lean_dec(v___f_2826_);
lean_dec(v___x_2825_);
lean_dec(v___f_2824_);
lean_dec(v___x_2823_);
goto v___jp_2848_;
}
else
{
lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v_toMonadRef_2869_; lean_object* v_type_2870_; lean_object* v___x_2871_; lean_object* v___f_2872_; lean_object* v___f_2873_; lean_object* v___f_2874_; lean_object* v___f_2875_; lean_object* v___f_2876_; lean_object* v___f_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_7548__overap_2882_; lean_object* v___x_2883_; 
v___f_2857_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18));
v___x_2858_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2859_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2860_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2858_, v___x_2823_, v___x_2859_);
v___x_2861_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2857_, v___f_2824_, v___x_2860_);
lean_inc(v___x_2825_);
v___x_2862_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2858_, v___x_2825_, v___x_2861_);
lean_inc(v___f_2826_);
v___x_2863_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2857_, v___f_2826_, v___x_2862_);
lean_inc(v___x_2827_);
v___x_2864_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2858_, v___x_2827_, v___x_2863_);
lean_inc(v___f_2828_);
v___x_2865_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2857_, v___f_2828_, v___x_2864_);
lean_inc(v___f_2829_);
v___x_2866_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2857_, v___f_2829_, v___x_2865_);
lean_inc(v___x_2830_);
v___x_2867_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2858_, v___x_2830_, v___x_2866_);
lean_inc(v___f_2831_);
v___x_2868_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2857_, v___f_2831_, v___x_2867_);
v_toMonadRef_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc_ref(v_toMonadRef_2869_);
lean_dec_ref(v___x_2868_);
v_type_2870_ = lean_ctor_get(v___y_2835_, 1);
lean_inc_ref(v_type_2870_);
lean_dec_ref(v___y_2835_);
v___x_2871_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2872_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2872_, 0, v___x_2871_);
lean_closure_set(v___f_2872_, 1, v___x_2825_);
v___f_2873_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2873_, 0, v___f_2872_);
lean_closure_set(v___f_2873_, 1, v___f_2826_);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2874_, 0, v___f_2873_);
lean_closure_set(v___f_2874_, 1, v___x_2827_);
v___f_2875_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2875_, 0, v___f_2874_);
lean_closure_set(v___f_2875_, 1, v___f_2828_);
v___f_2876_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2876_, 0, v___f_2875_);
lean_closure_set(v___f_2876_, 1, v___f_2829_);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2877_, 0, v___f_2876_);
lean_closure_set(v___f_2877_, 1, v___x_2830_);
v___f_2878_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2878_, 0, v___f_2877_);
lean_closure_set(v___f_2878_, 1, v___f_2831_);
v___x_2879_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2880_ = l_Lean_MessageData_ofExpr(v_type_2870_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_7548__overap_2882_ = l_Lean_addTrace___redArg(v___x_2832_, v___x_2833_, v_toMonadRef_2869_, v___f_2878_, v_cls_2854_, v___x_2881_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc_ref(v___y_2841_);
lean_inc(v___y_2840_);
lean_inc_ref(v___y_2839_);
lean_inc(v___y_2838_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
v___x_2883_ = lean_apply_12(v___x_7548__overap_2882_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, lean_box(0));
return v___x_2883_;
}
}
v___jp_2848_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2884_ = _args[0];
lean_object* v___f_2885_ = _args[1];
lean_object* v___x_2886_ = _args[2];
lean_object* v___f_2887_ = _args[3];
lean_object* v___x_2888_ = _args[4];
lean_object* v___f_2889_ = _args[5];
lean_object* v___f_2890_ = _args[6];
lean_object* v___x_2891_ = _args[7];
lean_object* v___f_2892_ = _args[8];
lean_object* v___x_2893_ = _args[9];
lean_object* v___x_2894_ = _args[10];
lean_object* v_x_2895_ = _args[11];
lean_object* v___y_2896_ = _args[12];
lean_object* v___y_2897_ = _args[13];
lean_object* v___y_2898_ = _args[14];
lean_object* v___y_2899_ = _args[15];
lean_object* v___y_2900_ = _args[16];
lean_object* v___y_2901_ = _args[17];
lean_object* v___y_2902_ = _args[18];
lean_object* v___y_2903_ = _args[19];
lean_object* v___y_2904_ = _args[20];
lean_object* v___y_2905_ = _args[21];
lean_object* v___y_2906_ = _args[22];
lean_object* v___y_2907_ = _args[23];
lean_object* v___y_2908_ = _args[24];
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2884_, v___f_2885_, v___x_2886_, v___f_2887_, v___x_2888_, v___f_2889_, v___f_2890_, v___x_2891_, v___f_2892_, v___x_2893_, v___x_2894_, v_x_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___y_2942_; lean_object* v___x_2943_; lean_object* v_toApplicative_2944_; lean_object* v_toFunctor_2945_; lean_object* v_toSeq_2946_; lean_object* v_toSeqLeft_2947_; lean_object* v_toSeqRight_2948_; lean_object* v___f_2949_; lean_object* v___f_2950_; lean_object* v___f_2951_; lean_object* v___f_2952_; lean_object* v___x_2953_; lean_object* v___f_2954_; lean_object* v___f_2955_; lean_object* v___f_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v_toApplicative_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3011_; 
v___x_2943_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2944_ = lean_ctor_get(v___x_2943_, 0);
v_toFunctor_2945_ = lean_ctor_get(v_toApplicative_2944_, 0);
v_toSeq_2946_ = lean_ctor_get(v_toApplicative_2944_, 2);
v_toSeqLeft_2947_ = lean_ctor_get(v_toApplicative_2944_, 3);
v_toSeqRight_2948_ = lean_ctor_get(v_toApplicative_2944_, 4);
v___f_2949_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2945_, 2);
v___f_2951_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2951_, 0, v_toFunctor_2945_);
v___f_2952_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2952_, 0, v_toFunctor_2945_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___f_2951_);
lean_ctor_set(v___x_2953_, 1, v___f_2952_);
lean_inc(v_toSeqRight_2948_);
v___f_2954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2954_, 0, v_toSeqRight_2948_);
lean_inc(v_toSeqLeft_2947_);
v___f_2955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2955_, 0, v_toSeqLeft_2947_);
lean_inc(v_toSeq_2946_);
v___f_2956_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2956_, 0, v_toSeq_2946_);
v___x_2957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2953_);
lean_ctor_set(v___x_2957_, 1, v___f_2949_);
lean_ctor_set(v___x_2957_, 2, v___f_2956_);
lean_ctor_set(v___x_2957_, 3, v___f_2955_);
lean_ctor_set(v___x_2957_, 4, v___f_2954_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_ctor_set(v___x_2958_, 1, v___f_2950_);
v___x_2959_ = l_StateRefT_x27_instMonad___redArg(v___x_2958_);
v_toApplicative_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; 
v_unused_3012_ = lean_ctor_get(v___x_2959_, 1);
lean_dec(v_unused_3012_);
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_3011_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_toApplicative_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3011_;
goto v_resetjp_2961_;
}
v___jp_2923_:
{
lean_object* v___x_2924_; lean_object* v_caches_2925_; lean_object* v_typeAnalysis_2926_; lean_object* v_target_2927_; lean_object* v_hypotheses_2928_; uint8_t v_didChange_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2940_; 
v___x_2924_ = lean_st_ref_take(v_a_2912_);
v_caches_2925_ = lean_ctor_get(v___x_2924_, 0);
v_typeAnalysis_2926_ = lean_ctor_get(v___x_2924_, 1);
v_target_2927_ = lean_ctor_get(v___x_2924_, 2);
v_hypotheses_2928_ = lean_ctor_get(v___x_2924_, 3);
v_didChange_2929_ = lean_ctor_get_uint8(v___x_2924_, sizeof(void*)*4);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2931_ = v___x_2924_;
v_isShared_2932_ = v_isSharedCheck_2940_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_hypotheses_2928_);
lean_inc(v_target_2927_);
lean_inc(v_typeAnalysis_2926_);
lean_inc(v_caches_2925_);
lean_dec(v___x_2924_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2940_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = l_Array_append___redArg(v_hypotheses_2928_, v_hyps_2910_);
lean_dec_ref(v_hyps_2910_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 3, v___x_2933_);
v___x_2935_ = v___x_2931_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_caches_2925_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_typeAnalysis_2926_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_target_2927_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v___x_2933_);
lean_ctor_set_uint8(v_reuseFailAlloc_2939_, sizeof(void*)*4, v_didChange_2929_);
v___x_2935_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_st_ref_put(v_a_2912_, v___x_2935_);
v___x_2937_ = lean_box(0);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
}
v___jp_2941_:
{
if (lean_obj_tag(v___y_2942_) == 0)
{
lean_dec_ref_known(v___y_2942_, 1);
goto v___jp_2923_;
}
else
{
lean_dec_ref(v_hyps_2910_);
return v___y_2942_;
}
}
v_resetjp_2961_:
{
lean_object* v_toFunctor_2964_; lean_object* v_toSeq_2965_; lean_object* v_toSeqLeft_2966_; lean_object* v_toSeqRight_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3009_; 
v_toFunctor_2964_ = lean_ctor_get(v_toApplicative_2960_, 0);
v_toSeq_2965_ = lean_ctor_get(v_toApplicative_2960_, 2);
v_toSeqLeft_2966_ = lean_ctor_get(v_toApplicative_2960_, 3);
v_toSeqRight_2967_ = lean_ctor_get(v_toApplicative_2960_, 4);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_toApplicative_2960_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; 
v_unused_3010_ = lean_ctor_get(v_toApplicative_2960_, 1);
lean_dec(v_unused_3010_);
v___x_2969_ = v_toApplicative_2960_;
v_isShared_2970_ = v_isSharedCheck_3009_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_toSeqRight_2967_);
lean_inc(v_toSeqLeft_2966_);
lean_inc(v_toSeq_2965_);
lean_inc(v_toFunctor_2964_);
lean_dec(v_toApplicative_2960_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3009_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___f_2971_; lean_object* v___f_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v___f_2978_; lean_object* v___x_2980_; 
v___f_2971_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2972_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2964_);
v___f_2973_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2973_, 0, v_toFunctor_2964_);
v___f_2974_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2974_, 0, v_toFunctor_2964_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___f_2973_);
lean_ctor_set(v___x_2975_, 1, v___f_2974_);
v___f_2976_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2976_, 0, v_toSeqRight_2967_);
v___f_2977_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2977_, 0, v_toSeqLeft_2966_);
v___f_2978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2978_, 0, v_toSeq_2965_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 4, v___f_2976_);
lean_ctor_set(v___x_2969_, 3, v___f_2977_);
lean_ctor_set(v___x_2969_, 2, v___f_2978_);
lean_ctor_set(v___x_2969_, 1, v___f_2971_);
lean_ctor_set(v___x_2969_, 0, v___x_2975_);
v___x_2980_ = v___x_2969_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___f_2971_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v___f_2978_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v___f_2977_);
lean_ctor_set(v_reuseFailAlloc_3008_, 4, v___f_2976_);
v___x_2980_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2982_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 1, v___f_2972_);
lean_ctor_set(v___x_2962_, 0, v___x_2980_);
v___x_2982_ = v___x_2962_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___f_2972_);
v___x_2982_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2983_ = l_StateRefT_x27_instMonad___redArg(v___x_2982_);
v___x_2984_ = l_ReaderT_instMonad___redArg(v___x_2983_);
v___x_2985_ = l_StateRefT_x27_instMonad___redArg(v___x_2984_);
v___x_2986_ = l_ReaderT_instMonad___redArg(v___x_2985_);
v___x_2987_ = l_ReaderT_instMonad___redArg(v___x_2986_);
v___x_2988_ = l_StateRefT_x27_instMonad___redArg(v___x_2987_);
v___x_2989_ = l_ReaderT_instMonad___redArg(v___x_2988_);
v___f_2990_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2991_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2992_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = lean_array_get_size(v_hyps_2910_);
v___x_2995_ = lean_nat_dec_lt(v___x_2993_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_dec_ref(v___x_2989_);
goto v___jp_2923_;
}
else
{
lean_object* v___f_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
lean_inc_ref(v___x_2989_);
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 25, 11);
lean_closure_set(v___f_2996_, 0, v___x_2991_);
lean_closure_set(v___f_2996_, 1, v___f_2990_);
lean_closure_set(v___f_2996_, 2, v___x_2991_);
lean_closure_set(v___f_2996_, 3, v___f_2990_);
lean_closure_set(v___f_2996_, 4, v___x_2991_);
lean_closure_set(v___f_2996_, 5, v___f_2990_);
lean_closure_set(v___f_2996_, 6, v___f_2990_);
lean_closure_set(v___f_2996_, 7, v___x_2991_);
lean_closure_set(v___f_2996_, 8, v___f_2990_);
lean_closure_set(v___f_2996_, 9, v___x_2989_);
lean_closure_set(v___f_2996_, 10, v___x_2992_);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_nat_dec_le(v___x_2994_, v___x_2994_);
if (v___x_2998_ == 0)
{
if (v___x_2995_ == 0)
{
lean_dec_ref(v___f_2996_);
lean_dec_ref(v___x_2989_);
goto v___jp_2923_;
}
else
{
size_t v___x_2999_; size_t v___x_3000_; lean_object* v___x_7104__overap_3001_; lean_object* v___x_3002_; 
v___x_2999_ = ((size_t)0ULL);
v___x_3000_ = lean_usize_of_nat(v___x_2994_);
lean_inc_ref(v_hyps_2910_);
v___x_7104__overap_3001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2989_, v___f_2996_, v_hyps_2910_, v___x_2999_, v___x_3000_, v___x_2997_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
lean_inc(v_a_2919_);
lean_inc_ref(v_a_2918_);
lean_inc(v_a_2917_);
lean_inc_ref(v_a_2916_);
lean_inc(v_a_2915_);
lean_inc_ref(v_a_2914_);
lean_inc(v_a_2913_);
lean_inc(v_a_2912_);
lean_inc_ref(v_a_2911_);
v___x_3002_ = lean_apply_12(v___x_7104__overap_3001_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, lean_box(0));
v___y_2942_ = v___x_3002_;
goto v___jp_2941_;
}
}
else
{
size_t v___x_3003_; size_t v___x_3004_; lean_object* v___x_7108__overap_3005_; lean_object* v___x_3006_; 
v___x_3003_ = ((size_t)0ULL);
v___x_3004_ = lean_usize_of_nat(v___x_2994_);
lean_inc_ref(v_hyps_2910_);
v___x_7108__overap_3005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2989_, v___f_2996_, v_hyps_2910_, v___x_3003_, v___x_3004_, v___x_2997_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
lean_inc(v_a_2919_);
lean_inc_ref(v_a_2918_);
lean_inc(v_a_2917_);
lean_inc_ref(v_a_2916_);
lean_inc(v_a_2915_);
lean_inc_ref(v_a_2914_);
lean_inc(v_a_2913_);
lean_inc(v_a_2912_);
lean_inc_ref(v_a_2911_);
v___x_3006_ = lean_apply_12(v___x_7108__overap_3005_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, lean_box(0));
v___y_2942_ = v___x_3006_;
goto v___jp_2941_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_3027_){
_start:
{
lean_object* v___x_3029_; lean_object* v_hypotheses_3030_; lean_object* v___x_3031_; 
v___x_3029_ = lean_st_ref_get(v_a_3027_);
v_hypotheses_3030_ = lean_ctor_get(v___x_3029_, 3);
lean_inc_ref(v_hypotheses_3030_);
lean_dec(v___x_3029_);
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_hypotheses_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_3032_);
lean_dec(v_a_3032_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3047_; lean_object* v_hypotheses_3048_; lean_object* v___x_3049_; 
v___x_3047_ = lean_st_ref_get(v_a_3036_);
v_hypotheses_3048_ = lean_ctor_get(v___x_3047_, 3);
lean_inc_ref(v_hypotheses_3048_);
lean_dec(v___x_3047_);
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_hypotheses_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; lean_object* v_caches_3077_; lean_object* v_typeAnalysis_3078_; lean_object* v_target_3079_; uint8_t v_didChange_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3090_; 
v___x_3076_ = lean_st_ref_take(v___y_3065_);
v_caches_3077_ = lean_ctor_get(v___x_3076_, 0);
v_typeAnalysis_3078_ = lean_ctor_get(v___x_3076_, 1);
v_target_3079_ = lean_ctor_get(v___x_3076_, 2);
v_didChange_3080_ = lean_ctor_get_uint8(v___x_3076_, sizeof(void*)*4);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3076_, 3);
lean_dec(v_unused_3091_);
v___x_3082_ = v___x_3076_;
v_isShared_3083_ = v_isSharedCheck_3090_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_target_3079_);
lean_inc(v_typeAnalysis_3078_);
lean_inc(v_caches_3077_);
lean_dec(v___x_3076_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3090_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 3, v_hyps_3063_);
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_caches_3077_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_typeAnalysis_3078_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_target_3079_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_hyps_3063_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*4, v_didChange_3080_);
v___x_3085_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_st_ref_put(v___y_3065_, v___x_3085_);
v___x_3087_ = lean_box(0);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3106_, lean_object* v_hyps_3107_){
_start:
{
lean_object* v___f_3108_; lean_object* v___x_3109_; 
v___f_3108_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3108_, 0, v_hyps_3107_);
v___x_3109_ = lean_apply_2(v_inst_3106_, lean_box(0), v___f_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v___x_3122_; lean_object* v_caches_3123_; lean_object* v_typeAnalysis_3124_; lean_object* v_target_3125_; uint8_t v_didChange_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3137_; 
v___x_3122_ = lean_st_ref_take(v___y_3111_);
v_caches_3123_ = lean_ctor_get(v___x_3122_, 0);
v_typeAnalysis_3124_ = lean_ctor_get(v___x_3122_, 1);
v_target_3125_ = lean_ctor_get(v___x_3122_, 2);
v_didChange_3126_ = lean_ctor_get_uint8(v___x_3122_, sizeof(void*)*4);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___x_3122_, 3);
lean_dec(v_unused_3138_);
v___x_3128_ = v___x_3122_;
v_isShared_3129_ = v_isSharedCheck_3137_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_target_3125_);
lean_inc(v_typeAnalysis_3124_);
lean_inc(v_caches_3123_);
lean_dec(v___x_3122_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3137_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 3, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_caches_3123_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_typeAnalysis_3124_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_target_3125_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v___x_3130_);
lean_ctor_set_uint8(v_reuseFailAlloc_3136_, sizeof(void*)*4, v_didChange_3126_);
v___x_3132_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = lean_st_ref_put(v___y_3111_, v___x_3132_);
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3152_, lean_object* v_cls_3153_, lean_object* v_____do__lift_3154_, lean_object* v_____do__lift_3155_){
_start:
{
uint8_t v_hasTrace_3156_; 
v_hasTrace_3156_ = lean_ctor_get_uint8(v_____do__lift_3155_, sizeof(void*)*1);
if (v_hasTrace_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_dec(v_cls_3153_);
v___x_3157_ = lean_box(v_hasTrace_3156_);
v___x_3158_ = lean_apply_2(v_toPure_3152_, lean_box(0), v___x_3157_);
return v___x_3158_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16));
v___x_3160_ = l_Lean_Name_append(v___x_3159_, v_cls_3153_);
v___x_3161_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3154_, v_____do__lift_3155_, v___x_3160_);
lean_dec(v___x_3160_);
v___x_3162_ = lean_box(v___x_3161_);
v___x_3163_ = lean_apply_2(v_toPure_3152_, lean_box(0), v___x_3162_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3164_, lean_object* v_cls_3165_, lean_object* v_____do__lift_3166_, lean_object* v_____do__lift_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3164_, v_cls_3165_, v_____do__lift_3166_, v_____do__lift_3167_);
lean_dec_ref(v_____do__lift_3167_);
lean_dec_ref(v_____do__lift_3166_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_toPure_3169_, lean_object* v_cls_3170_, lean_object* v_toBind_3171_, lean_object* v_inst_3172_, lean_object* v_____do__lift_3173_){
_start:
{
lean_object* v___f_3174_; lean_object* v___x_3175_; 
v___f_3174_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3174_, 0, v_toPure_3169_);
lean_closure_set(v___f_3174_, 1, v_cls_3170_);
lean_closure_set(v___f_3174_, 2, v_____do__lift_3173_);
v___x_3175_ = lean_apply_4(v_toBind_3171_, lean_box(0), lean_box(0), v_inst_3172_, v___f_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3178_ = l_Lean_stringToMessageData(v___x_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3179_, lean_object* v_a_3180_, lean_object* v___y_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_cls_3186_, uint8_t v_____do__lift_3187_){
_start:
{
if (v_____do__lift_3187_ == 0)
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_dec(v_cls_3186_);
lean_dec(v_inst_3185_);
lean_dec_ref(v_inst_3184_);
lean_dec_ref(v_inst_3183_);
lean_dec_ref(v_inst_3182_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v_a_3180_);
v___x_3188_ = lean_box(0);
v___x_3189_ = lean_apply_2(v_toPure_3179_, lean_box(0), v___x_3188_);
return v___x_3189_;
}
else
{
lean_object* v_type_3190_; lean_object* v_type_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_dec(v_toPure_3179_);
v_type_3190_ = lean_ctor_get(v_a_3180_, 1);
lean_inc_ref(v_type_3190_);
lean_dec_ref(v_a_3180_);
v_type_3191_ = lean_ctor_get(v___y_3181_, 1);
lean_inc_ref(v_type_3191_);
lean_dec_ref(v___y_3181_);
v___x_3192_ = l_Lean_MessageData_ofExpr(v_type_3190_);
v___x_3193_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Lean_MessageData_ofExpr(v_type_3191_);
v___x_3196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = l_Lean_addTrace___redArg(v_inst_3182_, v_inst_3183_, v_inst_3184_, v_inst_3185_, v_cls_3186_, v___x_3196_);
return v___x_3197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3198_, lean_object* v_a_3199_, lean_object* v___y_3200_, lean_object* v_inst_3201_, lean_object* v_inst_3202_, lean_object* v_inst_3203_, lean_object* v_inst_3204_, lean_object* v_cls_3205_, lean_object* v_____do__lift_3206_){
_start:
{
uint8_t v_____do__lift_3352__boxed_3207_; lean_object* v_res_3208_; 
v_____do__lift_3352__boxed_3207_ = lean_unbox(v_____do__lift_3206_);
v_res_3208_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3198_, v_a_3199_, v___y_3200_, v_inst_3201_, v_inst_3202_, v_inst_3203_, v_inst_3204_, v_cls_3205_, v_____do__lift_3352__boxed_3207_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3209_, lean_object* v_toPure_3210_, lean_object* v_toBind_3211_, lean_object* v_inst_3212_, lean_object* v_a_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_x_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_getInheritedTraceOptions_3219_; lean_object* v_cls_3220_; lean_object* v___f_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_getInheritedTraceOptions_3219_ = lean_ctor_get(v_inst_3209_, 2);
lean_inc(v_getInheritedTraceOptions_3219_);
v_cls_3220_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
lean_inc_n(v_toBind_3211_, 2);
lean_inc(v_toPure_3210_);
v___f_3221_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3221_, 0, v_toPure_3210_);
lean_closure_set(v___f_3221_, 1, v_cls_3220_);
lean_closure_set(v___f_3221_, 2, v_toBind_3211_);
lean_closure_set(v___f_3221_, 3, v_inst_3212_);
v___f_3222_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3222_, 0, v_toPure_3210_);
lean_closure_set(v___f_3222_, 1, v_a_3213_);
lean_closure_set(v___f_3222_, 2, v___y_3218_);
lean_closure_set(v___f_3222_, 3, v_inst_3214_);
lean_closure_set(v___f_3222_, 4, v_inst_3209_);
lean_closure_set(v___f_3222_, 5, v_inst_3215_);
lean_closure_set(v___f_3222_, 6, v_inst_3216_);
lean_closure_set(v___f_3222_, 7, v_cls_3220_);
v___x_3223_ = lean_apply_4(v_toBind_3211_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3219_, v___f_3221_);
v___x_3224_ = lean_apply_4(v_toBind_3211_, lean_box(0), lean_box(0), v___x_3223_, v___f_3222_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3225_, lean_object* v_res_3226_, lean_object* v_____r_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_apply_2(v_toPure_3225_, lean_box(0), v_res_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3229_, lean_object* v_toBind_3230_, lean_object* v___f_3231_, lean_object* v_____r_3232_){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3234_ = lean_apply_2(v_inst_3229_, lean_box(0), v___x_3233_);
v___x_3235_ = lean_apply_4(v_toBind_3230_, lean_box(0), lean_box(0), v___x_3234_, v___f_3231_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3236_, lean_object* v_____r_3237_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_apply_1(v___f_3236_, v_____r_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3239_, lean_object* v_type_3240_, lean_object* v_type_3241_, lean_object* v_inst_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_cls_3246_, lean_object* v_toBind_3247_, lean_object* v___f_3248_, uint8_t v_____do__lift_3249_){
_start:
{
if (v_____do__lift_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec(v___f_3248_);
lean_dec(v_toBind_3247_);
lean_dec(v_cls_3246_);
lean_dec(v_inst_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_inst_3243_);
lean_dec_ref(v_inst_3242_);
lean_dec_ref(v_type_3241_);
lean_dec_ref(v_type_3240_);
v___x_3250_ = lean_box(0);
v___x_3251_ = lean_apply_1(v___f_3239_, v___x_3250_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_dec(v___f_3239_);
v___x_3252_ = l_Lean_MessageData_ofExpr(v_type_3240_);
v___x_3253_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_MessageData_ofExpr(v_type_3241_);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_addTrace___redArg(v_inst_3242_, v_inst_3243_, v_inst_3244_, v_inst_3245_, v_cls_3246_, v___x_3256_);
v___x_3258_ = lean_apply_4(v_toBind_3247_, lean_box(0), lean_box(0), v___x_3257_, v___f_3248_);
return v___x_3258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3259_, lean_object* v_type_3260_, lean_object* v_type_3261_, lean_object* v_inst_3262_, lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_cls_3266_, lean_object* v_toBind_3267_, lean_object* v___f_3268_, lean_object* v_____do__lift_3269_){
_start:
{
uint8_t v_____do__lift_3452__boxed_3270_; lean_object* v_res_3271_; 
v_____do__lift_3452__boxed_3270_ = lean_unbox(v_____do__lift_3269_);
v_res_3271_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3259_, v_type_3260_, v_type_3261_, v_inst_3262_, v_inst_3263_, v_inst_3264_, v_inst_3265_, v_cls_3266_, v_toBind_3267_, v___f_3268_, v_____do__lift_3452__boxed_3270_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3272_, lean_object* v_inst_3273_, lean_object* v_toBind_3274_, lean_object* v_inst_3275_, lean_object* v___f_3276_, lean_object* v_a_3277_, lean_object* v_inst_3278_, lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_inst_3281_, lean_object* v___f_3282_, lean_object* v_res_3283_){
_start:
{
lean_object* v___x_3284_; lean_object* v_zero_3285_; uint8_t v_isZero_3286_; 
v___x_3284_ = lean_array_get_size(v_res_3283_);
v_zero_3285_ = lean_unsigned_to_nat(0u);
v_isZero_3286_ = lean_nat_dec_eq(v___x_3284_, v_zero_3285_);
if (v_isZero_3286_ == 1)
{
lean_object* v___f_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
lean_dec(v___f_3282_);
lean_dec(v_inst_3281_);
lean_dec_ref(v_inst_3280_);
lean_dec(v_inst_3279_);
lean_dec_ref(v_inst_3278_);
lean_dec_ref(v_a_3277_);
lean_inc_ref(v_res_3283_);
lean_inc(v_toPure_3272_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3287_, 0, v_toPure_3272_);
lean_closure_set(v___f_3287_, 1, v_res_3283_);
lean_inc(v_toBind_3274_);
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3288_, 0, v_inst_3273_);
lean_closure_set(v___f_3288_, 1, v_toBind_3274_);
lean_closure_set(v___f_3288_, 2, v___f_3287_);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_nat_dec_lt(v_zero_3285_, v___x_3284_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_dec_ref(v_res_3283_);
lean_dec(v___f_3276_);
lean_dec_ref(v_inst_3275_);
v___x_3291_ = lean_apply_2(v_toPure_3272_, lean_box(0), v___x_3289_);
v___x_3292_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3291_, v___f_3288_);
return v___x_3292_;
}
else
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_nat_dec_le(v___x_3284_, v___x_3284_);
if (v___x_3293_ == 0)
{
if (v___x_3290_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec_ref(v_res_3283_);
lean_dec(v___f_3276_);
lean_dec_ref(v_inst_3275_);
v___x_3294_ = lean_apply_2(v_toPure_3272_, lean_box(0), v___x_3289_);
v___x_3295_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3294_, v___f_3288_);
return v___x_3295_;
}
else
{
size_t v___x_3296_; size_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v_toPure_3272_);
v___x_3296_ = ((size_t)0ULL);
v___x_3297_ = lean_usize_of_nat(v___x_3284_);
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3275_, v___f_3276_, v_res_3283_, v___x_3296_, v___x_3297_, v___x_3289_);
v___x_3299_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3298_, v___f_3288_);
return v___x_3299_;
}
}
else
{
size_t v___x_3300_; size_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec(v_toPure_3272_);
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = lean_usize_of_nat(v___x_3284_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3275_, v___f_3276_, v_res_3283_, v___x_3300_, v___x_3301_, v___x_3289_);
v___x_3303_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3302_, v___f_3288_);
return v___x_3303_;
}
}
}
else
{
lean_object* v_one_3304_; lean_object* v_n_3305_; uint8_t v_isZero_3306_; 
lean_dec(v___f_3276_);
v_one_3304_ = lean_unsigned_to_nat(1u);
v_n_3305_ = lean_nat_sub(v___x_3284_, v_one_3304_);
v_isZero_3306_ = lean_nat_dec_eq(v_n_3305_, v_zero_3285_);
lean_dec(v_n_3305_);
if (v_isZero_3306_ == 1)
{
lean_object* v_newHyp_3307_; lean_object* v_type_3308_; lean_object* v_type_3309_; uint8_t v___x_3310_; 
lean_dec(v___f_3282_);
v_newHyp_3307_ = lean_array_fget_borrowed(v_res_3283_, v_zero_3285_);
v_type_3308_ = lean_ctor_get(v_newHyp_3307_, 1);
v_type_3309_ = lean_ctor_get(v_a_3277_, 1);
lean_inc_ref(v_type_3309_);
lean_dec_ref(v_a_3277_);
v___x_3310_ = lean_expr_eqv(v_type_3308_, v_type_3309_);
if (v___x_3310_ == 0)
{
lean_object* v_getInheritedTraceOptions_3311_; lean_object* v___f_3312_; lean_object* v___f_3313_; lean_object* v___f_3314_; lean_object* v_cls_3315_; lean_object* v___f_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_inc_ref(v_type_3308_);
v_getInheritedTraceOptions_3311_ = lean_ctor_get(v_inst_3278_, 2);
lean_inc(v_getInheritedTraceOptions_3311_);
lean_inc(v_toPure_3272_);
v___f_3312_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3312_, 0, v_toPure_3272_);
lean_closure_set(v___f_3312_, 1, v_res_3283_);
lean_inc_n(v_toBind_3274_, 4);
v___f_3313_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3313_, 0, v_inst_3273_);
lean_closure_set(v___f_3313_, 1, v_toBind_3274_);
lean_closure_set(v___f_3313_, 2, v___f_3312_);
lean_inc_ref(v___f_3313_);
v___f_3314_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3314_, 0, v___f_3313_);
v_cls_3315_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___f_3316_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3316_, 0, v_toPure_3272_);
lean_closure_set(v___f_3316_, 1, v_cls_3315_);
lean_closure_set(v___f_3316_, 2, v_toBind_3274_);
lean_closure_set(v___f_3316_, 3, v_inst_3279_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3317_, 0, v___f_3313_);
lean_closure_set(v___f_3317_, 1, v_type_3309_);
lean_closure_set(v___f_3317_, 2, v_type_3308_);
lean_closure_set(v___f_3317_, 3, v_inst_3275_);
lean_closure_set(v___f_3317_, 4, v_inst_3278_);
lean_closure_set(v___f_3317_, 5, v_inst_3280_);
lean_closure_set(v___f_3317_, 6, v_inst_3281_);
lean_closure_set(v___f_3317_, 7, v_cls_3315_);
lean_closure_set(v___f_3317_, 8, v_toBind_3274_);
lean_closure_set(v___f_3317_, 9, v___f_3314_);
v___x_3318_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3311_, v___f_3316_);
v___x_3319_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3318_, v___f_3317_);
return v___x_3319_;
}
else
{
lean_object* v___x_3320_; 
lean_dec_ref(v_type_3309_);
lean_dec(v_inst_3281_);
lean_dec_ref(v_inst_3280_);
lean_dec(v_inst_3279_);
lean_dec_ref(v_inst_3278_);
lean_dec_ref(v_inst_3275_);
lean_dec(v_toBind_3274_);
lean_dec(v_inst_3273_);
v___x_3320_ = lean_apply_2(v_toPure_3272_, lean_box(0), v_res_3283_);
return v___x_3320_;
}
}
else
{
lean_object* v___f_3321_; lean_object* v___f_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
lean_dec(v_inst_3281_);
lean_dec_ref(v_inst_3280_);
lean_dec(v_inst_3279_);
lean_dec_ref(v_inst_3278_);
lean_dec_ref(v_a_3277_);
lean_inc_ref(v_res_3283_);
lean_inc(v_toPure_3272_);
v___f_3321_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3321_, 0, v_toPure_3272_);
lean_closure_set(v___f_3321_, 1, v_res_3283_);
lean_inc(v_toBind_3274_);
v___f_3322_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3322_, 0, v_inst_3273_);
lean_closure_set(v___f_3322_, 1, v_toBind_3274_);
lean_closure_set(v___f_3322_, 2, v___f_3321_);
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_nat_dec_lt(v_zero_3285_, v___x_3284_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec_ref(v_res_3283_);
lean_dec(v___f_3282_);
lean_dec_ref(v_inst_3275_);
v___x_3325_ = lean_apply_2(v_toPure_3272_, lean_box(0), v___x_3323_);
v___x_3326_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3325_, v___f_3322_);
return v___x_3326_;
}
else
{
uint8_t v___x_3327_; 
v___x_3327_ = lean_nat_dec_le(v___x_3284_, v___x_3284_);
if (v___x_3327_ == 0)
{
if (v___x_3324_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec_ref(v_res_3283_);
lean_dec(v___f_3282_);
lean_dec_ref(v_inst_3275_);
v___x_3328_ = lean_apply_2(v_toPure_3272_, lean_box(0), v___x_3323_);
v___x_3329_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3328_, v___f_3322_);
return v___x_3329_;
}
else
{
size_t v___x_3330_; size_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec(v_toPure_3272_);
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = lean_usize_of_nat(v___x_3284_);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3275_, v___f_3282_, v_res_3283_, v___x_3330_, v___x_3331_, v___x_3323_);
v___x_3333_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3332_, v___f_3322_);
return v___x_3333_;
}
}
else
{
size_t v___x_3334_; size_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
lean_dec(v_toPure_3272_);
v___x_3334_ = ((size_t)0ULL);
v___x_3335_ = lean_usize_of_nat(v___x_3284_);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3275_, v___f_3282_, v_res_3283_, v___x_3334_, v___x_3335_, v___x_3323_);
v___x_3337_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3336_, v___f_3322_);
return v___x_3337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3338_, lean_object* v_toPure_3339_, lean_object* v_____do__lift_3340_){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = l_Array_append___redArg(v_bs_3338_, v_____do__lift_3340_);
v___x_3342_ = lean_apply_2(v_toPure_3339_, lean_box(0), v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3343_, lean_object* v_toPure_3344_, lean_object* v_____do__lift_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3343_, v_toPure_3344_, v_____do__lift_3345_);
lean_dec_ref(v_____do__lift_3345_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3347_, lean_object* v_toPure_3348_, lean_object* v_toBind_3349_, lean_object* v_inst_3350_, lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_inst_3354_, lean_object* v_f_3355_, lean_object* v_bs_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v___f_3358_; lean_object* v___f_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_inc(v_inst_3353_);
lean_inc_ref(v_inst_3352_);
lean_inc_ref(v_inst_3351_);
lean_inc_ref_n(v_a_3357_, 2);
lean_inc(v_inst_3350_);
lean_inc_n(v_toBind_3349_, 3);
lean_inc_n(v_toPure_3348_, 2);
lean_inc_ref(v_inst_3347_);
v___f_3358_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3358_, 0, v_inst_3347_);
lean_closure_set(v___f_3358_, 1, v_toPure_3348_);
lean_closure_set(v___f_3358_, 2, v_toBind_3349_);
lean_closure_set(v___f_3358_, 3, v_inst_3350_);
lean_closure_set(v___f_3358_, 4, v_a_3357_);
lean_closure_set(v___f_3358_, 5, v_inst_3351_);
lean_closure_set(v___f_3358_, 6, v_inst_3352_);
lean_closure_set(v___f_3358_, 7, v_inst_3353_);
lean_inc_ref(v___f_3358_);
v___f_3359_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3359_, 0, v_toPure_3348_);
lean_closure_set(v___f_3359_, 1, v_inst_3354_);
lean_closure_set(v___f_3359_, 2, v_toBind_3349_);
lean_closure_set(v___f_3359_, 3, v_inst_3351_);
lean_closure_set(v___f_3359_, 4, v___f_3358_);
lean_closure_set(v___f_3359_, 5, v_a_3357_);
lean_closure_set(v___f_3359_, 6, v_inst_3347_);
lean_closure_set(v___f_3359_, 7, v_inst_3350_);
lean_closure_set(v___f_3359_, 8, v_inst_3352_);
lean_closure_set(v___f_3359_, 9, v_inst_3353_);
lean_closure_set(v___f_3359_, 10, v___f_3358_);
v___f_3360_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3360_, 0, v_bs_3356_);
lean_closure_set(v___f_3360_, 1, v_toPure_3348_);
v___x_3361_ = lean_apply_1(v_f_3355_, v_a_3357_);
v___x_3362_ = lean_apply_4(v_toBind_3349_, lean_box(0), lean_box(0), v___x_3361_, v___f_3359_);
v___x_3363_ = lean_apply_4(v_toBind_3349_, lean_box(0), lean_box(0), v___x_3362_, v___f_3360_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3366_, lean_object* v_toPure_3367_, lean_object* v_toBind_3368_, lean_object* v___f_3369_, lean_object* v_inst_3370_, lean_object* v___f_3371_, lean_object* v_____r_3372_){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; uint8_t v___x_3376_; 
v___x_3373_ = lean_unsigned_to_nat(0u);
v___x_3374_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3375_ = lean_array_get_size(v_hyps_3366_);
v___x_3376_ = lean_nat_dec_lt(v___x_3373_, v___x_3375_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec(v___f_3371_);
lean_dec_ref(v_inst_3370_);
lean_dec_ref(v_hyps_3366_);
v___x_3377_ = lean_apply_2(v_toPure_3367_, lean_box(0), v___x_3374_);
v___x_3378_ = lean_apply_4(v_toBind_3368_, lean_box(0), lean_box(0), v___x_3377_, v___f_3369_);
return v___x_3378_;
}
else
{
uint8_t v___x_3379_; 
v___x_3379_ = lean_nat_dec_le(v___x_3375_, v___x_3375_);
if (v___x_3379_ == 0)
{
if (v___x_3376_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec(v___f_3371_);
lean_dec_ref(v_inst_3370_);
lean_dec_ref(v_hyps_3366_);
v___x_3380_ = lean_apply_2(v_toPure_3367_, lean_box(0), v___x_3374_);
v___x_3381_ = lean_apply_4(v_toBind_3368_, lean_box(0), lean_box(0), v___x_3380_, v___f_3369_);
return v___x_3381_;
}
else
{
size_t v___x_3382_; size_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec(v_toPure_3367_);
v___x_3382_ = ((size_t)0ULL);
v___x_3383_ = lean_usize_of_nat(v___x_3375_);
v___x_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3370_, v___f_3371_, v_hyps_3366_, v___x_3382_, v___x_3383_, v___x_3374_);
v___x_3385_ = lean_apply_4(v_toBind_3368_, lean_box(0), lean_box(0), v___x_3384_, v___f_3369_);
return v___x_3385_;
}
}
else
{
size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_dec(v_toPure_3367_);
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = lean_usize_of_nat(v___x_3375_);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3370_, v___f_3371_, v_hyps_3366_, v___x_3386_, v___x_3387_, v___x_3374_);
v___x_3389_ = lean_apply_4(v_toBind_3368_, lean_box(0), lean_box(0), v___x_3388_, v___f_3369_);
return v___x_3389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3390_, lean_object* v_toBind_3391_, lean_object* v___f_3392_, lean_object* v_inst_3393_, lean_object* v___f_3394_, lean_object* v_inst_3395_, lean_object* v___f_3396_, lean_object* v_hyps_3397_){
_start:
{
lean_object* v___f_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_inc(v_toBind_3391_);
v___f_3398_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3398_, 0, v_hyps_3397_);
lean_closure_set(v___f_3398_, 1, v_toPure_3390_);
lean_closure_set(v___f_3398_, 2, v_toBind_3391_);
lean_closure_set(v___f_3398_, 3, v___f_3392_);
lean_closure_set(v___f_3398_, 4, v_inst_3393_);
lean_closure_set(v___f_3398_, 5, v___f_3394_);
v___x_3399_ = lean_apply_2(v_inst_3395_, lean_box(0), v___f_3396_);
v___x_3400_ = lean_apply_4(v_toBind_3391_, lean_box(0), lean_box(0), v___x_3399_, v___f_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_f_3408_){
_start:
{
lean_object* v_toApplicative_3409_; lean_object* v_toBind_3410_; lean_object* v_toPure_3411_; lean_object* v___f_3412_; lean_object* v___f_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___f_3416_; lean_object* v___f_3417_; lean_object* v___x_3418_; 
v_toApplicative_3409_ = lean_ctor_get(v_inst_3402_, 0);
v_toBind_3410_ = lean_ctor_get(v_inst_3402_, 1);
lean_inc_n(v_toBind_3410_, 3);
v_toPure_3411_ = lean_ctor_get(v_toApplicative_3409_, 1);
lean_inc_n(v_toPure_3411_, 2);
lean_inc_n(v_inst_3407_, 3);
v___f_3412_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3412_, 0, v_inst_3407_);
v___f_3413_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3414_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3415_ = lean_apply_2(v_inst_3407_, lean_box(0), v___x_3414_);
lean_inc_ref(v_inst_3402_);
v___f_3416_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3416_, 0, v_inst_3403_);
lean_closure_set(v___f_3416_, 1, v_toPure_3411_);
lean_closure_set(v___f_3416_, 2, v_toBind_3410_);
lean_closure_set(v___f_3416_, 3, v_inst_3404_);
lean_closure_set(v___f_3416_, 4, v_inst_3402_);
lean_closure_set(v___f_3416_, 5, v_inst_3406_);
lean_closure_set(v___f_3416_, 6, v_inst_3405_);
lean_closure_set(v___f_3416_, 7, v_inst_3407_);
lean_closure_set(v___f_3416_, 8, v_f_3408_);
v___f_3417_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3417_, 0, v_toPure_3411_);
lean_closure_set(v___f_3417_, 1, v_toBind_3410_);
lean_closure_set(v___f_3417_, 2, v___f_3412_);
lean_closure_set(v___f_3417_, 3, v_inst_3402_);
lean_closure_set(v___f_3417_, 4, v___f_3416_);
lean_closure_set(v___f_3417_, 5, v_inst_3407_);
lean_closure_set(v___f_3417_, 6, v___f_3413_);
v___x_3418_ = lean_apply_4(v_toBind_3410_, lean_box(0), lean_box(0), v___x_3415_, v___f_3417_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_inst_3423_, lean_object* v_inst_3424_, lean_object* v_inst_3425_, lean_object* v_f_3426_){
_start:
{
lean_object* v_toApplicative_3427_; lean_object* v_toBind_3428_; lean_object* v_toPure_3429_; lean_object* v___f_3430_; lean_object* v___f_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___f_3434_; lean_object* v___f_3435_; lean_object* v___x_3436_; 
v_toApplicative_3427_ = lean_ctor_get(v_inst_3420_, 0);
v_toBind_3428_ = lean_ctor_get(v_inst_3420_, 1);
lean_inc_n(v_toBind_3428_, 3);
v_toPure_3429_ = lean_ctor_get(v_toApplicative_3427_, 1);
lean_inc_n(v_toPure_3429_, 2);
lean_inc_n(v_inst_3425_, 3);
v___f_3430_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3430_, 0, v_inst_3425_);
v___f_3431_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3432_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3433_ = lean_apply_2(v_inst_3425_, lean_box(0), v___x_3432_);
lean_inc_ref(v_inst_3420_);
v___f_3434_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3434_, 0, v_inst_3421_);
lean_closure_set(v___f_3434_, 1, v_toPure_3429_);
lean_closure_set(v___f_3434_, 2, v_toBind_3428_);
lean_closure_set(v___f_3434_, 3, v_inst_3422_);
lean_closure_set(v___f_3434_, 4, v_inst_3420_);
lean_closure_set(v___f_3434_, 5, v_inst_3424_);
lean_closure_set(v___f_3434_, 6, v_inst_3423_);
lean_closure_set(v___f_3434_, 7, v_inst_3425_);
lean_closure_set(v___f_3434_, 8, v_f_3426_);
v___f_3435_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3435_, 0, v_toPure_3429_);
lean_closure_set(v___f_3435_, 1, v_toBind_3428_);
lean_closure_set(v___f_3435_, 2, v___f_3430_);
lean_closure_set(v___f_3435_, 3, v_inst_3420_);
lean_closure_set(v___f_3435_, 4, v___f_3434_);
lean_closure_set(v___f_3435_, 5, v_inst_3425_);
lean_closure_set(v___f_3435_, 6, v___f_3431_);
v___x_3436_ = lean_apply_4(v_toBind_3428_, lean_box(0), lean_box(0), v___x_3433_, v___f_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3437_, lean_object* v_____do__lift_3438_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_apply_2(v_toPure_3437_, lean_box(0), v_____do__lift_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_toPure_3440_, lean_object* v_____r_3441_){
_start:
{
uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = 0;
v___x_3443_ = lean_box(v___x_3442_);
v___x_3444_ = lean_apply_2(v_toPure_3440_, lean_box(0), v___x_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_snd_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; lean_object* v_caches_3459_; lean_object* v_typeAnalysis_3460_; lean_object* v_target_3461_; uint8_t v_didChange_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3472_; 
v___x_3458_ = lean_st_ref_take(v___y_3447_);
v_caches_3459_ = lean_ctor_get(v___x_3458_, 0);
v_typeAnalysis_3460_ = lean_ctor_get(v___x_3458_, 1);
v_target_3461_ = lean_ctor_get(v___x_3458_, 2);
v_didChange_3462_ = lean_ctor_get_uint8(v___x_3458_, sizeof(void*)*4);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v___x_3458_, 3);
lean_dec(v_unused_3473_);
v___x_3464_ = v___x_3458_;
v_isShared_3465_ = v_isSharedCheck_3472_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_target_3461_);
lean_inc(v_typeAnalysis_3460_);
lean_inc(v_caches_3459_);
lean_dec(v___x_3458_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3472_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 3, v_snd_3445_);
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_caches_3459_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_typeAnalysis_3460_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_target_3461_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_snd_3445_);
lean_ctor_set_uint8(v_reuseFailAlloc_3471_, sizeof(void*)*4, v_didChange_3462_);
v___x_3467_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = lean_st_ref_put(v___y_3447_, v___x_3467_);
v___x_3469_ = lean_box(0);
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
return v___x_3470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object* v_snd_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(v_snd_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_inst_3488_, lean_object* v_toBind_3489_, lean_object* v___f_3490_, lean_object* v_toPure_3491_, lean_object* v_____s_3492_){
_start:
{
lean_object* v_fst_3493_; 
v_fst_3493_ = lean_ctor_get(v_____s_3492_, 0);
if (lean_obj_tag(v_fst_3493_) == 0)
{
lean_object* v_snd_3494_; lean_object* v___f_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_dec(v_toPure_3491_);
v_snd_3494_ = lean_ctor_get(v_____s_3492_, 1);
lean_inc(v_snd_3494_);
lean_dec_ref(v_____s_3492_);
v___f_3495_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed), 13, 1);
lean_closure_set(v___f_3495_, 0, v_snd_3494_);
v___x_3496_ = lean_apply_2(v_inst_3488_, lean_box(0), v___f_3495_);
v___x_3497_ = lean_apply_4(v_toBind_3489_, lean_box(0), lean_box(0), v___x_3496_, v___f_3490_);
return v___x_3497_;
}
else
{
lean_object* v_val_3498_; lean_object* v___x_3499_; 
lean_inc_ref(v_fst_3493_);
lean_dec_ref(v_____s_3492_);
lean_dec(v___f_3490_);
lean_dec(v_toBind_3489_);
lean_dec(v_inst_3488_);
v_val_3498_ = lean_ctor_get(v_fst_3493_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v_fst_3493_, 1);
v___x_3499_ = lean_apply_2(v_toPure_3491_, lean_box(0), v_val_3498_);
return v___x_3499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3500_, lean_object* v_next_3501_, lean_object* v_G_3502_, lean_object* v_____do__lift_3503_){
_start:
{
if (lean_obj_tag(v_____do__lift_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
lean_dec(v_G_3502_);
v_a_3504_ = lean_ctor_get(v_____do__lift_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v_____do__lift_3503_, 1);
v___x_3505_ = lean_apply_2(v_toPure_3500_, lean_box(0), v_a_3504_);
return v___x_3505_;
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
lean_dec(v_toPure_3500_);
v_a_3506_ = lean_ctor_get(v_____do__lift_3503_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v_____do__lift_3503_, 1);
v___x_3507_ = lean_unsigned_to_nat(1u);
v___x_3508_ = lean_nat_add(v_next_3501_, v___x_3507_);
v___x_3509_ = lean_apply_4(v_G_3502_, v___x_3508_, v_a_3506_, lean_box(0), lean_box(0));
return v___x_3509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3510_, lean_object* v_next_3511_, lean_object* v_G_3512_, lean_object* v_____do__lift_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3510_, v_next_3511_, v_G_3512_, v_____do__lift_3513_);
lean_dec(v_next_3511_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(lean_object* v_snd_3515_, lean_object* v_newHyp_3516_, lean_object* v___x_3517_, lean_object* v_toPure_3518_, lean_object* v_____r_3519_){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3520_ = lean_array_push(v_snd_3515_, v_newHyp_3516_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3517_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___x_3523_ = lean_apply_2(v_toPure_3518_, lean_box(0), v___x_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v_toPure_3524_, lean_object* v___x_3525_, lean_object* v_____do__lift_3526_, lean_object* v_____do__lift_3527_){
_start:
{
uint8_t v_hasTrace_3528_; 
v_hasTrace_3528_ = lean_ctor_get_uint8(v_____do__lift_3527_, sizeof(void*)*1);
if (v_hasTrace_3528_ == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v___x_3525_);
v___x_3529_ = lean_box(v_hasTrace_3528_);
v___x_3530_ = lean_apply_2(v_toPure_3524_, lean_box(0), v___x_3529_);
return v___x_3530_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3531_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16));
v___x_3532_ = l_Lean_Name_append(v___x_3531_, v___x_3525_);
v___x_3533_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3526_, v_____do__lift_3527_, v___x_3532_);
lean_dec(v___x_3532_);
v___x_3534_ = lean_box(v___x_3533_);
v___x_3535_ = lean_apply_2(v_toPure_3524_, lean_box(0), v___x_3534_);
return v___x_3535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed(lean_object* v_toPure_3536_, lean_object* v___x_3537_, lean_object* v_____do__lift_3538_, lean_object* v_____do__lift_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(v_toPure_3536_, v___x_3537_, v_____do__lift_3538_, v_____do__lift_3539_);
lean_dec_ref(v_____do__lift_3539_);
lean_dec_ref(v_____do__lift_3538_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_toPure_3541_, lean_object* v___x_3542_, lean_object* v_toBind_3543_, lean_object* v_inst_3544_, lean_object* v_____do__lift_3545_){
_start:
{
lean_object* v___f_3546_; lean_object* v___x_3547_; 
v___f_3546_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed), 4, 3);
lean_closure_set(v___f_3546_, 0, v_toPure_3541_);
lean_closure_set(v___f_3546_, 1, v___x_3542_);
lean_closure_set(v___f_3546_, 2, v_____do__lift_3545_);
v___x_3547_ = lean_apply_4(v_toBind_3543_, lean_box(0), lean_box(0), v_inst_3544_, v___f_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v___f_3548_, lean_object* v_inst_3549_, lean_object* v___x_3550_, lean_object* v_type_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_, lean_object* v_inst_3554_, lean_object* v___x_3555_, lean_object* v_toBind_3556_, lean_object* v___f_3557_, uint8_t v_____do__lift_3558_){
_start:
{
if (v_____do__lift_3558_ == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
lean_dec(v___f_3557_);
lean_dec(v_toBind_3556_);
lean_dec(v___x_3555_);
lean_dec(v_inst_3554_);
lean_dec_ref(v_inst_3553_);
lean_dec_ref(v_inst_3552_);
lean_dec_ref(v_type_3551_);
lean_dec_ref(v___x_3550_);
lean_dec_ref(v_inst_3549_);
v___x_3559_ = lean_box(0);
v___x_3560_ = lean_apply_1(v___f_3548_, v___x_3559_);
return v___x_3560_;
}
else
{
lean_object* v_toMonadRef_3561_; lean_object* v_type_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
lean_dec(v___f_3548_);
v_toMonadRef_3561_ = lean_ctor_get(v_inst_3549_, 1);
lean_inc_ref(v_toMonadRef_3561_);
lean_dec_ref(v_inst_3549_);
v_type_3562_ = lean_ctor_get(v___x_3550_, 1);
lean_inc_ref(v_type_3562_);
lean_dec_ref(v___x_3550_);
v___x_3563_ = l_Lean_MessageData_ofExpr(v_type_3562_);
v___x_3564_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set(v___x_3565_, 1, v___x_3564_);
v___x_3566_ = l_Lean_MessageData_ofExpr(v_type_3551_);
v___x_3567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3565_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = l_Lean_addTrace___redArg(v_inst_3552_, v_inst_3553_, v_toMonadRef_3561_, v_inst_3554_, v___x_3555_, v___x_3567_);
v___x_3569_ = lean_apply_4(v_toBind_3556_, lean_box(0), lean_box(0), v___x_3568_, v___f_3557_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed(lean_object* v___f_3570_, lean_object* v_inst_3571_, lean_object* v___x_3572_, lean_object* v_type_3573_, lean_object* v_inst_3574_, lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v___x_3577_, lean_object* v_toBind_3578_, lean_object* v___f_3579_, lean_object* v_____do__lift_3580_){
_start:
{
uint8_t v_____do__lift_2106__boxed_3581_; lean_object* v_res_3582_; 
v_____do__lift_2106__boxed_3581_ = lean_unbox(v_____do__lift_3580_);
v_res_3582_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(v___f_3570_, v_inst_3571_, v___x_3572_, v_type_3573_, v_inst_3574_, v_inst_3575_, v_inst_3576_, v___x_3577_, v_toBind_3578_, v___f_3579_, v_____do__lift_2106__boxed_3581_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(uint8_t v___x_3583_, lean_object* v_snd_3584_, lean_object* v_toPure_3585_, lean_object* v_____r_3586_){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3587_ = lean_box(v___x_3583_);
v___x_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
v___x_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v_snd_3584_);
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
v___x_3591_ = lean_apply_2(v_toPure_3585_, lean_box(0), v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___x_3592_, lean_object* v_snd_3593_, lean_object* v_toPure_3594_, lean_object* v_____r_3595_){
_start:
{
uint8_t v___x_2144__boxed_3596_; lean_object* v_res_3597_; 
v___x_2144__boxed_3596_ = lean_unbox(v___x_3592_);
v_res_3597_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___x_2144__boxed_3596_, v_snd_3593_, v_toPure_3594_, v_____r_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v___x_3598_, lean_object* v_snd_3599_, lean_object* v___x_3600_, lean_object* v_toPure_3601_, lean_object* v_inst_3602_, lean_object* v_toBind_3603_, lean_object* v_inst_3604_, lean_object* v_inst_3605_, lean_object* v_inst_3606_, lean_object* v_inst_3607_, lean_object* v_inst_3608_, lean_object* v_newHyp_3609_){
_start:
{
lean_object* v_type_3610_; lean_object* v_value_3611_; uint8_t v___x_3612_; 
v_type_3610_ = lean_ctor_get(v_newHyp_3609_, 1);
v_value_3611_ = lean_ctor_get(v_newHyp_3609_, 2);
lean_inc_ref(v_type_3610_);
v___x_3612_ = l_Lean_Expr_isFalse(v_type_3610_);
if (v___x_3612_ == 0)
{
lean_object* v_type_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___f_3616_; lean_object* v___f_3617_; uint8_t v___x_3625_; 
v_type_3613_ = lean_ctor_get(v___x_3598_, 1);
lean_inc(v_toPure_3601_);
lean_inc(v___x_3600_);
lean_inc_ref(v_newHyp_3609_);
lean_inc(v_snd_3599_);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3614_, 0, v_snd_3599_);
lean_closure_set(v___f_3614_, 1, v_newHyp_3609_);
lean_closure_set(v___f_3614_, 2, v___x_3600_);
lean_closure_set(v___f_3614_, 3, v_toPure_3601_);
v___f_3615_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3615_, 0, v___f_3614_);
lean_inc(v_toBind_3603_);
v___f_3616_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3616_, 0, v_inst_3602_);
lean_closure_set(v___f_3616_, 1, v_toBind_3603_);
lean_closure_set(v___f_3616_, 2, v___f_3615_);
lean_inc_ref(v___f_3616_);
v___f_3617_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3617_, 0, v___f_3616_);
v___x_3625_ = lean_expr_eqv(v_type_3613_, v_type_3610_);
if (v___x_3625_ == 0)
{
lean_inc_ref(v_type_3610_);
lean_dec_ref(v_newHyp_3609_);
lean_dec(v___x_3600_);
lean_dec(v_snd_3599_);
goto v___jp_3618_;
}
else
{
if (v___x_3612_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_dec_ref(v___f_3617_);
lean_dec_ref(v___f_3616_);
lean_dec(v_inst_3608_);
lean_dec_ref(v_inst_3607_);
lean_dec_ref(v_inst_3606_);
lean_dec(v_inst_3605_);
lean_dec_ref(v_inst_3604_);
lean_dec(v_toBind_3603_);
lean_dec_ref(v___x_3598_);
v___x_3626_ = lean_box(0);
v___x_3627_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_3599_, v_newHyp_3609_, v___x_3600_, v_toPure_3601_, v___x_3626_);
return v___x_3627_;
}
else
{
lean_inc_ref(v_type_3610_);
lean_dec_ref(v_newHyp_3609_);
lean_dec(v___x_3600_);
lean_dec(v_snd_3599_);
goto v___jp_3618_;
}
}
v___jp_3618_:
{
lean_object* v_getInheritedTraceOptions_3619_; lean_object* v___x_3620_; lean_object* v___f_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_getInheritedTraceOptions_3619_ = lean_ctor_get(v_inst_3604_, 2);
lean_inc(v_getInheritedTraceOptions_3619_);
v___x_3620_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
lean_inc_n(v_toBind_3603_, 3);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3621_, 0, v_toPure_3601_);
lean_closure_set(v___f_3621_, 1, v___x_3620_);
lean_closure_set(v___f_3621_, 2, v_toBind_3603_);
lean_closure_set(v___f_3621_, 3, v_inst_3605_);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_3622_, 0, v___f_3616_);
lean_closure_set(v___f_3622_, 1, v_inst_3606_);
lean_closure_set(v___f_3622_, 2, v___x_3598_);
lean_closure_set(v___f_3622_, 3, v_type_3610_);
lean_closure_set(v___f_3622_, 4, v_inst_3607_);
lean_closure_set(v___f_3622_, 5, v_inst_3604_);
lean_closure_set(v___f_3622_, 6, v_inst_3608_);
lean_closure_set(v___f_3622_, 7, v___x_3620_);
lean_closure_set(v___f_3622_, 8, v_toBind_3603_);
lean_closure_set(v___f_3622_, 9, v___f_3617_);
v___x_3623_ = lean_apply_4(v_toBind_3603_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3619_, v___f_3621_);
v___x_3624_ = lean_apply_4(v_toBind_3603_, lean_box(0), lean_box(0), v___x_3623_, v___f_3622_);
return v___x_3624_;
}
}
else
{
lean_object* v___x_3628_; lean_object* v___f_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_inc_ref(v_value_3611_);
lean_dec_ref(v_newHyp_3609_);
lean_dec(v_inst_3608_);
lean_dec_ref(v_inst_3607_);
lean_dec_ref(v_inst_3606_);
lean_dec(v_inst_3605_);
lean_dec_ref(v_inst_3604_);
lean_dec(v___x_3600_);
lean_dec_ref(v___x_3598_);
v___x_3628_ = lean_box(v___x_3612_);
v___f_3629_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_3629_, 0, v___x_3628_);
lean_closure_set(v___f_3629_, 1, v_snd_3599_);
lean_closure_set(v___f_3629_, 2, v_toPure_3601_);
v___x_3630_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3630_, 0, v_value_3611_);
v___x_3631_ = lean_apply_2(v_inst_3602_, lean_box(0), v___x_3630_);
v___x_3632_ = lean_apply_4(v_toBind_3603_, lean_box(0), lean_box(0), v___x_3631_, v___f_3629_);
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3633_, lean_object* v_toPure_3634_, lean_object* v_hyps_3635_, lean_object* v___x_3636_, lean_object* v_inst_3637_, lean_object* v_toBind_3638_, lean_object* v_inst_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_inst_3642_, lean_object* v_inst_3643_, lean_object* v_f_3644_, lean_object* v___f_3645_, lean_object* v_next_3646_, lean_object* v_acc_3647_, lean_object* v_h_3648_, lean_object* v_G_3649_){
_start:
{
uint8_t v___x_3650_; 
v___x_3650_ = lean_nat_dec_lt(v_next_3646_, v___x_3633_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
lean_dec(v_G_3649_);
lean_dec(v_next_3646_);
lean_dec(v___f_3645_);
lean_dec(v_f_3644_);
lean_dec(v_inst_3643_);
lean_dec_ref(v_inst_3642_);
lean_dec_ref(v_inst_3641_);
lean_dec(v_inst_3640_);
lean_dec_ref(v_inst_3639_);
lean_dec(v_toBind_3638_);
lean_dec(v_inst_3637_);
lean_dec(v___x_3636_);
v___x_3651_ = lean_apply_2(v_toPure_3634_, lean_box(0), v_acc_3647_);
return v___x_3651_;
}
else
{
lean_object* v_snd_3652_; lean_object* v___f_3653_; lean_object* v___x_3654_; lean_object* v___f_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_snd_3652_ = lean_ctor_get(v_acc_3647_, 1);
lean_inc(v_snd_3652_);
lean_dec_ref(v_acc_3647_);
lean_inc(v_next_3646_);
lean_inc(v_toPure_3634_);
v___f_3653_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3653_, 0, v_toPure_3634_);
lean_closure_set(v___f_3653_, 1, v_next_3646_);
lean_closure_set(v___f_3653_, 2, v_G_3649_);
v___x_3654_ = lean_array_fget_borrowed(v_hyps_3635_, v_next_3646_);
lean_inc_n(v_toBind_3638_, 3);
lean_inc_n(v___x_3654_, 2);
v___f_3655_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10), 12, 11);
lean_closure_set(v___f_3655_, 0, v___x_3654_);
lean_closure_set(v___f_3655_, 1, v_snd_3652_);
lean_closure_set(v___f_3655_, 2, v___x_3636_);
lean_closure_set(v___f_3655_, 3, v_toPure_3634_);
lean_closure_set(v___f_3655_, 4, v_inst_3637_);
lean_closure_set(v___f_3655_, 5, v_toBind_3638_);
lean_closure_set(v___f_3655_, 6, v_inst_3639_);
lean_closure_set(v___f_3655_, 7, v_inst_3640_);
lean_closure_set(v___f_3655_, 8, v_inst_3641_);
lean_closure_set(v___f_3655_, 9, v_inst_3642_);
lean_closure_set(v___f_3655_, 10, v_inst_3643_);
v___x_3656_ = lean_apply_2(v_f_3644_, v_next_3646_, v___x_3654_);
v___x_3657_ = lean_apply_4(v_toBind_3638_, lean_box(0), lean_box(0), v___x_3656_, v___f_3655_);
v___x_3658_ = lean_apply_4(v_toBind_3638_, lean_box(0), lean_box(0), v___x_3657_, v___f_3645_);
v___x_3659_ = lean_apply_4(v_toBind_3638_, lean_box(0), lean_box(0), v___x_3658_, v___f_3653_);
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3660_ = _args[0];
lean_object* v_toPure_3661_ = _args[1];
lean_object* v_hyps_3662_ = _args[2];
lean_object* v___x_3663_ = _args[3];
lean_object* v_inst_3664_ = _args[4];
lean_object* v_toBind_3665_ = _args[5];
lean_object* v_inst_3666_ = _args[6];
lean_object* v_inst_3667_ = _args[7];
lean_object* v_inst_3668_ = _args[8];
lean_object* v_inst_3669_ = _args[9];
lean_object* v_inst_3670_ = _args[10];
lean_object* v_f_3671_ = _args[11];
lean_object* v___f_3672_ = _args[12];
lean_object* v_next_3673_ = _args[13];
lean_object* v_acc_3674_ = _args[14];
lean_object* v_h_3675_ = _args[15];
lean_object* v_G_3676_ = _args[16];
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3660_, v_toPure_3661_, v_hyps_3662_, v___x_3663_, v_inst_3664_, v_toBind_3665_, v_inst_3666_, v_inst_3667_, v_inst_3668_, v_inst_3669_, v_inst_3670_, v_f_3671_, v___f_3672_, v_next_3673_, v_acc_3674_, v_h_3675_, v_G_3676_);
lean_dec_ref(v_hyps_3662_);
lean_dec(v___x_3660_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3678_, lean_object* v_inst_3679_, lean_object* v_toBind_3680_, lean_object* v_inst_3681_, lean_object* v_inst_3682_, lean_object* v_inst_3683_, lean_object* v_inst_3684_, lean_object* v_inst_3685_, lean_object* v_f_3686_, lean_object* v___f_3687_, lean_object* v___f_3688_, lean_object* v_hyps_3689_){
_start:
{
lean_object* v___x_3690_; lean_object* v_newHyps_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___f_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3690_ = lean_array_get_size(v_hyps_3689_);
v_newHyps_3691_ = lean_mk_empty_array_with_capacity(v___x_3690_);
v___x_3692_ = lean_unsigned_to_nat(0u);
v___x_3693_ = lean_box(0);
lean_inc(v_toBind_3680_);
v___f_3694_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3694_, 0, v___x_3690_);
lean_closure_set(v___f_3694_, 1, v_toPure_3678_);
lean_closure_set(v___f_3694_, 2, v_hyps_3689_);
lean_closure_set(v___f_3694_, 3, v___x_3693_);
lean_closure_set(v___f_3694_, 4, v_inst_3679_);
lean_closure_set(v___f_3694_, 5, v_toBind_3680_);
lean_closure_set(v___f_3694_, 6, v_inst_3681_);
lean_closure_set(v___f_3694_, 7, v_inst_3682_);
lean_closure_set(v___f_3694_, 8, v_inst_3683_);
lean_closure_set(v___f_3694_, 9, v_inst_3684_);
lean_closure_set(v___f_3694_, 10, v_inst_3685_);
lean_closure_set(v___f_3694_, 11, v_f_3686_);
lean_closure_set(v___f_3694_, 12, v___f_3687_);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v_newHyps_3691_);
v___x_3696_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3694_, v___x_3692_, v___x_3695_, lean_box(0));
v___x_3697_ = lean_apply_4(v_toBind_3680_, lean_box(0), lean_box(0), v___x_3696_, v___f_3688_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3698_, lean_object* v_inst_3699_, lean_object* v_inst_3700_, lean_object* v_inst_3701_, lean_object* v_inst_3702_, lean_object* v_inst_3703_, lean_object* v_f_3704_){
_start:
{
lean_object* v_toApplicative_3705_; lean_object* v_toBind_3706_; lean_object* v_toPure_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___f_3710_; lean_object* v___f_3711_; lean_object* v___f_3712_; lean_object* v___f_3713_; lean_object* v___x_3714_; 
v_toApplicative_3705_ = lean_ctor_get(v_inst_3698_, 0);
v_toBind_3706_ = lean_ctor_get(v_inst_3698_, 1);
lean_inc_n(v_toBind_3706_, 3);
v_toPure_3707_ = lean_ctor_get(v_toApplicative_3705_, 1);
lean_inc_n(v_toPure_3707_, 4);
v___x_3708_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3699_, 2);
v___x_3709_ = lean_apply_2(v_inst_3699_, lean_box(0), v___x_3708_);
v___f_3710_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3710_, 0, v_toPure_3707_);
v___f_3711_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3711_, 0, v_toPure_3707_);
v___f_3712_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3712_, 0, v_inst_3699_);
lean_closure_set(v___f_3712_, 1, v_toBind_3706_);
lean_closure_set(v___f_3712_, 2, v___f_3711_);
lean_closure_set(v___f_3712_, 3, v_toPure_3707_);
v___f_3713_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3713_, 0, v_toPure_3707_);
lean_closure_set(v___f_3713_, 1, v_inst_3699_);
lean_closure_set(v___f_3713_, 2, v_toBind_3706_);
lean_closure_set(v___f_3713_, 3, v_inst_3701_);
lean_closure_set(v___f_3713_, 4, v_inst_3702_);
lean_closure_set(v___f_3713_, 5, v_inst_3700_);
lean_closure_set(v___f_3713_, 6, v_inst_3698_);
lean_closure_set(v___f_3713_, 7, v_inst_3703_);
lean_closure_set(v___f_3713_, 8, v_f_3704_);
lean_closure_set(v___f_3713_, 9, v___f_3710_);
lean_closure_set(v___f_3713_, 10, v___f_3712_);
v___x_3714_ = lean_apply_4(v_toBind_3706_, lean_box(0), lean_box(0), v___x_3709_, v___f_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3715_, lean_object* v_inst_3716_, lean_object* v_inst_3717_, lean_object* v_inst_3718_, lean_object* v_inst_3719_, lean_object* v_inst_3720_, lean_object* v_inst_3721_, lean_object* v_inst_3722_, lean_object* v_inst_3723_, lean_object* v_f_3724_){
_start:
{
lean_object* v_toApplicative_3725_; lean_object* v_toBind_3726_; lean_object* v_toPure_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___f_3730_; lean_object* v___f_3731_; lean_object* v___f_3732_; lean_object* v___f_3733_; lean_object* v___x_3734_; 
v_toApplicative_3725_ = lean_ctor_get(v_inst_3716_, 0);
v_toBind_3726_ = lean_ctor_get(v_inst_3716_, 1);
lean_inc_n(v_toBind_3726_, 3);
v_toPure_3727_ = lean_ctor_get(v_toApplicative_3725_, 1);
lean_inc_n(v_toPure_3727_, 4);
v___x_3728_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3717_, 2);
v___x_3729_ = lean_apply_2(v_inst_3717_, lean_box(0), v___x_3728_);
v___f_3730_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3730_, 0, v_toPure_3727_);
v___f_3731_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3731_, 0, v_toPure_3727_);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3732_, 0, v_inst_3717_);
lean_closure_set(v___f_3732_, 1, v_toBind_3726_);
lean_closure_set(v___f_3732_, 2, v___f_3731_);
lean_closure_set(v___f_3732_, 3, v_toPure_3727_);
v___f_3733_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3733_, 0, v_toPure_3727_);
lean_closure_set(v___f_3733_, 1, v_inst_3717_);
lean_closure_set(v___f_3733_, 2, v_toBind_3726_);
lean_closure_set(v___f_3733_, 3, v_inst_3720_);
lean_closure_set(v___f_3733_, 4, v_inst_3721_);
lean_closure_set(v___f_3733_, 5, v_inst_3718_);
lean_closure_set(v___f_3733_, 6, v_inst_3716_);
lean_closure_set(v___f_3733_, 7, v_inst_3722_);
lean_closure_set(v___f_3733_, 8, v_f_3724_);
lean_closure_set(v___f_3733_, 9, v___f_3730_);
lean_closure_set(v___f_3733_, 10, v___f_3732_);
v___x_3734_ = lean_apply_4(v_toBind_3726_, lean_box(0), lean_box(0), v___x_3729_, v___f_3733_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3746_, lean_object* v_snd_3747_, lean_object* v___x_3748_, lean_object* v_toPure_3749_, lean_object* v_inst_3750_, lean_object* v_toBind_3751_, lean_object* v_inst_3752_, lean_object* v_inst_3753_, lean_object* v_inst_3754_, lean_object* v_inst_3755_, lean_object* v_inst_3756_, lean_object* v_newHyp_3757_){
_start:
{
lean_object* v_type_3758_; lean_object* v_value_3759_; uint8_t v___x_3760_; 
v_type_3758_ = lean_ctor_get(v_newHyp_3757_, 1);
v_value_3759_ = lean_ctor_get(v_newHyp_3757_, 2);
lean_inc_ref(v_type_3758_);
v___x_3760_ = l_Lean_Expr_isFalse(v_type_3758_);
if (v___x_3760_ == 0)
{
lean_object* v_type_3761_; lean_object* v___f_3762_; lean_object* v___f_3763_; lean_object* v___f_3764_; lean_object* v___f_3765_; uint8_t v___x_3773_; 
v_type_3761_ = lean_ctor_get(v___x_3746_, 1);
lean_inc(v_toPure_3749_);
lean_inc(v___x_3748_);
lean_inc_ref(v_newHyp_3757_);
lean_inc(v_snd_3747_);
v___f_3762_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3762_, 0, v_snd_3747_);
lean_closure_set(v___f_3762_, 1, v_newHyp_3757_);
lean_closure_set(v___f_3762_, 2, v___x_3748_);
lean_closure_set(v___f_3762_, 3, v_toPure_3749_);
v___f_3763_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3763_, 0, v___f_3762_);
lean_inc(v_toBind_3751_);
v___f_3764_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3764_, 0, v_inst_3750_);
lean_closure_set(v___f_3764_, 1, v_toBind_3751_);
lean_closure_set(v___f_3764_, 2, v___f_3763_);
lean_inc_ref(v___f_3764_);
v___f_3765_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3765_, 0, v___f_3764_);
v___x_3773_ = lean_expr_eqv(v_type_3761_, v_type_3758_);
if (v___x_3773_ == 0)
{
lean_inc_ref(v_type_3758_);
lean_dec_ref(v_newHyp_3757_);
lean_dec(v___x_3748_);
lean_dec(v_snd_3747_);
goto v___jp_3766_;
}
else
{
if (v___x_3760_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
lean_dec_ref(v___f_3765_);
lean_dec_ref(v___f_3764_);
lean_dec(v_inst_3756_);
lean_dec(v_inst_3755_);
lean_dec_ref(v_inst_3754_);
lean_dec_ref(v_inst_3753_);
lean_dec_ref(v_inst_3752_);
lean_dec(v_toBind_3751_);
lean_dec_ref(v___x_3746_);
v___x_3774_ = lean_box(0);
v___x_3775_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_3747_, v_newHyp_3757_, v___x_3748_, v_toPure_3749_, v___x_3774_);
return v___x_3775_;
}
else
{
lean_inc_ref(v_type_3758_);
lean_dec_ref(v_newHyp_3757_);
lean_dec(v___x_3748_);
lean_dec(v_snd_3747_);
goto v___jp_3766_;
}
}
v___jp_3766_:
{
lean_object* v_getInheritedTraceOptions_3767_; lean_object* v___x_3768_; lean_object* v___f_3769_; lean_object* v___f_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_getInheritedTraceOptions_3767_ = lean_ctor_get(v_inst_3752_, 2);
lean_inc(v_getInheritedTraceOptions_3767_);
v___x_3768_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
lean_inc_n(v_toBind_3751_, 3);
v___f_3769_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_3769_, 0, v___f_3764_);
lean_closure_set(v___f_3769_, 1, v_inst_3753_);
lean_closure_set(v___f_3769_, 2, v___x_3746_);
lean_closure_set(v___f_3769_, 3, v_type_3758_);
lean_closure_set(v___f_3769_, 4, v_inst_3754_);
lean_closure_set(v___f_3769_, 5, v_inst_3752_);
lean_closure_set(v___f_3769_, 6, v_inst_3755_);
lean_closure_set(v___f_3769_, 7, v___x_3768_);
lean_closure_set(v___f_3769_, 8, v_toBind_3751_);
lean_closure_set(v___f_3769_, 9, v___f_3765_);
v___f_3770_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3770_, 0, v_toPure_3749_);
lean_closure_set(v___f_3770_, 1, v___x_3768_);
lean_closure_set(v___f_3770_, 2, v_toBind_3751_);
lean_closure_set(v___f_3770_, 3, v_inst_3756_);
v___x_3771_ = lean_apply_4(v_toBind_3751_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3767_, v___f_3770_);
v___x_3772_ = lean_apply_4(v_toBind_3751_, lean_box(0), lean_box(0), v___x_3771_, v___f_3769_);
return v___x_3772_;
}
}
else
{
lean_object* v___x_3776_; lean_object* v___f_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
lean_inc_ref(v_value_3759_);
lean_dec_ref(v_newHyp_3757_);
lean_dec(v_inst_3756_);
lean_dec(v_inst_3755_);
lean_dec_ref(v_inst_3754_);
lean_dec_ref(v_inst_3753_);
lean_dec_ref(v_inst_3752_);
lean_dec(v___x_3748_);
lean_dec_ref(v___x_3746_);
v___x_3776_ = lean_box(v___x_3760_);
v___f_3777_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_3777_, 0, v___x_3776_);
lean_closure_set(v___f_3777_, 1, v_snd_3747_);
lean_closure_set(v___f_3777_, 2, v_toPure_3749_);
v___x_3778_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3778_, 0, v_value_3759_);
v___x_3779_ = lean_apply_2(v_inst_3750_, lean_box(0), v___x_3778_);
v___x_3780_ = lean_apply_4(v_toBind_3751_, lean_box(0), lean_box(0), v___x_3779_, v___f_3777_);
return v___x_3780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3781_, lean_object* v_toPure_3782_, lean_object* v_hyps_3783_, lean_object* v___x_3784_, lean_object* v_inst_3785_, lean_object* v_toBind_3786_, lean_object* v_inst_3787_, lean_object* v_inst_3788_, lean_object* v_inst_3789_, lean_object* v_inst_3790_, lean_object* v_inst_3791_, lean_object* v_f_3792_, lean_object* v___f_3793_, lean_object* v_next_3794_, lean_object* v_acc_3795_, lean_object* v_h_3796_, lean_object* v_G_3797_){
_start:
{
uint8_t v___x_3798_; 
v___x_3798_ = lean_nat_dec_lt(v_next_3794_, v___x_3781_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; 
lean_dec(v_G_3797_);
lean_dec(v_next_3794_);
lean_dec(v___f_3793_);
lean_dec(v_f_3792_);
lean_dec(v_inst_3791_);
lean_dec(v_inst_3790_);
lean_dec_ref(v_inst_3789_);
lean_dec_ref(v_inst_3788_);
lean_dec_ref(v_inst_3787_);
lean_dec(v_toBind_3786_);
lean_dec(v_inst_3785_);
lean_dec(v___x_3784_);
v___x_3799_ = lean_apply_2(v_toPure_3782_, lean_box(0), v_acc_3795_);
return v___x_3799_;
}
else
{
lean_object* v_snd_3800_; lean_object* v___f_3801_; lean_object* v___x_3802_; lean_object* v___f_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v_snd_3800_ = lean_ctor_get(v_acc_3795_, 1);
lean_inc(v_snd_3800_);
lean_dec_ref(v_acc_3795_);
lean_inc(v_next_3794_);
lean_inc(v_toPure_3782_);
v___f_3801_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3801_, 0, v_toPure_3782_);
lean_closure_set(v___f_3801_, 1, v_next_3794_);
lean_closure_set(v___f_3801_, 2, v_G_3797_);
v___x_3802_ = lean_array_fget_borrowed(v_hyps_3783_, v_next_3794_);
lean_dec(v_next_3794_);
lean_inc_n(v_toBind_3786_, 3);
lean_inc_n(v___x_3802_, 2);
v___f_3803_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3803_, 0, v___x_3802_);
lean_closure_set(v___f_3803_, 1, v_snd_3800_);
lean_closure_set(v___f_3803_, 2, v___x_3784_);
lean_closure_set(v___f_3803_, 3, v_toPure_3782_);
lean_closure_set(v___f_3803_, 4, v_inst_3785_);
lean_closure_set(v___f_3803_, 5, v_toBind_3786_);
lean_closure_set(v___f_3803_, 6, v_inst_3787_);
lean_closure_set(v___f_3803_, 7, v_inst_3788_);
lean_closure_set(v___f_3803_, 8, v_inst_3789_);
lean_closure_set(v___f_3803_, 9, v_inst_3790_);
lean_closure_set(v___f_3803_, 10, v_inst_3791_);
v___x_3804_ = lean_apply_1(v_f_3792_, v___x_3802_);
v___x_3805_ = lean_apply_4(v_toBind_3786_, lean_box(0), lean_box(0), v___x_3804_, v___f_3803_);
v___x_3806_ = lean_apply_4(v_toBind_3786_, lean_box(0), lean_box(0), v___x_3805_, v___f_3793_);
v___x_3807_ = lean_apply_4(v_toBind_3786_, lean_box(0), lean_box(0), v___x_3806_, v___f_3801_);
return v___x_3807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3808_ = _args[0];
lean_object* v_toPure_3809_ = _args[1];
lean_object* v_hyps_3810_ = _args[2];
lean_object* v___x_3811_ = _args[3];
lean_object* v_inst_3812_ = _args[4];
lean_object* v_toBind_3813_ = _args[5];
lean_object* v_inst_3814_ = _args[6];
lean_object* v_inst_3815_ = _args[7];
lean_object* v_inst_3816_ = _args[8];
lean_object* v_inst_3817_ = _args[9];
lean_object* v_inst_3818_ = _args[10];
lean_object* v_f_3819_ = _args[11];
lean_object* v___f_3820_ = _args[12];
lean_object* v_next_3821_ = _args[13];
lean_object* v_acc_3822_ = _args[14];
lean_object* v_h_3823_ = _args[15];
lean_object* v_G_3824_ = _args[16];
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3808_, v_toPure_3809_, v_hyps_3810_, v___x_3811_, v_inst_3812_, v_toBind_3813_, v_inst_3814_, v_inst_3815_, v_inst_3816_, v_inst_3817_, v_inst_3818_, v_f_3819_, v___f_3820_, v_next_3821_, v_acc_3822_, v_h_3823_, v_G_3824_);
lean_dec_ref(v_hyps_3810_);
lean_dec(v___x_3808_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3826_, lean_object* v_inst_3827_, lean_object* v_toBind_3828_, lean_object* v_inst_3829_, lean_object* v_inst_3830_, lean_object* v_inst_3831_, lean_object* v_inst_3832_, lean_object* v_inst_3833_, lean_object* v_f_3834_, lean_object* v___f_3835_, lean_object* v___f_3836_, lean_object* v_hyps_3837_){
_start:
{
lean_object* v___x_3838_; lean_object* v_newHyps_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___f_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3838_ = lean_array_get_size(v_hyps_3837_);
v_newHyps_3839_ = lean_mk_empty_array_with_capacity(v___x_3838_);
v___x_3840_ = lean_unsigned_to_nat(0u);
v___x_3841_ = lean_box(0);
lean_inc(v_toBind_3828_);
v___f_3842_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3842_, 0, v___x_3838_);
lean_closure_set(v___f_3842_, 1, v_toPure_3826_);
lean_closure_set(v___f_3842_, 2, v_hyps_3837_);
lean_closure_set(v___f_3842_, 3, v___x_3841_);
lean_closure_set(v___f_3842_, 4, v_inst_3827_);
lean_closure_set(v___f_3842_, 5, v_toBind_3828_);
lean_closure_set(v___f_3842_, 6, v_inst_3829_);
lean_closure_set(v___f_3842_, 7, v_inst_3830_);
lean_closure_set(v___f_3842_, 8, v_inst_3831_);
lean_closure_set(v___f_3842_, 9, v_inst_3832_);
lean_closure_set(v___f_3842_, 10, v_inst_3833_);
lean_closure_set(v___f_3842_, 11, v_f_3834_);
lean_closure_set(v___f_3842_, 12, v___f_3835_);
v___x_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3841_);
lean_ctor_set(v___x_3843_, 1, v_newHyps_3839_);
v___x_3844_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3842_, v___x_3840_, v___x_3843_, lean_box(0));
v___x_3845_ = lean_apply_4(v_toBind_3828_, lean_box(0), lean_box(0), v___x_3844_, v___f_3836_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3846_, lean_object* v_inst_3847_, lean_object* v_inst_3848_, lean_object* v_inst_3849_, lean_object* v_inst_3850_, lean_object* v_inst_3851_, lean_object* v_f_3852_){
_start:
{
lean_object* v_toApplicative_3853_; lean_object* v_toBind_3854_; lean_object* v_toPure_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___f_3858_; lean_object* v___f_3859_; lean_object* v___f_3860_; lean_object* v___f_3861_; lean_object* v___x_3862_; 
v_toApplicative_3853_ = lean_ctor_get(v_inst_3846_, 0);
v_toBind_3854_ = lean_ctor_get(v_inst_3846_, 1);
lean_inc_n(v_toBind_3854_, 3);
v_toPure_3855_ = lean_ctor_get(v_toApplicative_3853_, 1);
lean_inc_n(v_toPure_3855_, 4);
v___x_3856_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3847_, 2);
v___x_3857_ = lean_apply_2(v_inst_3847_, lean_box(0), v___x_3856_);
v___f_3858_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3858_, 0, v_toPure_3855_);
v___f_3859_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3859_, 0, v_inst_3847_);
lean_closure_set(v___f_3859_, 1, v_toBind_3854_);
lean_closure_set(v___f_3859_, 2, v___f_3858_);
lean_closure_set(v___f_3859_, 3, v_toPure_3855_);
v___f_3860_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3860_, 0, v_toPure_3855_);
v___f_3861_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3861_, 0, v_toPure_3855_);
lean_closure_set(v___f_3861_, 1, v_inst_3847_);
lean_closure_set(v___f_3861_, 2, v_toBind_3854_);
lean_closure_set(v___f_3861_, 3, v_inst_3849_);
lean_closure_set(v___f_3861_, 4, v_inst_3848_);
lean_closure_set(v___f_3861_, 5, v_inst_3846_);
lean_closure_set(v___f_3861_, 6, v_inst_3851_);
lean_closure_set(v___f_3861_, 7, v_inst_3850_);
lean_closure_set(v___f_3861_, 8, v_f_3852_);
lean_closure_set(v___f_3861_, 9, v___f_3860_);
lean_closure_set(v___f_3861_, 10, v___f_3859_);
v___x_3862_ = lean_apply_4(v_toBind_3854_, lean_box(0), lean_box(0), v___x_3857_, v___f_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3863_, lean_object* v_inst_3864_, lean_object* v_inst_3865_, lean_object* v_inst_3866_, lean_object* v_inst_3867_, lean_object* v_inst_3868_, lean_object* v_inst_3869_, lean_object* v_inst_3870_, lean_object* v_inst_3871_, lean_object* v_f_3872_){
_start:
{
lean_object* v_toApplicative_3873_; lean_object* v_toBind_3874_; lean_object* v_toPure_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___f_3878_; lean_object* v___f_3879_; lean_object* v___f_3880_; lean_object* v___f_3881_; lean_object* v___x_3882_; 
v_toApplicative_3873_ = lean_ctor_get(v_inst_3864_, 0);
v_toBind_3874_ = lean_ctor_get(v_inst_3864_, 1);
lean_inc_n(v_toBind_3874_, 3);
v_toPure_3875_ = lean_ctor_get(v_toApplicative_3873_, 1);
lean_inc_n(v_toPure_3875_, 4);
v___x_3876_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3865_, 2);
v___x_3877_ = lean_apply_2(v_inst_3865_, lean_box(0), v___x_3876_);
v___f_3878_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3878_, 0, v_toPure_3875_);
v___f_3879_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3879_, 0, v_inst_3865_);
lean_closure_set(v___f_3879_, 1, v_toBind_3874_);
lean_closure_set(v___f_3879_, 2, v___f_3878_);
lean_closure_set(v___f_3879_, 3, v_toPure_3875_);
v___f_3880_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3880_, 0, v_toPure_3875_);
v___f_3881_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3881_, 0, v_toPure_3875_);
lean_closure_set(v___f_3881_, 1, v_inst_3865_);
lean_closure_set(v___f_3881_, 2, v_toBind_3874_);
lean_closure_set(v___f_3881_, 3, v_inst_3868_);
lean_closure_set(v___f_3881_, 4, v_inst_3866_);
lean_closure_set(v___f_3881_, 5, v_inst_3864_);
lean_closure_set(v___f_3881_, 6, v_inst_3870_);
lean_closure_set(v___f_3881_, 7, v_inst_3869_);
lean_closure_set(v___f_3881_, 8, v_f_3872_);
lean_closure_set(v___f_3881_, 9, v___f_3880_);
lean_closure_set(v___f_3881_, 10, v___f_3879_);
v___x_3882_ = lean_apply_4(v_toBind_3874_, lean_box(0), lean_box(0), v___x_3877_, v___f_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3883_, lean_object* v_inst_3884_, lean_object* v_inst_3885_, lean_object* v_inst_3886_, lean_object* v_inst_3887_, lean_object* v_inst_3888_, lean_object* v_inst_3889_, lean_object* v_inst_3890_, lean_object* v_inst_3891_, lean_object* v_f_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3883_, v_inst_3884_, v_inst_3885_, v_inst_3886_, v_inst_3887_, v_inst_3888_, v_inst_3889_, v_inst_3890_, v_inst_3891_, v_f_3892_);
lean_dec_ref(v_inst_3891_);
lean_dec_ref(v_inst_3887_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3894_, lean_object* v_x_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_apply_1(v_f_3894_, v___y_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3898_, lean_object* v_inst_3899_, lean_object* v___f_3900_, lean_object* v_hyps_3901_){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; 
v___x_3902_ = lean_unsigned_to_nat(0u);
v___x_3903_ = lean_array_get_size(v_hyps_3901_);
v___x_3904_ = lean_box(0);
v___x_3905_ = lean_nat_dec_lt(v___x_3902_, v___x_3903_);
if (v___x_3905_ == 0)
{
lean_object* v_toPure_3906_; lean_object* v___x_3907_; 
lean_dec_ref(v_hyps_3901_);
lean_dec(v___f_3900_);
lean_dec_ref(v_inst_3899_);
v_toPure_3906_ = lean_ctor_get(v_toApplicative_3898_, 1);
lean_inc(v_toPure_3906_);
lean_dec_ref(v_toApplicative_3898_);
v___x_3907_ = lean_apply_2(v_toPure_3906_, lean_box(0), v___x_3904_);
return v___x_3907_;
}
else
{
uint8_t v___x_3908_; 
v___x_3908_ = lean_nat_dec_le(v___x_3903_, v___x_3903_);
if (v___x_3908_ == 0)
{
if (v___x_3905_ == 0)
{
lean_object* v_toPure_3909_; lean_object* v___x_3910_; 
lean_dec_ref(v_hyps_3901_);
lean_dec(v___f_3900_);
lean_dec_ref(v_inst_3899_);
v_toPure_3909_ = lean_ctor_get(v_toApplicative_3898_, 1);
lean_inc(v_toPure_3909_);
lean_dec_ref(v_toApplicative_3898_);
v___x_3910_ = lean_apply_2(v_toPure_3909_, lean_box(0), v___x_3904_);
return v___x_3910_;
}
else
{
size_t v___x_3911_; size_t v___x_3912_; lean_object* v___x_3913_; 
lean_dec_ref(v_toApplicative_3898_);
v___x_3911_ = ((size_t)0ULL);
v___x_3912_ = lean_usize_of_nat(v___x_3903_);
v___x_3913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3899_, v___f_3900_, v_hyps_3901_, v___x_3911_, v___x_3912_, v___x_3904_);
return v___x_3913_;
}
}
else
{
size_t v___x_3914_; size_t v___x_3915_; lean_object* v___x_3916_; 
lean_dec_ref(v_toApplicative_3898_);
v___x_3914_ = ((size_t)0ULL);
v___x_3915_ = lean_usize_of_nat(v___x_3903_);
v___x_3916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3899_, v___f_3900_, v_hyps_3901_, v___x_3914_, v___x_3915_, v___x_3904_);
return v___x_3916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3917_, lean_object* v_inst_3918_, lean_object* v_f_3919_){
_start:
{
lean_object* v_toApplicative_3920_; lean_object* v_toBind_3921_; lean_object* v___f_3922_; lean_object* v___f_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_toApplicative_3920_ = lean_ctor_get(v_inst_3917_, 0);
lean_inc_ref(v_toApplicative_3920_);
v_toBind_3921_ = lean_ctor_get(v_inst_3917_, 1);
lean_inc(v_toBind_3921_);
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3922_, 0, v_f_3919_);
v___f_3923_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3923_, 0, v_toApplicative_3920_);
lean_closure_set(v___f_3923_, 1, v_inst_3917_);
lean_closure_set(v___f_3923_, 2, v___f_3922_);
v___x_3924_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3925_ = lean_apply_2(v_inst_3918_, lean_box(0), v___x_3924_);
v___x_3926_ = lean_apply_4(v_toBind_3921_, lean_box(0), lean_box(0), v___x_3925_, v___f_3923_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3927_, lean_object* v_inst_3928_, lean_object* v_inst_3929_, lean_object* v_inst_3930_, lean_object* v_f_3931_){
_start:
{
lean_object* v_toApplicative_3932_; lean_object* v_toBind_3933_; lean_object* v___f_3934_; lean_object* v___f_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v_toApplicative_3932_ = lean_ctor_get(v_inst_3928_, 0);
lean_inc_ref(v_toApplicative_3932_);
v_toBind_3933_ = lean_ctor_get(v_inst_3928_, 1);
lean_inc(v_toBind_3933_);
v___f_3934_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3934_, 0, v_f_3931_);
v___f_3935_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3935_, 0, v_toApplicative_3932_);
lean_closure_set(v___f_3935_, 1, v_inst_3928_);
lean_closure_set(v___f_3935_, 2, v___f_3934_);
v___x_3936_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3937_ = lean_apply_2(v_inst_3929_, lean_box(0), v___x_3936_);
v___x_3938_ = lean_apply_4(v_toBind_3933_, lean_box(0), lean_box(0), v___x_3937_, v___f_3935_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3939_, lean_object* v_inst_3940_, lean_object* v_inst_3941_, lean_object* v_inst_3942_, lean_object* v_f_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3939_, v_inst_3940_, v_inst_3941_, v_inst_3942_, v_f_3943_);
lean_dec_ref(v_inst_3942_);
return v_res_3944_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3945_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3946_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_3948_, lean_object* v_methods_3949_, lean_object* v_config_3950_, lean_object* v_hyp_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v___x_3960_; lean_object* v_caches_3961_; lean_object* v___x_3962_; lean_object* v_typeAnalysis_3963_; lean_object* v_target_3964_; lean_object* v_hypotheses_3965_; uint8_t v_didChange_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_4012_; 
v___x_3960_ = lean_st_ref_get(v_a_3952_);
v_caches_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc_ref(v_caches_3961_);
lean_dec(v___x_3960_);
v___x_3962_ = lean_st_ref_take(v_a_3952_);
v_typeAnalysis_3963_ = lean_ctor_get(v___x_3962_, 1);
v_target_3964_ = lean_ctor_get(v___x_3962_, 2);
v_hypotheses_3965_ = lean_ctor_get(v___x_3962_, 3);
v_didChange_3966_ = lean_ctor_get_uint8(v___x_3962_, sizeof(void*)*4);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; 
v_unused_4013_ = lean_ctor_get(v___x_3962_, 0);
lean_dec(v_unused_4013_);
v___x_3968_ = v___x_3962_;
v_isShared_3969_ = v_isSharedCheck_4012_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_hypotheses_3965_);
lean_inc(v_target_3964_);
lean_inc(v_typeAnalysis_3963_);
lean_dec(v___x_3962_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_4012_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_3971_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_3948_, v_caches_3961_);
v___x_3972_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_3973_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3970_);
lean_ctor_set(v___x_3973_, 1, v___x_3971_);
lean_ctor_set(v___x_3973_, 2, v___x_3972_);
lean_ctor_set(v___x_3973_, 3, v___x_3972_);
v___x_3974_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3948_, v___x_3972_, v_caches_3961_);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3974_);
v___x_3976_ = v___x_3968_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_typeAnalysis_3963_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_target_3964_);
lean_ctor_set(v_reuseFailAlloc_4011_, 3, v_hypotheses_3965_);
lean_ctor_set_uint8(v_reuseFailAlloc_4011_, sizeof(void*)*4, v_didChange_3966_);
v___x_3976_ = v_reuseFailAlloc_4011_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; lean_object* v_type_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3977_ = lean_st_ref_put(v_a_3952_, v___x_3976_);
v_type_3978_ = lean_ctor_get(v_hyp_3951_, 1);
lean_inc_ref(v_type_3978_);
v___x_3979_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3979_, 0, v_type_3978_);
v___x_3980_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3979_, v_methods_3949_, v_config_3950_, v___x_3973_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v_fst_3982_; lean_object* v_snd_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v_caches_3986_; lean_object* v_persistentCache_3987_; lean_object* v_typeAnalysis_3988_; lean_object* v_target_3989_; lean_object* v_hypotheses_3990_; uint8_t v_didChange_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4001_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3980_, 1);
v_fst_3982_ = lean_ctor_get(v_a_3981_, 0);
lean_inc(v_fst_3982_);
v_snd_3983_ = lean_ctor_get(v_a_3981_, 1);
lean_inc(v_snd_3983_);
lean_dec(v_a_3981_);
v___x_3984_ = lean_st_ref_get(v_a_3952_);
v___x_3985_ = lean_st_ref_take(v_a_3952_);
v_caches_3986_ = lean_ctor_get(v___x_3984_, 0);
lean_inc_ref(v_caches_3986_);
lean_dec(v___x_3984_);
v_persistentCache_3987_ = lean_ctor_get(v_snd_3983_, 1);
lean_inc_ref(v_persistentCache_3987_);
lean_dec(v_snd_3983_);
v_typeAnalysis_3988_ = lean_ctor_get(v___x_3985_, 1);
v_target_3989_ = lean_ctor_get(v___x_3985_, 2);
v_hypotheses_3990_ = lean_ctor_get(v___x_3985_, 3);
v_didChange_3991_ = lean_ctor_get_uint8(v___x_3985_, sizeof(void*)*4);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4001_ == 0)
{
lean_object* v_unused_4002_; 
v_unused_4002_ = lean_ctor_get(v___x_3985_, 0);
lean_dec(v_unused_4002_);
v___x_3993_ = v___x_3985_;
v_isShared_3994_ = v_isSharedCheck_4001_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_hypotheses_3990_);
lean_inc(v_target_3989_);
lean_inc(v_typeAnalysis_3988_);
lean_dec(v___x_3985_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4001_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3995_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3948_, v_persistentCache_3987_, v_caches_3986_);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_3995_);
v___x_3997_ = v___x_3993_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_typeAnalysis_3988_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_target_3989_);
lean_ctor_set(v_reuseFailAlloc_4000_, 3, v_hypotheses_3990_);
lean_ctor_set_uint8(v_reuseFailAlloc_4000_, sizeof(void*)*4, v_didChange_3991_);
v___x_3997_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = lean_st_ref_put(v_a_3952_, v___x_3997_);
v___x_3999_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_3951_, v_fst_3982_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
return v___x_3999_;
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v_hyp_3951_);
v_a_4003_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3980_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3980_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_4014_, lean_object* v_methods_4015_, lean_object* v_config_4016_, lean_object* v_hyp_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
uint8_t v_cacheId_boxed_4026_; lean_object* v_res_4027_; 
v_cacheId_boxed_4026_ = lean_unbox(v_cacheId_4014_);
v_res_4027_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_4026_, v_methods_4015_, v_config_4016_, v_hyp_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
lean_dec(v_a_4024_);
lean_dec_ref(v_a_4023_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_4028_, lean_object* v_methods_4029_, lean_object* v_config_4030_, lean_object* v_hyp_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4028_, v_methods_4029_, v_config_4030_, v_hyp_4031_, v_a_4033_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4045_, lean_object* v_methods_4046_, lean_object* v_config_4047_, lean_object* v_hyp_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
uint8_t v_cacheId_boxed_4061_; lean_object* v_res_4062_; 
v_cacheId_boxed_4061_ = lean_unbox(v_cacheId_4045_);
v_res_4062_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4061_, v_methods_4046_, v_config_4047_, v_hyp_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4063_, lean_object* v_methods_4064_, lean_object* v_config_4065_, lean_object* v_hyp_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v___x_4075_; lean_object* v_caches_4076_; lean_object* v___x_4077_; lean_object* v_typeAnalysis_4078_; lean_object* v_target_4079_; lean_object* v_hypotheses_4080_; uint8_t v_didChange_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4127_; 
v___x_4075_ = lean_st_ref_get(v_a_4067_);
v_caches_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc_ref(v_caches_4076_);
lean_dec(v___x_4075_);
v___x_4077_ = lean_st_ref_take(v_a_4067_);
v_typeAnalysis_4078_ = lean_ctor_get(v___x_4077_, 1);
v_target_4079_ = lean_ctor_get(v___x_4077_, 2);
v_hypotheses_4080_ = lean_ctor_get(v___x_4077_, 3);
v_didChange_4081_ = lean_ctor_get_uint8(v___x_4077_, sizeof(void*)*4);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; 
v_unused_4128_ = lean_ctor_get(v___x_4077_, 0);
lean_dec(v_unused_4128_);
v___x_4083_ = v___x_4077_;
v_isShared_4084_ = v_isSharedCheck_4127_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_hypotheses_4080_);
lean_inc(v_target_4079_);
lean_inc(v_typeAnalysis_4078_);
lean_dec(v___x_4077_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4127_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4089_; 
v___x_4085_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4063_, v_caches_4076_);
v___x_4086_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4087_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4063_, v___x_4086_, v_caches_4076_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 0, v___x_4087_);
v___x_4089_ = v___x_4083_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4087_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_typeAnalysis_4078_);
lean_ctor_set(v_reuseFailAlloc_4126_, 2, v_target_4079_);
lean_ctor_set(v_reuseFailAlloc_4126_, 3, v_hypotheses_4080_);
lean_ctor_set_uint8(v_reuseFailAlloc_4126_, sizeof(void*)*4, v_didChange_4081_);
v___x_4089_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
lean_object* v___x_4090_; lean_object* v_type_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4090_ = lean_st_ref_put(v_a_4067_, v___x_4089_);
v_type_4091_ = lean_ctor_get(v_hyp_4066_, 1);
v___x_4092_ = lean_unsigned_to_nat(0u);
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
lean_ctor_set(v___x_4093_, 1, v___x_4085_);
lean_inc_ref(v_type_4091_);
v___x_4094_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4094_, 0, v_type_4091_);
v___x_4095_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4094_, v_methods_4064_, v_config_4065_, v___x_4093_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v_fst_4097_; lean_object* v_snd_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v_caches_4101_; lean_object* v_cache_4102_; lean_object* v_typeAnalysis_4103_; lean_object* v_target_4104_; lean_object* v_hypotheses_4105_; uint8_t v_didChange_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4116_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4095_, 1);
v_fst_4097_ = lean_ctor_get(v_a_4096_, 0);
lean_inc(v_fst_4097_);
v_snd_4098_ = lean_ctor_get(v_a_4096_, 1);
lean_inc(v_snd_4098_);
lean_dec(v_a_4096_);
v___x_4099_ = lean_st_ref_get(v_a_4067_);
v___x_4100_ = lean_st_ref_take(v_a_4067_);
v_caches_4101_ = lean_ctor_get(v___x_4099_, 0);
lean_inc_ref(v_caches_4101_);
lean_dec(v___x_4099_);
v_cache_4102_ = lean_ctor_get(v_snd_4098_, 1);
lean_inc_ref(v_cache_4102_);
lean_dec(v_snd_4098_);
v_typeAnalysis_4103_ = lean_ctor_get(v___x_4100_, 1);
v_target_4104_ = lean_ctor_get(v___x_4100_, 2);
v_hypotheses_4105_ = lean_ctor_get(v___x_4100_, 3);
v_didChange_4106_ = lean_ctor_get_uint8(v___x_4100_, sizeof(void*)*4);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; 
v_unused_4117_ = lean_ctor_get(v___x_4100_, 0);
lean_dec(v_unused_4117_);
v___x_4108_ = v___x_4100_;
v_isShared_4109_ = v_isSharedCheck_4116_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_hypotheses_4105_);
lean_inc(v_target_4104_);
lean_inc(v_typeAnalysis_4103_);
lean_dec(v___x_4100_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4116_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4110_; lean_object* v___x_4112_; 
v___x_4110_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4063_, v_cache_4102_, v_caches_4101_);
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 0, v___x_4110_);
v___x_4112_ = v___x_4108_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4110_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_typeAnalysis_4103_);
lean_ctor_set(v_reuseFailAlloc_4115_, 2, v_target_4104_);
lean_ctor_set(v_reuseFailAlloc_4115_, 3, v_hypotheses_4105_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, sizeof(void*)*4, v_didChange_4106_);
v___x_4112_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = lean_st_ref_put(v_a_4067_, v___x_4112_);
v___x_4114_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4066_, v_fst_4097_);
lean_dec(v_fst_4097_);
return v___x_4114_;
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec_ref(v_hyp_4066_);
v_a_4118_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4095_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4095_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4129_, lean_object* v_methods_4130_, lean_object* v_config_4131_, lean_object* v_hyp_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
uint8_t v_cacheId_boxed_4141_; lean_object* v_res_4142_; 
v_cacheId_boxed_4141_ = lean_unbox(v_cacheId_4129_);
v_res_4142_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4141_, v_methods_4130_, v_config_4131_, v_hyp_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec(v_a_4133_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4143_, lean_object* v_methods_4144_, lean_object* v_config_4145_, lean_object* v_hyp_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4143_, v_methods_4144_, v_config_4145_, v_hyp_4146_, v_a_4148_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4160_, lean_object* v_methods_4161_, lean_object* v_config_4162_, lean_object* v_hyp_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
uint8_t v_cacheId_boxed_4176_; lean_object* v_res_4177_; 
v_cacheId_boxed_4176_ = lean_unbox(v_cacheId_4160_);
v_res_4177_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4176_, v_methods_4161_, v_config_4162_, v_hyp_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4178_, lean_object* v_a_4179_, lean_object* v___x_4180_, lean_object* v_____r_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4194_ = lean_array_push(v_snd_4178_, v_a_4179_);
v___x_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4180_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4198_, lean_object* v_a_4199_, lean_object* v___x_4200_, lean_object* v_____r_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4198_, v_a_4199_, v___x_4200_, v_____r_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4215_, lean_object* v___f_4216_, lean_object* v_____r_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v___x_4230_; lean_object* v_caches_4231_; lean_object* v_typeAnalysis_4232_; lean_object* v_target_4233_; lean_object* v_hypotheses_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4244_; 
v___x_4230_ = lean_st_ref_take(v___y_4219_);
v_caches_4231_ = lean_ctor_get(v___x_4230_, 0);
v_typeAnalysis_4232_ = lean_ctor_get(v___x_4230_, 1);
v_target_4233_ = lean_ctor_get(v___x_4230_, 2);
v_hypotheses_4234_ = lean_ctor_get(v___x_4230_, 3);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4236_ = v___x_4230_;
v_isShared_4237_ = v_isSharedCheck_4244_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_hypotheses_4234_);
lean_inc(v_target_4233_);
lean_inc(v_typeAnalysis_4232_);
lean_inc(v_caches_4231_);
lean_dec(v___x_4230_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4244_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_caches_4231_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_typeAnalysis_4232_);
lean_ctor_set(v_reuseFailAlloc_4243_, 2, v_target_4233_);
lean_ctor_set(v_reuseFailAlloc_4243_, 3, v_hypotheses_4234_);
v___x_4239_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_ctor_set_uint8(v___x_4239_, sizeof(void*)*4, v___x_4215_);
v___x_4240_ = lean_st_ref_put(v___y_4219_, v___x_4239_);
v___x_4241_ = lean_box(0);
lean_inc(v___y_4228_);
lean_inc_ref(v___y_4227_);
lean_inc(v___y_4226_);
lean_inc_ref(v___y_4225_);
lean_inc(v___y_4224_);
lean_inc_ref(v___y_4223_);
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
lean_inc(v___y_4220_);
lean_inc(v___y_4219_);
lean_inc_ref(v___y_4218_);
v___x_4242_ = lean_apply_13(v___f_4216_, v___x_4241_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, lean_box(0));
return v___x_4242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4245_, lean_object* v___f_4246_, lean_object* v_____r_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
uint8_t v___x_22146__boxed_4260_; lean_object* v_res_4261_; 
v___x_22146__boxed_4260_ = lean_unbox(v___x_4245_);
v_res_4261_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22146__boxed_4260_, v___f_4246_, v_____r_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4262_, lean_object* v_hypotheses_4263_, uint8_t v_cacheId_4264_, lean_object* v_methods_4265_, lean_object* v_config_4266_, lean_object* v___x_4267_, lean_object* v___x_4268_, lean_object* v___x_4269_, lean_object* v_toMonadRef_4270_, lean_object* v___f_4271_, lean_object* v_next_4272_, lean_object* v_acc_4273_, lean_object* v_h_4274_, lean_object* v_G_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___y_4289_; uint8_t v___x_4311_; 
v___x_4311_ = lean_nat_dec_lt(v_next_4272_, v___x_4262_);
if (v___x_4311_ == 0)
{
lean_object* v___x_4312_; 
lean_dec_ref(v_G_4275_);
lean_dec(v___f_4271_);
lean_dec_ref(v_toMonadRef_4270_);
lean_dec_ref(v___x_4269_);
lean_dec_ref(v___x_4268_);
lean_dec(v___x_4267_);
lean_dec_ref(v_config_4266_);
lean_dec_ref(v_methods_4265_);
v___x_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4312_, 0, v_acc_4273_);
return v___x_4312_;
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = lean_array_fget_borrowed(v_hypotheses_4263_, v_next_4272_);
lean_inc(v___x_4313_);
v___x_4314_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4264_, v_methods_4265_, v_config_4266_, v___x_4313_, v___y_4277_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v_snd_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4378_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v_snd_4316_ = lean_ctor_get(v_acc_4273_, 1);
v_isSharedCheck_4378_ = !lean_is_exclusive(v_acc_4273_);
if (v_isSharedCheck_4378_ == 0)
{
lean_object* v_unused_4379_; 
v_unused_4379_ = lean_ctor_get(v_acc_4273_, 0);
lean_dec(v_unused_4379_);
v___x_4318_ = v_acc_4273_;
v_isShared_4319_ = v_isSharedCheck_4378_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_snd_4316_);
lean_dec(v_acc_4273_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4378_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v_type_4320_; lean_object* v_value_4321_; uint8_t v___x_4322_; 
v_type_4320_ = lean_ctor_get(v_a_4315_, 1);
v_value_4321_ = lean_ctor_get(v_a_4315_, 2);
lean_inc_ref(v_type_4320_);
v___x_4322_ = l_Lean_Expr_isFalse(v_type_4320_);
if (v___x_4322_ == 0)
{
lean_object* v_type_4323_; lean_object* v___f_4324_; uint8_t v___x_4353_; 
lean_del_object(v___x_4318_);
v_type_4323_ = lean_ctor_get(v___x_4313_, 1);
lean_inc(v___x_4267_);
lean_inc(v_a_4315_);
lean_inc(v_snd_4316_);
v___f_4324_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4324_, 0, v_snd_4316_);
lean_closure_set(v___f_4324_, 1, v_a_4315_);
lean_closure_set(v___f_4324_, 2, v___x_4267_);
v___x_4353_ = lean_expr_eqv(v_type_4323_, v_type_4320_);
if (v___x_4353_ == 0)
{
lean_inc_ref(v_type_4320_);
lean_dec(v_snd_4316_);
lean_dec(v_a_4315_);
lean_dec(v___x_4267_);
goto v___jp_4328_;
}
else
{
if (v___x_4322_ == 0)
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
lean_dec_ref(v___f_4324_);
lean_dec(v___f_4271_);
lean_dec_ref(v_toMonadRef_4270_);
lean_dec_ref(v___x_4269_);
lean_dec_ref(v___x_4268_);
v___x_4354_ = lean_box(0);
v___x_4355_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4316_, v_a_4315_, v___x_4267_, v___x_4354_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
v___y_4289_ = v___x_4355_;
goto v___jp_4288_;
}
else
{
lean_inc_ref(v_type_4320_);
lean_dec(v_snd_4316_);
lean_dec(v_a_4315_);
lean_dec(v___x_4267_);
goto v___jp_4328_;
}
}
v___jp_4325_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = lean_box(0);
v___x_4327_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4311_, v___f_4324_, v___x_4326_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
v___y_4289_ = v___x_4327_;
goto v___jp_4288_;
}
v___jp_4328_:
{
lean_object* v_options_4329_; uint8_t v_hasTrace_4330_; 
v_options_4329_ = lean_ctor_get(v___y_4285_, 2);
v_hasTrace_4330_ = lean_ctor_get_uint8(v_options_4329_, sizeof(void*)*1);
if (v_hasTrace_4330_ == 0)
{
lean_dec_ref(v_type_4320_);
lean_dec(v___f_4271_);
lean_dec_ref(v_toMonadRef_4270_);
lean_dec_ref(v___x_4269_);
lean_dec_ref(v___x_4268_);
goto v___jp_4325_;
}
else
{
lean_object* v_inheritedTraceOptions_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; uint8_t v___x_4334_; 
v_inheritedTraceOptions_4331_ = lean_ctor_get(v___y_4285_, 13);
v___x_4332_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_4333_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_4334_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4331_, v_options_4329_, v___x_4333_);
if (v___x_4334_ == 0)
{
lean_dec_ref(v_type_4320_);
lean_dec(v___f_4271_);
lean_dec_ref(v_toMonadRef_4270_);
lean_dec_ref(v___x_4269_);
lean_dec_ref(v___x_4268_);
goto v___jp_4325_;
}
else
{
lean_object* v_type_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_22071__overap_4341_; lean_object* v___x_4342_; 
v_type_4335_ = lean_ctor_get(v___x_4313_, 1);
lean_inc_ref(v_type_4335_);
v___x_4336_ = l_Lean_MessageData_ofExpr(v_type_4335_);
v___x_4337_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = l_Lean_MessageData_ofExpr(v_type_4320_);
v___x_4340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_22071__overap_4341_ = l_Lean_addTrace___redArg(v___x_4268_, v___x_4269_, v_toMonadRef_4270_, v___f_4271_, v___x_4332_, v___x_4340_);
lean_inc(v___y_4286_);
lean_inc_ref(v___y_4285_);
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
lean_inc(v___y_4280_);
lean_inc_ref(v___y_4279_);
lean_inc(v___y_4278_);
lean_inc(v___y_4277_);
lean_inc_ref(v___y_4276_);
v___x_4342_ = lean_apply_12(v___x_22071__overap_4341_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, lean_box(0));
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4344_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_a_4343_);
lean_dec_ref_known(v___x_4342_, 1);
v___x_4344_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4311_, v___f_4324_, v_a_4343_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
v___y_4289_ = v___x_4344_;
goto v___jp_4288_;
}
else
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
lean_dec_ref(v___f_4324_);
lean_dec_ref(v_G_4275_);
v_a_4345_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4347_ = v___x_4342_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v___x_4342_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_a_4345_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4356_; 
lean_inc_ref(v_value_4321_);
lean_dec(v_a_4315_);
lean_dec_ref(v_G_4275_);
lean_dec(v___f_4271_);
lean_dec_ref(v_toMonadRef_4270_);
lean_dec_ref(v___x_4269_);
lean_dec_ref(v___x_4268_);
lean_dec(v___x_4267_);
v___x_4356_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4321_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4368_; 
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4368_ == 0)
{
lean_object* v_unused_4369_; 
v_unused_4369_ = lean_ctor_get(v___x_4356_, 0);
lean_dec(v_unused_4369_);
v___x_4358_ = v___x_4356_;
v_isShared_4359_ = v_isSharedCheck_4368_;
goto v_resetjp_4357_;
}
else
{
lean_dec(v___x_4356_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4368_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
v___x_4360_ = lean_box(v___x_4322_);
v___x_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v___x_4361_);
v___x_4363_ = v___x_4318_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4361_);
lean_ctor_set(v_reuseFailAlloc_4367_, 1, v_snd_4316_);
v___x_4363_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4365_; 
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4363_);
v___x_4365_ = v___x_4358_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4363_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
lean_del_object(v___x_4318_);
lean_dec(v_snd_4316_);
v_a_4370_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4356_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4356_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec_ref(v_G_4275_);
lean_dec_ref(v_acc_4273_);
lean_dec(v___f_4271_);
lean_dec_ref(v_toMonadRef_4270_);
lean_dec_ref(v___x_4269_);
lean_dec_ref(v___x_4268_);
lean_dec(v___x_4267_);
v_a_4380_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4314_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4314_);
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
v___jp_4288_:
{
if (lean_obj_tag(v___y_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4302_; 
v_a_4290_ = lean_ctor_get(v___y_4289_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___y_4289_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4292_ = v___y_4289_;
v_isShared_4293_ = v_isSharedCheck_4302_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___y_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4302_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
if (lean_obj_tag(v_a_4290_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4296_; 
lean_dec_ref(v_G_4275_);
v_a_4294_ = lean_ctor_get(v_a_4290_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v_a_4290_, 1);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v_a_4294_);
v___x_4296_ = v___x_4292_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4294_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
lean_del_object(v___x_4292_);
v_a_4298_ = lean_ctor_get(v_a_4290_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v_a_4290_, 1);
v___x_4299_ = lean_unsigned_to_nat(1u);
v___x_4300_ = lean_nat_add(v_next_4272_, v___x_4299_);
lean_inc(v___y_4286_);
lean_inc_ref(v___y_4285_);
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
lean_inc(v___y_4280_);
lean_inc_ref(v___y_4279_);
lean_inc(v___y_4278_);
lean_inc(v___y_4277_);
lean_inc_ref(v___y_4276_);
v___x_4301_ = lean_apply_16(v_G_4275_, v___x_4300_, v_a_4298_, lean_box(0), lean_box(0), v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, lean_box(0));
return v___x_4301_;
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
lean_dec_ref(v_G_4275_);
v_a_4303_ = lean_ctor_get(v___y_4289_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___y_4289_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___y_4289_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___y_4289_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4388_ = _args[0];
lean_object* v_hypotheses_4389_ = _args[1];
lean_object* v_cacheId_4390_ = _args[2];
lean_object* v_methods_4391_ = _args[3];
lean_object* v_config_4392_ = _args[4];
lean_object* v___x_4393_ = _args[5];
lean_object* v___x_4394_ = _args[6];
lean_object* v___x_4395_ = _args[7];
lean_object* v_toMonadRef_4396_ = _args[8];
lean_object* v___f_4397_ = _args[9];
lean_object* v_next_4398_ = _args[10];
lean_object* v_acc_4399_ = _args[11];
lean_object* v_h_4400_ = _args[12];
lean_object* v_G_4401_ = _args[13];
lean_object* v___y_4402_ = _args[14];
lean_object* v___y_4403_ = _args[15];
lean_object* v___y_4404_ = _args[16];
lean_object* v___y_4405_ = _args[17];
lean_object* v___y_4406_ = _args[18];
lean_object* v___y_4407_ = _args[19];
lean_object* v___y_4408_ = _args[20];
lean_object* v___y_4409_ = _args[21];
lean_object* v___y_4410_ = _args[22];
lean_object* v___y_4411_ = _args[23];
lean_object* v___y_4412_ = _args[24];
lean_object* v___y_4413_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4414_; lean_object* v_res_4415_; 
v_cacheId_boxed_4414_ = lean_unbox(v_cacheId_4390_);
v_res_4415_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4388_, v_hypotheses_4389_, v_cacheId_boxed_4414_, v_methods_4391_, v_config_4392_, v___x_4393_, v___x_4394_, v___x_4395_, v_toMonadRef_4396_, v___f_4397_, v_next_4398_, v_acc_4399_, v_h_4400_, v_G_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v_next_4398_);
lean_dec_ref(v_hypotheses_4389_);
lean_dec(v___x_4388_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4416_, lean_object* v_methods_4417_, lean_object* v_config_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_){
_start:
{
lean_object* v___x_4431_; lean_object* v_toApplicative_4432_; lean_object* v_toFunctor_4433_; lean_object* v_toSeq_4434_; lean_object* v_toSeqLeft_4435_; lean_object* v_toSeqRight_4436_; lean_object* v___f_4437_; lean_object* v___f_4438_; lean_object* v___f_4439_; lean_object* v___f_4440_; lean_object* v___x_4441_; lean_object* v___f_4442_; lean_object* v___f_4443_; lean_object* v___f_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v_toApplicative_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4535_; 
v___x_4431_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4432_ = lean_ctor_get(v___x_4431_, 0);
v_toFunctor_4433_ = lean_ctor_get(v_toApplicative_4432_, 0);
v_toSeq_4434_ = lean_ctor_get(v_toApplicative_4432_, 2);
v_toSeqLeft_4435_ = lean_ctor_get(v_toApplicative_4432_, 3);
v_toSeqRight_4436_ = lean_ctor_get(v_toApplicative_4432_, 4);
v___f_4437_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4438_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4433_, 2);
v___f_4439_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4439_, 0, v_toFunctor_4433_);
v___f_4440_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4440_, 0, v_toFunctor_4433_);
v___x_4441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___f_4439_);
lean_ctor_set(v___x_4441_, 1, v___f_4440_);
lean_inc(v_toSeqRight_4436_);
v___f_4442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4442_, 0, v_toSeqRight_4436_);
lean_inc(v_toSeqLeft_4435_);
v___f_4443_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4443_, 0, v_toSeqLeft_4435_);
lean_inc(v_toSeq_4434_);
v___f_4444_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4444_, 0, v_toSeq_4434_);
v___x_4445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4441_);
lean_ctor_set(v___x_4445_, 1, v___f_4437_);
lean_ctor_set(v___x_4445_, 2, v___f_4444_);
lean_ctor_set(v___x_4445_, 3, v___f_4443_);
lean_ctor_set(v___x_4445_, 4, v___f_4442_);
v___x_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4445_);
lean_ctor_set(v___x_4446_, 1, v___f_4438_);
v___x_4447_ = l_StateRefT_x27_instMonad___redArg(v___x_4446_);
v_toApplicative_4448_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4535_ == 0)
{
lean_object* v_unused_4536_; 
v_unused_4536_ = lean_ctor_get(v___x_4447_, 1);
lean_dec(v_unused_4536_);
v___x_4450_ = v___x_4447_;
v_isShared_4451_ = v_isSharedCheck_4535_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_toApplicative_4448_);
lean_dec(v___x_4447_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4535_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v_toFunctor_4452_; lean_object* v_toSeq_4453_; lean_object* v_toSeqLeft_4454_; lean_object* v_toSeqRight_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4533_; 
v_toFunctor_4452_ = lean_ctor_get(v_toApplicative_4448_, 0);
v_toSeq_4453_ = lean_ctor_get(v_toApplicative_4448_, 2);
v_toSeqLeft_4454_ = lean_ctor_get(v_toApplicative_4448_, 3);
v_toSeqRight_4455_ = lean_ctor_get(v_toApplicative_4448_, 4);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_toApplicative_4448_);
if (v_isSharedCheck_4533_ == 0)
{
lean_object* v_unused_4534_; 
v_unused_4534_ = lean_ctor_get(v_toApplicative_4448_, 1);
lean_dec(v_unused_4534_);
v___x_4457_ = v_toApplicative_4448_;
v_isShared_4458_ = v_isSharedCheck_4533_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_toSeqRight_4455_);
lean_inc(v_toSeqLeft_4454_);
lean_inc(v_toSeq_4453_);
lean_inc(v_toFunctor_4452_);
lean_dec(v_toApplicative_4448_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4533_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___f_4459_; lean_object* v___f_4460_; lean_object* v___f_4461_; lean_object* v___f_4462_; lean_object* v___x_4463_; lean_object* v___f_4464_; lean_object* v___f_4465_; lean_object* v___f_4466_; lean_object* v___x_4468_; 
v___f_4459_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4460_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4452_);
v___f_4461_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4461_, 0, v_toFunctor_4452_);
v___f_4462_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4462_, 0, v_toFunctor_4452_);
v___x_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___f_4461_);
lean_ctor_set(v___x_4463_, 1, v___f_4462_);
v___f_4464_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4464_, 0, v_toSeqRight_4455_);
v___f_4465_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4465_, 0, v_toSeqLeft_4454_);
v___f_4466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4466_, 0, v_toSeq_4453_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 4, v___f_4464_);
lean_ctor_set(v___x_4457_, 3, v___f_4465_);
lean_ctor_set(v___x_4457_, 2, v___f_4466_);
lean_ctor_set(v___x_4457_, 1, v___f_4459_);
lean_ctor_set(v___x_4457_, 0, v___x_4463_);
v___x_4468_ = v___x_4457_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___f_4459_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v___f_4466_);
lean_ctor_set(v_reuseFailAlloc_4532_, 3, v___f_4465_);
lean_ctor_set(v_reuseFailAlloc_4532_, 4, v___f_4464_);
v___x_4468_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4470_; 
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 1, v___f_4460_);
lean_ctor_set(v___x_4450_, 0, v___x_4468_);
v___x_4470_ = v___x_4450_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v___f_4460_);
v___x_4470_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v_toMonadRef_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v_hypotheses_4482_; lean_object* v___f_4483_; lean_object* v___x_4484_; lean_object* v_newHyps_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___f_4489_; lean_object* v___x_4490_; lean_object* v___x_21853__overap_4491_; lean_object* v___x_4492_; 
v___x_4471_ = l_StateRefT_x27_instMonad___redArg(v___x_4470_);
v___x_4472_ = l_ReaderT_instMonad___redArg(v___x_4471_);
v___x_4473_ = l_StateRefT_x27_instMonad___redArg(v___x_4472_);
v___x_4474_ = l_ReaderT_instMonad___redArg(v___x_4473_);
v___x_4475_ = l_ReaderT_instMonad___redArg(v___x_4474_);
v___x_4476_ = l_StateRefT_x27_instMonad___redArg(v___x_4475_);
v___x_4477_ = l_ReaderT_instMonad___redArg(v___x_4476_);
v___x_4478_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_4479_ = lean_ctor_get(v___x_4478_, 0);
v___x_4480_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4481_ = lean_st_ref_get(v_a_4420_);
v_hypotheses_4482_ = lean_ctor_get(v___x_4481_, 3);
lean_inc_ref(v_hypotheses_4482_);
lean_dec(v___x_4481_);
v___f_4483_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4484_ = lean_array_get_size(v_hypotheses_4482_);
v_newHyps_4485_ = lean_mk_empty_array_with_capacity(v___x_4484_);
v___x_4486_ = lean_unsigned_to_nat(0u);
v___x_4487_ = lean_box(0);
v___x_4488_ = lean_box(v_cacheId_4416_);
lean_inc_ref(v_toMonadRef_4479_);
v___f_4489_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4489_, 0, v___x_4484_);
lean_closure_set(v___f_4489_, 1, v_hypotheses_4482_);
lean_closure_set(v___f_4489_, 2, v___x_4488_);
lean_closure_set(v___f_4489_, 3, v_methods_4417_);
lean_closure_set(v___f_4489_, 4, v_config_4418_);
lean_closure_set(v___f_4489_, 5, v___x_4487_);
lean_closure_set(v___f_4489_, 6, v___x_4477_);
lean_closure_set(v___f_4489_, 7, v___x_4480_);
lean_closure_set(v___f_4489_, 8, v_toMonadRef_4479_);
lean_closure_set(v___f_4489_, 9, v___f_4483_);
v___x_4490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4487_);
lean_ctor_set(v___x_4490_, 1, v_newHyps_4485_);
v___x_21853__overap_4491_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4489_, v___x_4486_, v___x_4490_, lean_box(0));
lean_inc(v_a_4429_);
lean_inc_ref(v_a_4428_);
lean_inc(v_a_4427_);
lean_inc_ref(v_a_4426_);
lean_inc(v_a_4425_);
lean_inc_ref(v_a_4424_);
lean_inc(v_a_4423_);
lean_inc_ref(v_a_4422_);
lean_inc(v_a_4421_);
lean_inc(v_a_4420_);
lean_inc_ref(v_a_4419_);
v___x_4492_ = lean_apply_12(v___x_21853__overap_4491_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, lean_box(0));
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4522_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4495_ = v___x_4492_;
v_isShared_4496_ = v_isSharedCheck_4522_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4492_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4522_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v_fst_4497_; 
v_fst_4497_ = lean_ctor_get(v_a_4493_, 0);
if (lean_obj_tag(v_fst_4497_) == 0)
{
lean_object* v_snd_4498_; lean_object* v___x_4499_; lean_object* v_caches_4500_; lean_object* v_typeAnalysis_4501_; lean_object* v_target_4502_; uint8_t v_didChange_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4516_; 
v_snd_4498_ = lean_ctor_get(v_a_4493_, 1);
lean_inc(v_snd_4498_);
lean_dec(v_a_4493_);
v___x_4499_ = lean_st_ref_take(v_a_4420_);
v_caches_4500_ = lean_ctor_get(v___x_4499_, 0);
v_typeAnalysis_4501_ = lean_ctor_get(v___x_4499_, 1);
v_target_4502_ = lean_ctor_get(v___x_4499_, 2);
v_didChange_4503_ = lean_ctor_get_uint8(v___x_4499_, sizeof(void*)*4);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4516_ == 0)
{
lean_object* v_unused_4517_; 
v_unused_4517_ = lean_ctor_get(v___x_4499_, 3);
lean_dec(v_unused_4517_);
v___x_4505_ = v___x_4499_;
v_isShared_4506_ = v_isSharedCheck_4516_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_target_4502_);
lean_inc(v_typeAnalysis_4501_);
lean_inc(v_caches_4500_);
lean_dec(v___x_4499_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4516_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 3, v_snd_4498_);
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_caches_4500_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_typeAnalysis_4501_);
lean_ctor_set(v_reuseFailAlloc_4515_, 2, v_target_4502_);
lean_ctor_set(v_reuseFailAlloc_4515_, 3, v_snd_4498_);
lean_ctor_set_uint8(v_reuseFailAlloc_4515_, sizeof(void*)*4, v_didChange_4503_);
v___x_4508_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4509_; uint8_t v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4513_; 
v___x_4509_ = lean_st_ref_put(v_a_4420_, v___x_4508_);
v___x_4510_ = 0;
v___x_4511_ = lean_box(v___x_4510_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4511_);
v___x_4513_ = v___x_4495_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4511_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
else
{
lean_object* v_val_4518_; lean_object* v___x_4520_; 
lean_inc_ref(v_fst_4497_);
lean_dec(v_a_4493_);
v_val_4518_ = lean_ctor_get(v_fst_4497_, 0);
lean_inc(v_val_4518_);
lean_dec_ref_known(v_fst_4497_, 1);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v_val_4518_);
v___x_4520_ = v___x_4495_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_val_4518_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
v_a_4523_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4492_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4492_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_4537_, lean_object* v_methods_4538_, lean_object* v_config_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_){
_start:
{
uint8_t v_cacheId_boxed_4552_; lean_object* v_res_4553_; 
v_cacheId_boxed_4552_ = lean_unbox(v_cacheId_4537_);
v_res_4553_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_4552_, v_methods_4538_, v_config_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_4554_, lean_object* v_hypotheses_4555_, uint8_t v_cacheId_4556_, lean_object* v_methods_4557_, lean_object* v_config_4558_, lean_object* v___x_4559_, lean_object* v___x_4560_, lean_object* v___x_4561_, lean_object* v_toMonadRef_4562_, lean_object* v___f_4563_, lean_object* v_next_4564_, lean_object* v_acc_4565_, lean_object* v_h_4566_, lean_object* v_G_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v___y_4581_; uint8_t v___x_4603_; 
v___x_4603_ = lean_nat_dec_lt(v_next_4564_, v___x_4554_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; 
lean_dec_ref(v_G_4567_);
lean_dec(v___f_4563_);
lean_dec_ref(v_toMonadRef_4562_);
lean_dec_ref(v___x_4561_);
lean_dec_ref(v___x_4560_);
lean_dec(v___x_4559_);
lean_dec_ref(v_config_4558_);
lean_dec_ref(v_methods_4557_);
v___x_4604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4604_, 0, v_acc_4565_);
return v___x_4604_;
}
else
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = lean_array_fget_borrowed(v_hypotheses_4555_, v_next_4564_);
lean_inc(v___x_4605_);
v___x_4606_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4556_, v_methods_4557_, v_config_4558_, v___x_4605_, v___y_4569_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v_snd_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4670_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4607_);
lean_dec_ref_known(v___x_4606_, 1);
v_snd_4608_ = lean_ctor_get(v_acc_4565_, 1);
v_isSharedCheck_4670_ = !lean_is_exclusive(v_acc_4565_);
if (v_isSharedCheck_4670_ == 0)
{
lean_object* v_unused_4671_; 
v_unused_4671_ = lean_ctor_get(v_acc_4565_, 0);
lean_dec(v_unused_4671_);
v___x_4610_ = v_acc_4565_;
v_isShared_4611_ = v_isSharedCheck_4670_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_snd_4608_);
lean_dec(v_acc_4565_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4670_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v_type_4612_; lean_object* v_value_4613_; uint8_t v___x_4614_; 
v_type_4612_ = lean_ctor_get(v_a_4607_, 1);
v_value_4613_ = lean_ctor_get(v_a_4607_, 2);
lean_inc_ref(v_type_4612_);
v___x_4614_ = l_Lean_Expr_isFalse(v_type_4612_);
if (v___x_4614_ == 0)
{
lean_object* v_type_4615_; lean_object* v___f_4616_; uint8_t v___x_4645_; 
lean_del_object(v___x_4610_);
v_type_4615_ = lean_ctor_get(v___x_4605_, 1);
lean_inc(v___x_4559_);
lean_inc(v_a_4607_);
lean_inc(v_snd_4608_);
v___f_4616_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4616_, 0, v_snd_4608_);
lean_closure_set(v___f_4616_, 1, v_a_4607_);
lean_closure_set(v___f_4616_, 2, v___x_4559_);
v___x_4645_ = lean_expr_eqv(v_type_4615_, v_type_4612_);
if (v___x_4645_ == 0)
{
lean_inc_ref(v_type_4612_);
lean_dec(v_snd_4608_);
lean_dec(v_a_4607_);
lean_dec(v___x_4559_);
goto v___jp_4620_;
}
else
{
if (v___x_4614_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
lean_dec_ref(v___f_4616_);
lean_dec(v___f_4563_);
lean_dec_ref(v_toMonadRef_4562_);
lean_dec_ref(v___x_4561_);
lean_dec_ref(v___x_4560_);
v___x_4646_ = lean_box(0);
v___x_4647_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4608_, v_a_4607_, v___x_4559_, v___x_4646_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
v___y_4581_ = v___x_4647_;
goto v___jp_4580_;
}
else
{
lean_inc_ref(v_type_4612_);
lean_dec(v_snd_4608_);
lean_dec(v_a_4607_);
lean_dec(v___x_4559_);
goto v___jp_4620_;
}
}
v___jp_4617_:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = lean_box(0);
v___x_4619_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4603_, v___f_4616_, v___x_4618_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
v___y_4581_ = v___x_4619_;
goto v___jp_4580_;
}
v___jp_4620_:
{
lean_object* v_options_4621_; uint8_t v_hasTrace_4622_; 
v_options_4621_ = lean_ctor_get(v___y_4577_, 2);
v_hasTrace_4622_ = lean_ctor_get_uint8(v_options_4621_, sizeof(void*)*1);
if (v_hasTrace_4622_ == 0)
{
lean_dec_ref(v_type_4612_);
lean_dec(v___f_4563_);
lean_dec_ref(v_toMonadRef_4562_);
lean_dec_ref(v___x_4561_);
lean_dec_ref(v___x_4560_);
goto v___jp_4617_;
}
else
{
lean_object* v_inheritedTraceOptions_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; uint8_t v___x_4626_; 
v_inheritedTraceOptions_4623_ = lean_ctor_get(v___y_4577_, 13);
v___x_4624_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_4625_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_4626_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4623_, v_options_4621_, v___x_4625_);
if (v___x_4626_ == 0)
{
lean_dec_ref(v_type_4612_);
lean_dec(v___f_4563_);
lean_dec_ref(v_toMonadRef_4562_);
lean_dec_ref(v___x_4561_);
lean_dec_ref(v___x_4560_);
goto v___jp_4617_;
}
else
{
lean_object* v_type_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_22071__overap_4633_; lean_object* v___x_4634_; 
v_type_4627_ = lean_ctor_get(v___x_4605_, 1);
lean_inc_ref(v_type_4627_);
v___x_4628_ = l_Lean_MessageData_ofExpr(v_type_4627_);
v___x_4629_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4628_);
lean_ctor_set(v___x_4630_, 1, v___x_4629_);
v___x_4631_ = l_Lean_MessageData_ofExpr(v_type_4612_);
v___x_4632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4630_);
lean_ctor_set(v___x_4632_, 1, v___x_4631_);
v___x_22071__overap_4633_ = l_Lean_addTrace___redArg(v___x_4560_, v___x_4561_, v_toMonadRef_4562_, v___f_4563_, v___x_4624_, v___x_4632_);
lean_inc(v___y_4578_);
lean_inc_ref(v___y_4577_);
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4575_);
lean_inc(v___y_4574_);
lean_inc_ref(v___y_4573_);
lean_inc(v___y_4572_);
lean_inc_ref(v___y_4571_);
lean_inc(v___y_4570_);
lean_inc(v___y_4569_);
lean_inc_ref(v___y_4568_);
v___x_4634_ = lean_apply_12(v___x_22071__overap_4633_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, lean_box(0));
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4636_; 
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
lean_inc(v_a_4635_);
lean_dec_ref_known(v___x_4634_, 1);
v___x_4636_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4603_, v___f_4616_, v_a_4635_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
v___y_4581_ = v___x_4636_;
goto v___jp_4580_;
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec_ref(v___f_4616_);
lean_dec_ref(v_G_4567_);
v_a_4637_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4634_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4634_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4648_; 
lean_inc_ref(v_value_4613_);
lean_dec(v_a_4607_);
lean_dec_ref(v_G_4567_);
lean_dec(v___f_4563_);
lean_dec_ref(v_toMonadRef_4562_);
lean_dec_ref(v___x_4561_);
lean_dec_ref(v___x_4560_);
lean_dec(v___x_4559_);
v___x_4648_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4613_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4660_; 
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4660_ == 0)
{
lean_object* v_unused_4661_; 
v_unused_4661_ = lean_ctor_get(v___x_4648_, 0);
lean_dec(v_unused_4661_);
v___x_4650_ = v___x_4648_;
v_isShared_4651_ = v_isSharedCheck_4660_;
goto v_resetjp_4649_;
}
else
{
lean_dec(v___x_4648_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4660_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4655_; 
v___x_4652_ = lean_box(v___x_4614_);
v___x_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 0, v___x_4653_);
v___x_4655_ = v___x_4610_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_snd_4608_);
v___x_4655_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4657_; 
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 0, v___x_4655_);
v___x_4657_ = v___x_4650_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_del_object(v___x_4610_);
lean_dec(v_snd_4608_);
v_a_4662_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4648_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4648_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec_ref(v_G_4567_);
lean_dec_ref(v_acc_4565_);
lean_dec(v___f_4563_);
lean_dec_ref(v_toMonadRef_4562_);
lean_dec_ref(v___x_4561_);
lean_dec_ref(v___x_4560_);
lean_dec(v___x_4559_);
v_a_4672_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4606_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4606_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
v___jp_4580_:
{
if (lean_obj_tag(v___y_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4594_; 
v_a_4582_ = lean_ctor_get(v___y_4581_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___y_4581_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4584_ = v___y_4581_;
v_isShared_4585_ = v_isSharedCheck_4594_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___y_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4594_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
if (lean_obj_tag(v_a_4582_) == 0)
{
lean_object* v_a_4586_; lean_object* v___x_4588_; 
lean_dec_ref(v_G_4567_);
v_a_4586_ = lean_ctor_get(v_a_4582_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v_a_4582_, 1);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v_a_4586_);
v___x_4588_ = v___x_4584_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4586_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
lean_del_object(v___x_4584_);
v_a_4590_ = lean_ctor_get(v_a_4582_, 0);
lean_inc(v_a_4590_);
lean_dec_ref_known(v_a_4582_, 1);
v___x_4591_ = lean_unsigned_to_nat(1u);
v___x_4592_ = lean_nat_add(v_next_4564_, v___x_4591_);
lean_inc(v___y_4578_);
lean_inc_ref(v___y_4577_);
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4575_);
lean_inc(v___y_4574_);
lean_inc_ref(v___y_4573_);
lean_inc(v___y_4572_);
lean_inc_ref(v___y_4571_);
lean_inc(v___y_4570_);
lean_inc(v___y_4569_);
lean_inc_ref(v___y_4568_);
v___x_4593_ = lean_apply_16(v_G_4567_, v___x_4592_, v_a_4590_, lean_box(0), lean_box(0), v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, lean_box(0));
return v___x_4593_;
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
lean_dec_ref(v_G_4567_);
v_a_4595_ = lean_ctor_get(v___y_4581_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___y_4581_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___y_4581_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___y_4581_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4680_ = _args[0];
lean_object* v_hypotheses_4681_ = _args[1];
lean_object* v_cacheId_4682_ = _args[2];
lean_object* v_methods_4683_ = _args[3];
lean_object* v_config_4684_ = _args[4];
lean_object* v___x_4685_ = _args[5];
lean_object* v___x_4686_ = _args[6];
lean_object* v___x_4687_ = _args[7];
lean_object* v_toMonadRef_4688_ = _args[8];
lean_object* v___f_4689_ = _args[9];
lean_object* v_next_4690_ = _args[10];
lean_object* v_acc_4691_ = _args[11];
lean_object* v_h_4692_ = _args[12];
lean_object* v_G_4693_ = _args[13];
lean_object* v___y_4694_ = _args[14];
lean_object* v___y_4695_ = _args[15];
lean_object* v___y_4696_ = _args[16];
lean_object* v___y_4697_ = _args[17];
lean_object* v___y_4698_ = _args[18];
lean_object* v___y_4699_ = _args[19];
lean_object* v___y_4700_ = _args[20];
lean_object* v___y_4701_ = _args[21];
lean_object* v___y_4702_ = _args[22];
lean_object* v___y_4703_ = _args[23];
lean_object* v___y_4704_ = _args[24];
lean_object* v___y_4705_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4706_; lean_object* v_res_4707_; 
v_cacheId_boxed_4706_ = lean_unbox(v_cacheId_4682_);
v_res_4707_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4680_, v_hypotheses_4681_, v_cacheId_boxed_4706_, v_methods_4683_, v_config_4684_, v___x_4685_, v___x_4686_, v___x_4687_, v_toMonadRef_4688_, v___f_4689_, v_next_4690_, v_acc_4691_, v_h_4692_, v_G_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v_next_4690_);
lean_dec_ref(v_hypotheses_4681_);
lean_dec(v___x_4680_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4708_, lean_object* v_methods_4709_, lean_object* v_config_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v___x_4723_; lean_object* v_toApplicative_4724_; lean_object* v_toFunctor_4725_; lean_object* v_toSeq_4726_; lean_object* v_toSeqLeft_4727_; lean_object* v_toSeqRight_4728_; lean_object* v___f_4729_; lean_object* v___f_4730_; lean_object* v___f_4731_; lean_object* v___f_4732_; lean_object* v___x_4733_; lean_object* v___f_4734_; lean_object* v___f_4735_; lean_object* v___f_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v_toApplicative_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4827_; 
v___x_4723_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4724_ = lean_ctor_get(v___x_4723_, 0);
v_toFunctor_4725_ = lean_ctor_get(v_toApplicative_4724_, 0);
v_toSeq_4726_ = lean_ctor_get(v_toApplicative_4724_, 2);
v_toSeqLeft_4727_ = lean_ctor_get(v_toApplicative_4724_, 3);
v_toSeqRight_4728_ = lean_ctor_get(v_toApplicative_4724_, 4);
v___f_4729_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4730_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4725_, 2);
v___f_4731_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4731_, 0, v_toFunctor_4725_);
v___f_4732_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4732_, 0, v_toFunctor_4725_);
v___x_4733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___f_4731_);
lean_ctor_set(v___x_4733_, 1, v___f_4732_);
lean_inc(v_toSeqRight_4728_);
v___f_4734_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4734_, 0, v_toSeqRight_4728_);
lean_inc(v_toSeqLeft_4727_);
v___f_4735_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4735_, 0, v_toSeqLeft_4727_);
lean_inc(v_toSeq_4726_);
v___f_4736_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4736_, 0, v_toSeq_4726_);
v___x_4737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4733_);
lean_ctor_set(v___x_4737_, 1, v___f_4729_);
lean_ctor_set(v___x_4737_, 2, v___f_4736_);
lean_ctor_set(v___x_4737_, 3, v___f_4735_);
lean_ctor_set(v___x_4737_, 4, v___f_4734_);
v___x_4738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
lean_ctor_set(v___x_4738_, 1, v___f_4730_);
v___x_4739_ = l_StateRefT_x27_instMonad___redArg(v___x_4738_);
v_toApplicative_4740_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4827_ == 0)
{
lean_object* v_unused_4828_; 
v_unused_4828_ = lean_ctor_get(v___x_4739_, 1);
lean_dec(v_unused_4828_);
v___x_4742_ = v___x_4739_;
v_isShared_4743_ = v_isSharedCheck_4827_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_toApplicative_4740_);
lean_dec(v___x_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4827_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_toFunctor_4744_; lean_object* v_toSeq_4745_; lean_object* v_toSeqLeft_4746_; lean_object* v_toSeqRight_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4825_; 
v_toFunctor_4744_ = lean_ctor_get(v_toApplicative_4740_, 0);
v_toSeq_4745_ = lean_ctor_get(v_toApplicative_4740_, 2);
v_toSeqLeft_4746_ = lean_ctor_get(v_toApplicative_4740_, 3);
v_toSeqRight_4747_ = lean_ctor_get(v_toApplicative_4740_, 4);
v_isSharedCheck_4825_ = !lean_is_exclusive(v_toApplicative_4740_);
if (v_isSharedCheck_4825_ == 0)
{
lean_object* v_unused_4826_; 
v_unused_4826_ = lean_ctor_get(v_toApplicative_4740_, 1);
lean_dec(v_unused_4826_);
v___x_4749_ = v_toApplicative_4740_;
v_isShared_4750_ = v_isSharedCheck_4825_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_toSeqRight_4747_);
lean_inc(v_toSeqLeft_4746_);
lean_inc(v_toSeq_4745_);
lean_inc(v_toFunctor_4744_);
lean_dec(v_toApplicative_4740_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4825_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___f_4751_; lean_object* v___f_4752_; lean_object* v___f_4753_; lean_object* v___f_4754_; lean_object* v___x_4755_; lean_object* v___f_4756_; lean_object* v___f_4757_; lean_object* v___f_4758_; lean_object* v___x_4760_; 
v___f_4751_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4752_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4744_);
v___f_4753_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4753_, 0, v_toFunctor_4744_);
v___f_4754_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4754_, 0, v_toFunctor_4744_);
v___x_4755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4755_, 0, v___f_4753_);
lean_ctor_set(v___x_4755_, 1, v___f_4754_);
v___f_4756_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4756_, 0, v_toSeqRight_4747_);
v___f_4757_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4757_, 0, v_toSeqLeft_4746_);
v___f_4758_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4758_, 0, v_toSeq_4745_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 4, v___f_4756_);
lean_ctor_set(v___x_4749_, 3, v___f_4757_);
lean_ctor_set(v___x_4749_, 2, v___f_4758_);
lean_ctor_set(v___x_4749_, 1, v___f_4751_);
lean_ctor_set(v___x_4749_, 0, v___x_4755_);
v___x_4760_ = v___x_4749_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4824_, 1, v___f_4751_);
lean_ctor_set(v_reuseFailAlloc_4824_, 2, v___f_4758_);
lean_ctor_set(v_reuseFailAlloc_4824_, 3, v___f_4757_);
lean_ctor_set(v_reuseFailAlloc_4824_, 4, v___f_4756_);
v___x_4760_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4762_; 
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 1, v___f_4752_);
lean_ctor_set(v___x_4742_, 0, v___x_4760_);
v___x_4762_ = v___x_4742_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4760_);
lean_ctor_set(v_reuseFailAlloc_4823_, 1, v___f_4752_);
v___x_4762_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v_toMonadRef_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v_hypotheses_4774_; lean_object* v___f_4775_; lean_object* v___x_4776_; lean_object* v_newHyps_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___f_4781_; lean_object* v___x_4782_; lean_object* v___x_21853__overap_4783_; lean_object* v___x_4784_; 
v___x_4763_ = l_StateRefT_x27_instMonad___redArg(v___x_4762_);
v___x_4764_ = l_ReaderT_instMonad___redArg(v___x_4763_);
v___x_4765_ = l_StateRefT_x27_instMonad___redArg(v___x_4764_);
v___x_4766_ = l_ReaderT_instMonad___redArg(v___x_4765_);
v___x_4767_ = l_ReaderT_instMonad___redArg(v___x_4766_);
v___x_4768_ = l_StateRefT_x27_instMonad___redArg(v___x_4767_);
v___x_4769_ = l_ReaderT_instMonad___redArg(v___x_4768_);
v___x_4770_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_4771_ = lean_ctor_get(v___x_4770_, 0);
v___x_4772_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4773_ = lean_st_ref_get(v_a_4712_);
v_hypotheses_4774_ = lean_ctor_get(v___x_4773_, 3);
lean_inc_ref(v_hypotheses_4774_);
lean_dec(v___x_4773_);
v___f_4775_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4776_ = lean_array_get_size(v_hypotheses_4774_);
v_newHyps_4777_ = lean_mk_empty_array_with_capacity(v___x_4776_);
v___x_4778_ = lean_unsigned_to_nat(0u);
v___x_4779_ = lean_box(0);
v___x_4780_ = lean_box(v_cacheId_4708_);
lean_inc_ref(v_toMonadRef_4771_);
v___f_4781_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4781_, 0, v___x_4776_);
lean_closure_set(v___f_4781_, 1, v_hypotheses_4774_);
lean_closure_set(v___f_4781_, 2, v___x_4780_);
lean_closure_set(v___f_4781_, 3, v_methods_4709_);
lean_closure_set(v___f_4781_, 4, v_config_4710_);
lean_closure_set(v___f_4781_, 5, v___x_4779_);
lean_closure_set(v___f_4781_, 6, v___x_4769_);
lean_closure_set(v___f_4781_, 7, v___x_4772_);
lean_closure_set(v___f_4781_, 8, v_toMonadRef_4771_);
lean_closure_set(v___f_4781_, 9, v___f_4775_);
v___x_4782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4779_);
lean_ctor_set(v___x_4782_, 1, v_newHyps_4777_);
v___x_21853__overap_4783_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4781_, v___x_4778_, v___x_4782_, lean_box(0));
lean_inc(v_a_4721_);
lean_inc_ref(v_a_4720_);
lean_inc(v_a_4719_);
lean_inc_ref(v_a_4718_);
lean_inc(v_a_4717_);
lean_inc_ref(v_a_4716_);
lean_inc(v_a_4715_);
lean_inc_ref(v_a_4714_);
lean_inc(v_a_4713_);
lean_inc(v_a_4712_);
lean_inc_ref(v_a_4711_);
v___x_4784_ = lean_apply_12(v___x_21853__overap_4783_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, lean_box(0));
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4814_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4787_ = v___x_4784_;
v_isShared_4788_ = v_isSharedCheck_4814_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4784_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4814_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v_fst_4789_; 
v_fst_4789_ = lean_ctor_get(v_a_4785_, 0);
if (lean_obj_tag(v_fst_4789_) == 0)
{
lean_object* v_snd_4790_; lean_object* v___x_4791_; lean_object* v_caches_4792_; lean_object* v_typeAnalysis_4793_; lean_object* v_target_4794_; uint8_t v_didChange_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4808_; 
v_snd_4790_ = lean_ctor_get(v_a_4785_, 1);
lean_inc(v_snd_4790_);
lean_dec(v_a_4785_);
v___x_4791_ = lean_st_ref_take(v_a_4712_);
v_caches_4792_ = lean_ctor_get(v___x_4791_, 0);
v_typeAnalysis_4793_ = lean_ctor_get(v___x_4791_, 1);
v_target_4794_ = lean_ctor_get(v___x_4791_, 2);
v_didChange_4795_ = lean_ctor_get_uint8(v___x_4791_, sizeof(void*)*4);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4808_ == 0)
{
lean_object* v_unused_4809_; 
v_unused_4809_ = lean_ctor_get(v___x_4791_, 3);
lean_dec(v_unused_4809_);
v___x_4797_ = v___x_4791_;
v_isShared_4798_ = v_isSharedCheck_4808_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_target_4794_);
lean_inc(v_typeAnalysis_4793_);
lean_inc(v_caches_4792_);
lean_dec(v___x_4791_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4808_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 3, v_snd_4790_);
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_caches_4792_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_typeAnalysis_4793_);
lean_ctor_set(v_reuseFailAlloc_4807_, 2, v_target_4794_);
lean_ctor_set(v_reuseFailAlloc_4807_, 3, v_snd_4790_);
lean_ctor_set_uint8(v_reuseFailAlloc_4807_, sizeof(void*)*4, v_didChange_4795_);
v___x_4800_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4801_; uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4805_; 
v___x_4801_ = lean_st_ref_put(v_a_4712_, v___x_4800_);
v___x_4802_ = 0;
v___x_4803_ = lean_box(v___x_4802_);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4803_);
v___x_4805_ = v___x_4787_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
else
{
lean_object* v_val_4810_; lean_object* v___x_4812_; 
lean_inc_ref(v_fst_4789_);
lean_dec(v_a_4785_);
v_val_4810_ = lean_ctor_get(v_fst_4789_, 0);
lean_inc(v_val_4810_);
lean_dec_ref_known(v_fst_4789_, 1);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v_val_4810_);
v___x_4812_ = v___x_4787_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_val_4810_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
else
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4822_; 
v_a_4815_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4817_ = v___x_4784_;
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4784_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4829_, lean_object* v_methods_4830_, lean_object* v_config_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
uint8_t v_cacheId_boxed_4844_; lean_object* v_res_4845_; 
v_cacheId_boxed_4844_ = lean_unbox(v_cacheId_4829_);
v_res_4845_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4844_, v_methods_4830_, v_config_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec(v_a_4833_);
lean_dec_ref(v_a_4832_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
lean_object* v___x_4852_; lean_object* v_env_4853_; lean_object* v___x_4854_; lean_object* v_mctx_4855_; lean_object* v_lctx_4856_; lean_object* v_options_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4852_ = lean_st_ref_get(v___y_4850_);
v_env_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc_ref(v_env_4853_);
lean_dec(v___x_4852_);
v___x_4854_ = lean_st_ref_get(v___y_4848_);
v_mctx_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc_ref(v_mctx_4855_);
lean_dec(v___x_4854_);
v_lctx_4856_ = lean_ctor_get(v___y_4847_, 2);
v_options_4857_ = lean_ctor_get(v___y_4849_, 2);
lean_inc_ref(v_options_4857_);
lean_inc_ref(v_lctx_4856_);
v___x_4858_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4858_, 0, v_env_4853_);
lean_ctor_set(v___x_4858_, 1, v_mctx_4855_);
lean_ctor_set(v___x_4858_, 2, v_lctx_4856_);
lean_ctor_set(v___x_4858_, 3, v_options_4857_);
v___x_4859_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
lean_ctor_set(v___x_4859_, 1, v_msgData_4846_);
v___x_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4859_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
return v_res_4867_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4868_; double v___x_4869_; 
v___x_4868_ = lean_unsigned_to_nat(0u);
v___x_4869_ = lean_float_of_nat(v___x_4868_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4873_, lean_object* v_msg_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v_ref_4880_; lean_object* v___x_4881_; lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4926_; 
v_ref_4880_ = lean_ctor_get(v___y_4877_, 5);
v___x_4881_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4884_ = v___x_4881_;
v_isShared_4885_ = v_isSharedCheck_4926_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4881_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4926_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4886_; lean_object* v_traceState_4887_; lean_object* v_env_4888_; lean_object* v_nextMacroScope_4889_; lean_object* v_ngen_4890_; lean_object* v_auxDeclNGen_4891_; lean_object* v_cache_4892_; lean_object* v_messages_4893_; lean_object* v_infoState_4894_; lean_object* v_snapshotTasks_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4925_; 
v___x_4886_ = lean_st_ref_take(v___y_4878_);
v_traceState_4887_ = lean_ctor_get(v___x_4886_, 4);
v_env_4888_ = lean_ctor_get(v___x_4886_, 0);
v_nextMacroScope_4889_ = lean_ctor_get(v___x_4886_, 1);
v_ngen_4890_ = lean_ctor_get(v___x_4886_, 2);
v_auxDeclNGen_4891_ = lean_ctor_get(v___x_4886_, 3);
v_cache_4892_ = lean_ctor_get(v___x_4886_, 5);
v_messages_4893_ = lean_ctor_get(v___x_4886_, 6);
v_infoState_4894_ = lean_ctor_get(v___x_4886_, 7);
v_snapshotTasks_4895_ = lean_ctor_get(v___x_4886_, 8);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4897_ = v___x_4886_;
v_isShared_4898_ = v_isSharedCheck_4925_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_snapshotTasks_4895_);
lean_inc(v_infoState_4894_);
lean_inc(v_messages_4893_);
lean_inc(v_cache_4892_);
lean_inc(v_traceState_4887_);
lean_inc(v_auxDeclNGen_4891_);
lean_inc(v_ngen_4890_);
lean_inc(v_nextMacroScope_4889_);
lean_inc(v_env_4888_);
lean_dec(v___x_4886_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4925_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
uint64_t v_tid_4899_; lean_object* v_traces_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4924_; 
v_tid_4899_ = lean_ctor_get_uint64(v_traceState_4887_, sizeof(void*)*1);
v_traces_4900_ = lean_ctor_get(v_traceState_4887_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v_traceState_4887_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4902_ = v_traceState_4887_;
v_isShared_4903_ = v_isSharedCheck_4924_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_traces_4900_);
lean_dec(v_traceState_4887_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4924_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; double v___x_4905_; uint8_t v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4914_; 
v___x_4904_ = lean_box(0);
v___x_4905_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4906_ = 0;
v___x_4907_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4908_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4908_, 0, v_cls_4873_);
lean_ctor_set(v___x_4908_, 1, v___x_4904_);
lean_ctor_set(v___x_4908_, 2, v___x_4907_);
lean_ctor_set_float(v___x_4908_, sizeof(void*)*3, v___x_4905_);
lean_ctor_set_float(v___x_4908_, sizeof(void*)*3 + 8, v___x_4905_);
lean_ctor_set_uint8(v___x_4908_, sizeof(void*)*3 + 16, v___x_4906_);
v___x_4909_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4910_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4908_);
lean_ctor_set(v___x_4910_, 1, v_a_4882_);
lean_ctor_set(v___x_4910_, 2, v___x_4909_);
lean_inc(v_ref_4880_);
v___x_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4911_, 0, v_ref_4880_);
lean_ctor_set(v___x_4911_, 1, v___x_4910_);
v___x_4912_ = l_Lean_PersistentArray_push___redArg(v_traces_4900_, v___x_4911_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v___x_4912_);
v___x_4914_ = v___x_4902_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4912_);
lean_ctor_set_uint64(v_reuseFailAlloc_4923_, sizeof(void*)*1, v_tid_4899_);
v___x_4914_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
lean_object* v___x_4916_; 
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 4, v___x_4914_);
v___x_4916_ = v___x_4897_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_env_4888_);
lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_nextMacroScope_4889_);
lean_ctor_set(v_reuseFailAlloc_4922_, 2, v_ngen_4890_);
lean_ctor_set(v_reuseFailAlloc_4922_, 3, v_auxDeclNGen_4891_);
lean_ctor_set(v_reuseFailAlloc_4922_, 4, v___x_4914_);
lean_ctor_set(v_reuseFailAlloc_4922_, 5, v_cache_4892_);
lean_ctor_set(v_reuseFailAlloc_4922_, 6, v_messages_4893_);
lean_ctor_set(v_reuseFailAlloc_4922_, 7, v_infoState_4894_);
lean_ctor_set(v_reuseFailAlloc_4922_, 8, v_snapshotTasks_4895_);
v___x_4916_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4917_ = lean_st_ref_put(v___y_4878_, v___x_4916_);
v___x_4918_ = lean_box(0);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v___x_4918_);
v___x_4920_ = v___x_4884_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4927_, lean_object* v_msg_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4927_, v_msg_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_);
lean_dec(v___y_4932_);
lean_dec_ref(v___y_4931_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_4935_, lean_object* v___f_4936_, lean_object* v_____r_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v___x_4951_; lean_object* v_caches_4952_; lean_object* v_typeAnalysis_4953_; lean_object* v_target_4954_; lean_object* v_hypotheses_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4965_; 
v___x_4951_ = lean_st_ref_take(v___y_4940_);
v_caches_4952_ = lean_ctor_get(v___x_4951_, 0);
v_typeAnalysis_4953_ = lean_ctor_get(v___x_4951_, 1);
v_target_4954_ = lean_ctor_get(v___x_4951_, 2);
v_hypotheses_4955_ = lean_ctor_get(v___x_4951_, 3);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4957_ = v___x_4951_;
v_isShared_4958_ = v_isSharedCheck_4965_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_hypotheses_4955_);
lean_inc(v_target_4954_);
lean_inc(v_typeAnalysis_4953_);
lean_inc(v_caches_4952_);
lean_dec(v___x_4951_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4965_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4960_; 
if (v_isShared_4958_ == 0)
{
v___x_4960_ = v___x_4957_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_caches_4952_);
lean_ctor_set(v_reuseFailAlloc_4964_, 1, v_typeAnalysis_4953_);
lean_ctor_set(v_reuseFailAlloc_4964_, 2, v_target_4954_);
lean_ctor_set(v_reuseFailAlloc_4964_, 3, v_hypotheses_4955_);
v___x_4960_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*4, v___x_4935_);
v___x_4961_ = lean_st_ref_put(v___y_4940_, v___x_4960_);
v___x_4962_ = lean_box(0);
lean_inc(v___y_4949_);
lean_inc_ref(v___y_4948_);
lean_inc(v___y_4947_);
lean_inc_ref(v___y_4946_);
lean_inc(v___y_4945_);
lean_inc_ref(v___y_4944_);
lean_inc(v___y_4943_);
lean_inc_ref(v___y_4942_);
lean_inc(v___y_4941_);
lean_inc(v___y_4940_);
lean_inc_ref(v___y_4939_);
lean_inc(v___y_4938_);
v___x_4963_ = lean_apply_14(v___f_4936_, v___x_4962_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, lean_box(0));
return v___x_4963_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_4966_, lean_object* v___f_4967_, lean_object* v_____r_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
uint8_t v___x_35708__boxed_4982_; lean_object* v_res_4983_; 
v___x_35708__boxed_4982_ = lean_unbox(v___x_4966_);
v_res_4983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35708__boxed_4982_, v___f_4967_, v_____r_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
lean_dec(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
lean_dec(v___y_4969_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_4984_, lean_object* v_a_4985_, lean_object* v___x_4986_, lean_object* v_____r_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5001_ = lean_array_push(v_snd_4984_, v_a_4985_);
v___x_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_4986_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
v___x_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5003_, 0, v___x_5002_);
v___x_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5004_, 0, v___x_5003_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_5005_ = _args[0];
lean_object* v_a_5006_ = _args[1];
lean_object* v___x_5007_ = _args[2];
lean_object* v_____r_5008_ = _args[3];
lean_object* v___y_5009_ = _args[4];
lean_object* v___y_5010_ = _args[5];
lean_object* v___y_5011_ = _args[6];
lean_object* v___y_5012_ = _args[7];
lean_object* v___y_5013_ = _args[8];
lean_object* v___y_5014_ = _args[9];
lean_object* v___y_5015_ = _args[10];
lean_object* v___y_5016_ = _args[11];
lean_object* v___y_5017_ = _args[12];
lean_object* v___y_5018_ = _args[13];
lean_object* v___y_5019_ = _args[14];
lean_object* v___y_5020_ = _args[15];
lean_object* v___y_5021_ = _args[16];
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5005_, v_a_5006_, v___x_5007_, v_____r_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
lean_dec(v___y_5012_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
lean_dec(v___y_5009_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5023_, lean_object* v___x_5024_, lean_object* v_methods_5025_, lean_object* v_config_5026_, lean_object* v_a_5027_, lean_object* v_b_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
lean_object* v___y_5043_; uint8_t v___x_5065_; 
v___x_5065_ = lean_nat_dec_lt(v_a_5027_, v_upperBound_5023_);
if (v___x_5065_ == 0)
{
lean_object* v___x_5066_; 
lean_dec(v_a_5027_);
lean_dec_ref(v_config_5026_);
lean_dec_ref(v_methods_5025_);
v___x_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5066_, 0, v_b_5028_);
return v___x_5066_;
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v_type_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___x_5067_ = lean_st_ref_take(v___y_5029_);
v___x_5068_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
v___x_5069_ = lean_st_ref_put(v___y_5029_, v___x_5068_);
v___x_5070_ = lean_array_fget_borrowed(v___x_5024_, v_a_5027_);
v_type_5071_ = lean_ctor_get(v___x_5070_, 1);
v___x_5072_ = lean_unsigned_to_nat(0u);
v___x_5073_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5072_);
lean_ctor_set(v___x_5073_, 1, v___x_5067_);
lean_ctor_set(v___x_5073_, 2, v___x_5068_);
lean_ctor_set(v___x_5073_, 3, v___x_5068_);
lean_inc_ref(v_type_5071_);
v___x_5074_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5074_, 0, v_type_5071_);
lean_inc_ref(v_config_5026_);
lean_inc_ref(v_methods_5025_);
v___x_5075_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5074_, v_methods_5025_, v_config_5026_, v___x_5073_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v_a_5076_; lean_object* v_snd_5077_; lean_object* v_fst_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5158_; 
v_a_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_a_5076_);
lean_dec_ref_known(v___x_5075_, 1);
v_snd_5077_ = lean_ctor_get(v_a_5076_, 1);
v_fst_5078_ = lean_ctor_get(v_a_5076_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_a_5076_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5080_ = v_a_5076_;
v_isShared_5081_ = v_isSharedCheck_5158_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_snd_5077_);
lean_inc(v_fst_5078_);
lean_dec(v_a_5076_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5158_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v_persistentCache_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v_persistentCache_5082_ = lean_ctor_get(v_snd_5077_, 1);
lean_inc_ref(v_persistentCache_5082_);
lean_dec(v_snd_5077_);
v___x_5083_ = lean_st_ref_swap(v___y_5029_, v_persistentCache_5082_);
lean_dec(v___x_5083_);
lean_inc(v___x_5070_);
v___x_5084_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5070_, v_fst_5078_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v_snd_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5148_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___x_5084_, 1);
v_snd_5086_ = lean_ctor_get(v_b_5028_, 1);
v_isSharedCheck_5148_ = !lean_is_exclusive(v_b_5028_);
if (v_isSharedCheck_5148_ == 0)
{
lean_object* v_unused_5149_; 
v_unused_5149_ = lean_ctor_get(v_b_5028_, 0);
lean_dec(v_unused_5149_);
v___x_5088_ = v_b_5028_;
v_isShared_5089_ = v_isSharedCheck_5148_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_snd_5086_);
lean_dec(v_b_5028_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5148_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v_type_5090_; lean_object* v_value_5091_; uint8_t v___x_5092_; 
v_type_5090_ = lean_ctor_get(v_a_5085_, 1);
v_value_5091_ = lean_ctor_get(v_a_5085_, 2);
lean_inc_ref(v_type_5090_);
v___x_5092_ = l_Lean_Expr_isFalse(v_type_5090_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; lean_object* v___f_5094_; uint8_t v___x_5123_; 
lean_del_object(v___x_5088_);
v___x_5093_ = lean_box(0);
lean_inc(v_a_5085_);
lean_inc(v_snd_5086_);
v___f_5094_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5094_, 0, v_snd_5086_);
lean_closure_set(v___f_5094_, 1, v_a_5085_);
lean_closure_set(v___f_5094_, 2, v___x_5093_);
v___x_5123_ = lean_expr_eqv(v_type_5071_, v_type_5090_);
if (v___x_5123_ == 0)
{
lean_inc_ref(v_type_5090_);
lean_dec(v_snd_5086_);
lean_dec(v_a_5085_);
goto v___jp_5098_;
}
else
{
if (v___x_5092_ == 0)
{
lean_object* v___x_5124_; lean_object* v___x_5125_; 
lean_dec_ref(v___f_5094_);
lean_del_object(v___x_5080_);
v___x_5124_ = lean_box(0);
v___x_5125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5086_, v_a_5085_, v___x_5093_, v___x_5124_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
v___y_5043_ = v___x_5125_;
goto v___jp_5042_;
}
else
{
lean_inc_ref(v_type_5090_);
lean_dec(v_snd_5086_);
lean_dec(v_a_5085_);
goto v___jp_5098_;
}
}
v___jp_5095_:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5096_ = lean_box(0);
v___x_5097_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5065_, v___f_5094_, v___x_5096_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
v___y_5043_ = v___x_5097_;
goto v___jp_5042_;
}
v___jp_5098_:
{
lean_object* v_options_5099_; uint8_t v_hasTrace_5100_; 
v_options_5099_ = lean_ctor_get(v___y_5039_, 2);
v_hasTrace_5100_ = lean_ctor_get_uint8(v_options_5099_, sizeof(void*)*1);
if (v_hasTrace_5100_ == 0)
{
lean_dec_ref(v_type_5090_);
lean_del_object(v___x_5080_);
goto v___jp_5095_;
}
else
{
lean_object* v_inheritedTraceOptions_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
v_inheritedTraceOptions_5101_ = lean_ctor_get(v___y_5039_, 13);
v___x_5102_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_5103_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_5104_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5101_, v_options_5099_, v___x_5103_);
if (v___x_5104_ == 0)
{
lean_dec_ref(v_type_5090_);
lean_del_object(v___x_5080_);
goto v___jp_5095_;
}
else
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5108_; 
lean_inc_ref(v_type_5071_);
v___x_5105_ = l_Lean_MessageData_ofExpr(v_type_5071_);
v___x_5106_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5081_ == 0)
{
lean_ctor_set_tag(v___x_5080_, 7);
lean_ctor_set(v___x_5080_, 1, v___x_5106_);
lean_ctor_set(v___x_5080_, 0, v___x_5105_);
v___x_5108_ = v___x_5080_;
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
v___x_5111_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5102_, v___x_5110_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; lean_object* v___x_5113_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5112_);
lean_dec_ref_known(v___x_5111_, 1);
v___x_5113_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5065_, v___f_5094_, v_a_5112_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
v___y_5043_ = v___x_5113_;
goto v___jp_5042_;
}
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_dec_ref(v___f_5094_);
lean_dec(v_a_5027_);
lean_dec_ref(v_config_5026_);
lean_dec_ref(v_methods_5025_);
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
lean_dec(v_a_5085_);
lean_del_object(v___x_5080_);
lean_dec(v_a_5027_);
lean_dec_ref(v_config_5026_);
lean_dec_ref(v_methods_5025_);
v___x_5126_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5091_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
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
v___x_5130_ = lean_box(v___x_5092_);
v___x_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5131_, 0, v___x_5130_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 0, v___x_5131_);
v___x_5133_ = v___x_5088_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5131_);
lean_ctor_set(v_reuseFailAlloc_5137_, 1, v_snd_5086_);
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
lean_del_object(v___x_5088_);
lean_dec(v_snd_5086_);
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
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
lean_del_object(v___x_5080_);
lean_dec_ref(v_b_5028_);
lean_dec(v_a_5027_);
lean_dec_ref(v_config_5026_);
lean_dec_ref(v_methods_5025_);
v_a_5150_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_5084_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5084_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_dec_ref(v_b_5028_);
lean_dec(v_a_5027_);
lean_dec_ref(v_config_5026_);
lean_dec_ref(v_methods_5025_);
v_a_5159_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5075_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5075_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
v___jp_5042_:
{
if (lean_obj_tag(v___y_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5056_; 
v_a_5044_ = lean_ctor_get(v___y_5043_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___y_5043_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5046_ = v___y_5043_;
v_isShared_5047_ = v_isSharedCheck_5056_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___y_5043_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5056_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
if (lean_obj_tag(v_a_5044_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5050_; 
lean_dec(v_a_5027_);
lean_dec_ref(v_config_5026_);
lean_dec_ref(v_methods_5025_);
v_a_5048_ = lean_ctor_get(v_a_5044_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v_a_5044_, 1);
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 0, v_a_5048_);
v___x_5050_ = v___x_5046_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5048_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
lean_del_object(v___x_5046_);
v_a_5052_ = lean_ctor_get(v_a_5044_, 0);
lean_inc(v_a_5052_);
lean_dec_ref_known(v_a_5044_, 1);
v___x_5053_ = lean_unsigned_to_nat(1u);
v___x_5054_ = lean_nat_add(v_a_5027_, v___x_5053_);
lean_dec(v_a_5027_);
v_a_5027_ = v___x_5054_;
v_b_5028_ = v_a_5052_;
goto _start;
}
}
}
else
{
lean_object* v_a_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5064_; 
lean_dec(v_a_5027_);
lean_dec_ref(v_config_5026_);
lean_dec_ref(v_methods_5025_);
v_a_5057_ = lean_ctor_get(v___y_5043_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___y_5043_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5059_ = v___y_5043_;
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_a_5057_);
lean_dec(v___y_5043_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v___x_5062_; 
if (v_isShared_5060_ == 0)
{
v___x_5062_ = v___x_5059_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
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
v___x_5356_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__1);
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
lean_object* v_ref_5390_; lean_object* v___x_5391_; lean_object* v_a_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5436_; 
v_ref_5390_ = lean_ctor_get(v___y_5387_, 5);
v___x_5391_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5394_ = v___x_5391_;
v_isShared_5395_ = v_isSharedCheck_5436_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_a_5392_);
lean_dec(v___x_5391_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5436_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v___x_5396_; lean_object* v_traceState_5397_; lean_object* v_env_5398_; lean_object* v_nextMacroScope_5399_; lean_object* v_ngen_5400_; lean_object* v_auxDeclNGen_5401_; lean_object* v_cache_5402_; lean_object* v_messages_5403_; lean_object* v_infoState_5404_; lean_object* v_snapshotTasks_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5435_; 
v___x_5396_ = lean_st_ref_take(v___y_5388_);
v_traceState_5397_ = lean_ctor_get(v___x_5396_, 4);
v_env_5398_ = lean_ctor_get(v___x_5396_, 0);
v_nextMacroScope_5399_ = lean_ctor_get(v___x_5396_, 1);
v_ngen_5400_ = lean_ctor_get(v___x_5396_, 2);
v_auxDeclNGen_5401_ = lean_ctor_get(v___x_5396_, 3);
v_cache_5402_ = lean_ctor_get(v___x_5396_, 5);
v_messages_5403_ = lean_ctor_get(v___x_5396_, 6);
v_infoState_5404_ = lean_ctor_get(v___x_5396_, 7);
v_snapshotTasks_5405_ = lean_ctor_get(v___x_5396_, 8);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5396_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5407_ = v___x_5396_;
v_isShared_5408_ = v_isSharedCheck_5435_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_snapshotTasks_5405_);
lean_inc(v_infoState_5404_);
lean_inc(v_messages_5403_);
lean_inc(v_cache_5402_);
lean_inc(v_traceState_5397_);
lean_inc(v_auxDeclNGen_5401_);
lean_inc(v_ngen_5400_);
lean_inc(v_nextMacroScope_5399_);
lean_inc(v_env_5398_);
lean_dec(v___x_5396_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5435_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
uint64_t v_tid_5409_; lean_object* v_traces_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5434_; 
v_tid_5409_ = lean_ctor_get_uint64(v_traceState_5397_, sizeof(void*)*1);
v_traces_5410_ = lean_ctor_get(v_traceState_5397_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v_traceState_5397_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5412_ = v_traceState_5397_;
v_isShared_5413_ = v_isSharedCheck_5434_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_traces_5410_);
lean_dec(v_traceState_5397_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5434_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v___x_5414_; double v___x_5415_; uint8_t v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5424_; 
v___x_5414_ = lean_box(0);
v___x_5415_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5416_ = 0;
v___x_5417_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5418_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5418_, 0, v_cls_5383_);
lean_ctor_set(v___x_5418_, 1, v___x_5414_);
lean_ctor_set(v___x_5418_, 2, v___x_5417_);
lean_ctor_set_float(v___x_5418_, sizeof(void*)*3, v___x_5415_);
lean_ctor_set_float(v___x_5418_, sizeof(void*)*3 + 8, v___x_5415_);
lean_ctor_set_uint8(v___x_5418_, sizeof(void*)*3 + 16, v___x_5416_);
v___x_5419_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5420_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5420_, 0, v___x_5418_);
lean_ctor_set(v___x_5420_, 1, v_a_5392_);
lean_ctor_set(v___x_5420_, 2, v___x_5419_);
lean_inc(v_ref_5390_);
v___x_5421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5421_, 0, v_ref_5390_);
lean_ctor_set(v___x_5421_, 1, v___x_5420_);
v___x_5422_ = l_Lean_PersistentArray_push___redArg(v_traces_5410_, v___x_5421_);
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 0, v___x_5422_);
v___x_5424_ = v___x_5412_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v___x_5422_);
lean_ctor_set_uint64(v_reuseFailAlloc_5433_, sizeof(void*)*1, v_tid_5409_);
v___x_5424_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
lean_object* v___x_5426_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 4, v___x_5424_);
v___x_5426_ = v___x_5407_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_env_5398_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v_nextMacroScope_5399_);
lean_ctor_set(v_reuseFailAlloc_5432_, 2, v_ngen_5400_);
lean_ctor_set(v_reuseFailAlloc_5432_, 3, v_auxDeclNGen_5401_);
lean_ctor_set(v_reuseFailAlloc_5432_, 4, v___x_5424_);
lean_ctor_set(v_reuseFailAlloc_5432_, 5, v_cache_5402_);
lean_ctor_set(v_reuseFailAlloc_5432_, 6, v_messages_5403_);
lean_ctor_set(v_reuseFailAlloc_5432_, 7, v_infoState_5404_);
lean_ctor_set(v_reuseFailAlloc_5432_, 8, v_snapshotTasks_5405_);
v___x_5426_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5430_; 
v___x_5427_ = lean_st_ref_put(v___y_5388_, v___x_5426_);
v___x_5428_ = lean_box(0);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 0, v___x_5428_);
v___x_5430_ = v___x_5394_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5428_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5437_, lean_object* v_msg_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5437_, v_msg_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
return v_res_5444_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5445_, lean_object* v___x_5446_, lean_object* v_methods_5447_, lean_object* v_config_5448_, lean_object* v_a_5449_, lean_object* v_b_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v___y_5465_; uint8_t v___x_5487_; 
v___x_5487_ = lean_nat_dec_lt(v_a_5449_, v_upperBound_5445_);
if (v___x_5487_ == 0)
{
lean_object* v___x_5488_; 
lean_dec(v_a_5449_);
lean_dec_ref(v_config_5448_);
lean_dec_ref(v_methods_5447_);
v___x_5488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5488_, 0, v_b_5450_);
return v___x_5488_;
}
else
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v_type_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5489_ = lean_st_ref_take(v___y_5451_);
v___x_5490_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5491_ = lean_st_ref_put(v___y_5451_, v___x_5490_);
v___x_5492_ = lean_array_fget_borrowed(v___x_5446_, v_a_5449_);
v_type_5493_ = lean_ctor_get(v___x_5492_, 1);
v___x_5494_ = lean_unsigned_to_nat(0u);
v___x_5495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5494_);
lean_ctor_set(v___x_5495_, 1, v___x_5489_);
lean_inc_ref(v_type_5493_);
v___x_5496_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5496_, 0, v_type_5493_);
lean_inc_ref(v_config_5448_);
lean_inc_ref(v_methods_5447_);
v___x_5497_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5496_, v_methods_5447_, v_config_5448_, v___x_5495_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_object* v_a_5498_; lean_object* v_snd_5499_; lean_object* v_fst_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5587_; 
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_a_5498_);
lean_dec_ref_known(v___x_5497_, 1);
v_snd_5499_ = lean_ctor_get(v_a_5498_, 1);
v_fst_5500_ = lean_ctor_get(v_a_5498_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v_a_5498_);
if (v_isSharedCheck_5587_ == 0)
{
v___x_5502_ = v_a_5498_;
v_isShared_5503_ = v_isSharedCheck_5587_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_snd_5499_);
lean_inc(v_fst_5500_);
lean_dec(v_a_5498_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5587_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v_cache_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5585_; 
v_cache_5504_ = lean_ctor_get(v_snd_5499_, 1);
v_isSharedCheck_5585_ = !lean_is_exclusive(v_snd_5499_);
if (v_isSharedCheck_5585_ == 0)
{
lean_object* v_unused_5586_; 
v_unused_5586_ = lean_ctor_get(v_snd_5499_, 0);
lean_dec(v_unused_5586_);
v___x_5506_ = v_snd_5499_;
v_isShared_5507_ = v_isSharedCheck_5585_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_cache_5504_);
lean_dec(v_snd_5499_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5585_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5508_ = lean_st_ref_swap(v___y_5451_, v_cache_5504_);
lean_dec(v___x_5508_);
lean_inc(v___x_5492_);
v___x_5509_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5492_, v_fst_5500_);
lean_dec(v_fst_5500_);
if (lean_obj_tag(v___x_5509_) == 0)
{
lean_object* v_a_5510_; lean_object* v_snd_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5575_; 
v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
lean_inc(v_a_5510_);
lean_dec_ref_known(v___x_5509_, 1);
v_snd_5511_ = lean_ctor_get(v_b_5450_, 1);
v_isSharedCheck_5575_ = !lean_is_exclusive(v_b_5450_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; 
v_unused_5576_ = lean_ctor_get(v_b_5450_, 0);
lean_dec(v_unused_5576_);
v___x_5513_ = v_b_5450_;
v_isShared_5514_ = v_isSharedCheck_5575_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_snd_5511_);
lean_dec(v_b_5450_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5575_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v_type_5515_; lean_object* v_value_5516_; uint8_t v___x_5517_; 
v_type_5515_ = lean_ctor_get(v_a_5510_, 1);
v_value_5516_ = lean_ctor_get(v_a_5510_, 2);
lean_inc_ref(v_type_5515_);
v___x_5517_ = l_Lean_Expr_isFalse(v_type_5515_);
if (v___x_5517_ == 0)
{
lean_object* v___x_5518_; lean_object* v___f_5519_; uint8_t v___x_5550_; 
lean_del_object(v___x_5513_);
v___x_5518_ = lean_box(0);
lean_inc(v_a_5510_);
lean_inc(v_snd_5511_);
v___f_5519_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5519_, 0, v_snd_5511_);
lean_closure_set(v___f_5519_, 1, v_a_5510_);
lean_closure_set(v___f_5519_, 2, v___x_5518_);
v___x_5550_ = lean_expr_eqv(v_type_5493_, v_type_5515_);
if (v___x_5550_ == 0)
{
lean_inc_ref(v_type_5515_);
lean_dec(v_snd_5511_);
lean_dec(v_a_5510_);
goto v___jp_5523_;
}
else
{
if (v___x_5517_ == 0)
{
lean_object* v___x_5551_; lean_object* v___x_5552_; 
lean_dec_ref(v___f_5519_);
lean_del_object(v___x_5506_);
lean_del_object(v___x_5502_);
v___x_5551_ = lean_box(0);
v___x_5552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5511_, v_a_5510_, v___x_5518_, v___x_5551_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
v___y_5465_ = v___x_5552_;
goto v___jp_5464_;
}
else
{
lean_inc_ref(v_type_5515_);
lean_dec(v_snd_5511_);
lean_dec(v_a_5510_);
goto v___jp_5523_;
}
}
v___jp_5520_:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; 
v___x_5521_ = lean_box(0);
v___x_5522_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5487_, v___f_5519_, v___x_5521_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
v___y_5465_ = v___x_5522_;
goto v___jp_5464_;
}
v___jp_5523_:
{
lean_object* v_options_5524_; uint8_t v_hasTrace_5525_; 
v_options_5524_ = lean_ctor_get(v___y_5461_, 2);
v_hasTrace_5525_ = lean_ctor_get_uint8(v_options_5524_, sizeof(void*)*1);
if (v_hasTrace_5525_ == 0)
{
lean_dec_ref(v_type_5515_);
lean_del_object(v___x_5506_);
lean_del_object(v___x_5502_);
goto v___jp_5520_;
}
else
{
lean_object* v_inheritedTraceOptions_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; uint8_t v___x_5529_; 
v_inheritedTraceOptions_5526_ = lean_ctor_get(v___y_5461_, 13);
v___x_5527_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_5528_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_5529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5526_, v_options_5524_, v___x_5528_);
if (v___x_5529_ == 0)
{
lean_dec_ref(v_type_5515_);
lean_del_object(v___x_5506_);
lean_del_object(v___x_5502_);
goto v___jp_5520_;
}
else
{
lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5533_; 
lean_inc_ref(v_type_5493_);
v___x_5530_ = l_Lean_MessageData_ofExpr(v_type_5493_);
v___x_5531_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5507_ == 0)
{
lean_ctor_set_tag(v___x_5506_, 7);
lean_ctor_set(v___x_5506_, 1, v___x_5531_);
lean_ctor_set(v___x_5506_, 0, v___x_5530_);
v___x_5533_ = v___x_5506_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5530_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v___x_5531_);
v___x_5533_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
lean_object* v___x_5534_; lean_object* v___x_5536_; 
v___x_5534_ = l_Lean_MessageData_ofExpr(v_type_5515_);
if (v_isShared_5503_ == 0)
{
lean_ctor_set_tag(v___x_5502_, 7);
lean_ctor_set(v___x_5502_, 1, v___x_5534_);
lean_ctor_set(v___x_5502_, 0, v___x_5533_);
v___x_5536_ = v___x_5502_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5533_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
lean_object* v___x_5537_; 
v___x_5537_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5527_, v___x_5536_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
if (lean_obj_tag(v___x_5537_) == 0)
{
lean_object* v_a_5538_; lean_object* v___x_5539_; 
v_a_5538_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_a_5538_);
lean_dec_ref_known(v___x_5537_, 1);
v___x_5539_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5487_, v___f_5519_, v_a_5538_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
v___y_5465_ = v___x_5539_;
goto v___jp_5464_;
}
else
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_dec_ref(v___f_5519_);
lean_dec(v_a_5449_);
lean_dec_ref(v_config_5448_);
lean_dec_ref(v_methods_5447_);
v_a_5540_ = lean_ctor_get(v___x_5537_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5537_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5537_);
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
}
}
}
else
{
lean_object* v___x_5553_; 
lean_inc_ref(v_value_5516_);
lean_dec(v_a_5510_);
lean_del_object(v___x_5506_);
lean_del_object(v___x_5502_);
lean_dec(v_a_5449_);
lean_dec_ref(v_config_5448_);
lean_dec_ref(v_methods_5447_);
v___x_5553_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5516_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5565_; 
v_isSharedCheck_5565_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5565_ == 0)
{
lean_object* v_unused_5566_; 
v_unused_5566_ = lean_ctor_get(v___x_5553_, 0);
lean_dec(v_unused_5566_);
v___x_5555_ = v___x_5553_;
v_isShared_5556_ = v_isSharedCheck_5565_;
goto v_resetjp_5554_;
}
else
{
lean_dec(v___x_5553_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5565_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5560_; 
v___x_5557_ = lean_box(v___x_5517_);
v___x_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5557_);
if (v_isShared_5514_ == 0)
{
lean_ctor_set(v___x_5513_, 0, v___x_5558_);
v___x_5560_ = v___x_5513_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5558_);
lean_ctor_set(v_reuseFailAlloc_5564_, 1, v_snd_5511_);
v___x_5560_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
lean_object* v___x_5562_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 0, v___x_5560_);
v___x_5562_ = v___x_5555_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v___x_5560_);
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
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5574_; 
lean_del_object(v___x_5513_);
lean_dec(v_snd_5511_);
v_a_5567_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5569_ = v___x_5553_;
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5553_);
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
else
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5584_; 
lean_del_object(v___x_5506_);
lean_del_object(v___x_5502_);
lean_dec_ref(v_b_5450_);
lean_dec(v_a_5449_);
lean_dec_ref(v_config_5448_);
lean_dec_ref(v_methods_5447_);
v_a_5577_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5579_ = v___x_5509_;
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5509_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5582_; 
if (v_isShared_5580_ == 0)
{
v___x_5582_ = v___x_5579_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5577_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
}
}
else
{
lean_object* v_a_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5595_; 
lean_dec_ref(v_b_5450_);
lean_dec(v_a_5449_);
lean_dec_ref(v_config_5448_);
lean_dec_ref(v_methods_5447_);
v_a_5588_ = lean_ctor_get(v___x_5497_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5497_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5590_ = v___x_5497_;
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_a_5588_);
lean_dec(v___x_5497_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5593_; 
if (v_isShared_5591_ == 0)
{
v___x_5593_ = v___x_5590_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
v___jp_5464_:
{
if (lean_obj_tag(v___y_5465_) == 0)
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5478_; 
v_a_5466_ = lean_ctor_get(v___y_5465_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___y_5465_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5468_ = v___y_5465_;
v_isShared_5469_ = v_isSharedCheck_5478_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___y_5465_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5478_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
if (lean_obj_tag(v_a_5466_) == 0)
{
lean_object* v_a_5470_; lean_object* v___x_5472_; 
lean_dec(v_a_5449_);
lean_dec_ref(v_config_5448_);
lean_dec_ref(v_methods_5447_);
v_a_5470_ = lean_ctor_get(v_a_5466_, 0);
lean_inc(v_a_5470_);
lean_dec_ref_known(v_a_5466_, 1);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v_a_5470_);
v___x_5472_ = v___x_5468_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_a_5470_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
return v___x_5472_;
}
}
else
{
lean_object* v_a_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; 
lean_del_object(v___x_5468_);
v_a_5474_ = lean_ctor_get(v_a_5466_, 0);
lean_inc(v_a_5474_);
lean_dec_ref_known(v_a_5466_, 1);
v___x_5475_ = lean_unsigned_to_nat(1u);
v___x_5476_ = lean_nat_add(v_a_5449_, v___x_5475_);
lean_dec(v_a_5449_);
v_a_5449_ = v___x_5476_;
v_b_5450_ = v_a_5474_;
goto _start;
}
}
}
else
{
lean_object* v_a_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5486_; 
lean_dec(v_a_5449_);
lean_dec_ref(v_config_5448_);
lean_dec_ref(v_methods_5447_);
v_a_5479_ = lean_ctor_get(v___y_5465_, 0);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___y_5465_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5481_ = v___y_5465_;
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_a_5479_);
lean_dec(v___y_5465_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5484_; 
if (v_isShared_5482_ == 0)
{
v___x_5484_ = v___x_5481_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_a_5479_);
v___x_5484_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
return v___x_5484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5596_ = _args[0];
lean_object* v___x_5597_ = _args[1];
lean_object* v_methods_5598_ = _args[2];
lean_object* v_config_5599_ = _args[3];
lean_object* v_a_5600_ = _args[4];
lean_object* v_b_5601_ = _args[5];
lean_object* v___y_5602_ = _args[6];
lean_object* v___y_5603_ = _args[7];
lean_object* v___y_5604_ = _args[8];
lean_object* v___y_5605_ = _args[9];
lean_object* v___y_5606_ = _args[10];
lean_object* v___y_5607_ = _args[11];
lean_object* v___y_5608_ = _args[12];
lean_object* v___y_5609_ = _args[13];
lean_object* v___y_5610_ = _args[14];
lean_object* v___y_5611_ = _args[15];
lean_object* v___y_5612_ = _args[16];
lean_object* v___y_5613_ = _args[17];
lean_object* v___y_5614_ = _args[18];
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5596_, v___x_5597_, v_methods_5598_, v_config_5599_, v_a_5600_, v_b_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
lean_dec(v___y_5611_);
lean_dec_ref(v___y_5610_);
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5608_);
lean_dec(v___y_5607_);
lean_dec_ref(v___y_5606_);
lean_dec(v___y_5605_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___x_5597_);
lean_dec(v_upperBound_5596_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5616_, lean_object* v_config_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_){
_start:
{
lean_object* v___x_5631_; lean_object* v_hypotheses_5632_; lean_object* v___x_5633_; lean_object* v_newHyps_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; 
v___x_5631_ = lean_st_ref_get(v_a_5620_);
v_hypotheses_5632_ = lean_ctor_get(v___x_5631_, 3);
lean_inc_ref(v_hypotheses_5632_);
lean_dec(v___x_5631_);
v___x_5633_ = lean_array_get_size(v_hypotheses_5632_);
v_newHyps_5634_ = lean_mk_empty_array_with_capacity(v___x_5633_);
v___x_5635_ = lean_unsigned_to_nat(0u);
v___x_5636_ = lean_box(0);
v___x_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
lean_ctor_set(v___x_5637_, 1, v_newHyps_5634_);
v___x_5638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5633_, v_hypotheses_5632_, v_methods_5616_, v_config_5617_, v___x_5635_, v___x_5637_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_);
lean_dec_ref(v_hypotheses_5632_);
if (lean_obj_tag(v___x_5638_) == 0)
{
lean_object* v_a_5639_; lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5668_; 
v_a_5639_ = lean_ctor_get(v___x_5638_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v___x_5638_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5641_ = v___x_5638_;
v_isShared_5642_ = v_isSharedCheck_5668_;
goto v_resetjp_5640_;
}
else
{
lean_inc(v_a_5639_);
lean_dec(v___x_5638_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5668_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v_fst_5643_; 
v_fst_5643_ = lean_ctor_get(v_a_5639_, 0);
if (lean_obj_tag(v_fst_5643_) == 0)
{
lean_object* v_snd_5644_; lean_object* v___x_5645_; lean_object* v_caches_5646_; lean_object* v_typeAnalysis_5647_; lean_object* v_target_5648_; uint8_t v_didChange_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5662_; 
v_snd_5644_ = lean_ctor_get(v_a_5639_, 1);
lean_inc(v_snd_5644_);
lean_dec(v_a_5639_);
v___x_5645_ = lean_st_ref_take(v_a_5620_);
v_caches_5646_ = lean_ctor_get(v___x_5645_, 0);
v_typeAnalysis_5647_ = lean_ctor_get(v___x_5645_, 1);
v_target_5648_ = lean_ctor_get(v___x_5645_, 2);
v_didChange_5649_ = lean_ctor_get_uint8(v___x_5645_, sizeof(void*)*4);
v_isSharedCheck_5662_ = !lean_is_exclusive(v___x_5645_);
if (v_isSharedCheck_5662_ == 0)
{
lean_object* v_unused_5663_; 
v_unused_5663_ = lean_ctor_get(v___x_5645_, 3);
lean_dec(v_unused_5663_);
v___x_5651_ = v___x_5645_;
v_isShared_5652_ = v_isSharedCheck_5662_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_target_5648_);
lean_inc(v_typeAnalysis_5647_);
lean_inc(v_caches_5646_);
lean_dec(v___x_5645_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5662_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
lean_object* v___x_5654_; 
if (v_isShared_5652_ == 0)
{
lean_ctor_set(v___x_5651_, 3, v_snd_5644_);
v___x_5654_ = v___x_5651_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_caches_5646_);
lean_ctor_set(v_reuseFailAlloc_5661_, 1, v_typeAnalysis_5647_);
lean_ctor_set(v_reuseFailAlloc_5661_, 2, v_target_5648_);
lean_ctor_set(v_reuseFailAlloc_5661_, 3, v_snd_5644_);
lean_ctor_set_uint8(v_reuseFailAlloc_5661_, sizeof(void*)*4, v_didChange_5649_);
v___x_5654_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
lean_object* v___x_5655_; uint8_t v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5659_; 
v___x_5655_ = lean_st_ref_put(v_a_5620_, v___x_5654_);
v___x_5656_ = 0;
v___x_5657_ = lean_box(v___x_5656_);
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 0, v___x_5657_);
v___x_5659_ = v___x_5641_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v___x_5657_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
return v___x_5659_;
}
}
}
}
else
{
lean_object* v_val_5664_; lean_object* v___x_5666_; 
lean_inc_ref(v_fst_5643_);
lean_dec(v_a_5639_);
v_val_5664_ = lean_ctor_get(v_fst_5643_, 0);
lean_inc(v_val_5664_);
lean_dec_ref_known(v_fst_5643_, 1);
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 0, v_val_5664_);
v___x_5666_ = v___x_5641_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_val_5664_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
else
{
lean_object* v_a_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5676_; 
v_a_5669_ = lean_ctor_get(v___x_5638_, 0);
v_isSharedCheck_5676_ = !lean_is_exclusive(v___x_5638_);
if (v_isSharedCheck_5676_ == 0)
{
v___x_5671_ = v___x_5638_;
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_a_5669_);
lean_dec(v___x_5638_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5677_, lean_object* v_config_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_){
_start:
{
lean_object* v_res_5692_; 
v_res_5692_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5677_, v_config_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_);
lean_dec(v_a_5690_);
lean_dec_ref(v_a_5689_);
lean_dec(v_a_5688_);
lean_dec_ref(v_a_5687_);
lean_dec(v_a_5686_);
lean_dec_ref(v_a_5685_);
lean_dec(v_a_5684_);
lean_dec_ref(v_a_5683_);
lean_dec(v_a_5682_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
lean_dec(v_a_5679_);
return v_res_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5693_, lean_object* v_msg_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
lean_object* v___x_5708_; 
v___x_5708_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5693_, v_msg_5694_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
return v___x_5708_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5709_, lean_object* v_msg_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_){
_start:
{
lean_object* v_res_5724_; 
v_res_5724_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5709_, v_msg_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec(v___y_5713_);
lean_dec_ref(v___y_5712_);
lean_dec(v___y_5711_);
return v_res_5724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5725_, lean_object* v___x_5726_, lean_object* v_methods_5727_, lean_object* v_config_5728_, lean_object* v_inst_5729_, lean_object* v_R_5730_, lean_object* v_a_5731_, lean_object* v_b_5732_, lean_object* v_c_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v___x_5747_; 
v___x_5747_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5725_, v___x_5726_, v_methods_5727_, v_config_5728_, v_a_5731_, v_b_5732_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5748_ = _args[0];
lean_object* v___x_5749_ = _args[1];
lean_object* v_methods_5750_ = _args[2];
lean_object* v_config_5751_ = _args[3];
lean_object* v_inst_5752_ = _args[4];
lean_object* v_R_5753_ = _args[5];
lean_object* v_a_5754_ = _args[6];
lean_object* v_b_5755_ = _args[7];
lean_object* v_c_5756_ = _args[8];
lean_object* v___y_5757_ = _args[9];
lean_object* v___y_5758_ = _args[10];
lean_object* v___y_5759_ = _args[11];
lean_object* v___y_5760_ = _args[12];
lean_object* v___y_5761_ = _args[13];
lean_object* v___y_5762_ = _args[14];
lean_object* v___y_5763_ = _args[15];
lean_object* v___y_5764_ = _args[16];
lean_object* v___y_5765_ = _args[17];
lean_object* v___y_5766_ = _args[18];
lean_object* v___y_5767_ = _args[19];
lean_object* v___y_5768_ = _args[20];
lean_object* v___y_5769_ = _args[21];
_start:
{
lean_object* v_res_5770_; 
v_res_5770_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5748_, v___x_5749_, v_methods_5750_, v_config_5751_, v_inst_5752_, v_R_5753_, v_a_5754_, v_b_5755_, v_c_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
lean_dec(v___y_5766_);
lean_dec_ref(v___y_5765_);
lean_dec(v___y_5764_);
lean_dec_ref(v___y_5763_);
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec(v___y_5759_);
lean_dec_ref(v___y_5758_);
lean_dec(v___y_5757_);
lean_dec_ref(v___x_5749_);
lean_dec(v_upperBound_5748_);
return v_res_5770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5771_, lean_object* v_config_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_){
_start:
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; 
v___x_5785_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5786_ = lean_st_mk_ref(v___x_5785_);
v___x_5787_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5771_, v_config_5772_, v___x_5786_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_);
if (lean_obj_tag(v___x_5787_) == 0)
{
lean_object* v_a_5788_; lean_object* v___x_5790_; uint8_t v_isShared_5791_; uint8_t v_isSharedCheck_5796_; 
v_a_5788_ = lean_ctor_get(v___x_5787_, 0);
v_isSharedCheck_5796_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5790_ = v___x_5787_;
v_isShared_5791_ = v_isSharedCheck_5796_;
goto v_resetjp_5789_;
}
else
{
lean_inc(v_a_5788_);
lean_dec(v___x_5787_);
v___x_5790_ = lean_box(0);
v_isShared_5791_ = v_isSharedCheck_5796_;
goto v_resetjp_5789_;
}
v_resetjp_5789_:
{
lean_object* v___x_5792_; lean_object* v___x_5794_; 
v___x_5792_ = lean_st_ref_get(v___x_5786_);
lean_dec(v___x_5786_);
lean_dec(v___x_5792_);
if (v_isShared_5791_ == 0)
{
v___x_5794_ = v___x_5790_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_a_5788_);
v___x_5794_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
return v___x_5794_;
}
}
}
else
{
lean_dec(v___x_5786_);
return v___x_5787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5797_, lean_object* v_config_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_){
_start:
{
lean_object* v_res_5811_; 
v_res_5811_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5797_, v_config_5798_, v_a_5799_, v_a_5800_, v_a_5801_, v_a_5802_, v_a_5803_, v_a_5804_, v_a_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_);
lean_dec(v_a_5809_);
lean_dec_ref(v_a_5808_);
lean_dec(v_a_5807_);
lean_dec_ref(v_a_5806_);
lean_dec(v_a_5805_);
lean_dec_ref(v_a_5804_);
lean_dec(v_a_5803_);
lean_dec_ref(v_a_5802_);
lean_dec(v_a_5801_);
lean_dec(v_a_5800_);
lean_dec_ref(v_a_5799_);
return v_res_5811_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5813_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5814_ = l_Lean_stringToMessageData(v___x_5813_);
return v___x_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5815_, lean_object* v_x_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_){
_start:
{
lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5829_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5830_ = l_Lean_MessageData_ofName(v_name_5815_);
v___x_5831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5831_, 0, v___x_5829_);
lean_ctor_set(v___x_5831_, 1, v___x_5830_);
v___x_5832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5831_);
return v___x_5832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5833_, lean_object* v_x_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_){
_start:
{
lean_object* v_res_5847_; 
v_res_5847_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5833_, v_x_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_);
lean_dec(v___y_5845_);
lean_dec_ref(v___y_5844_);
lean_dec(v___y_5843_);
lean_dec_ref(v___y_5842_);
lean_dec(v___y_5841_);
lean_dec_ref(v___y_5840_);
lean_dec(v___y_5839_);
lean_dec_ref(v___y_5838_);
lean_dec(v___y_5837_);
lean_dec(v___y_5836_);
lean_dec_ref(v___y_5835_);
lean_dec_ref(v_x_5834_);
return v_res_5847_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5848_; 
v___x_5848_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_5848_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5849_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5850_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5849_);
return v___x_5850_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5852_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5851_);
return v___x_5852_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5853_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5854_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5853_);
return v___x_5854_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5855_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5856_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5855_);
return v___x_5856_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5857_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5858_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5857_);
return v___x_5858_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5859_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5860_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5859_);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5861_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5862_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5861_);
return v___x_5862_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5863_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5864_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5863_);
return v___x_5864_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5866_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5865_);
return v___x_5866_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5867_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5868_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5867_);
return v___x_5868_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5869_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5870_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5869_);
return v___x_5870_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5872_; double v___x_5873_; 
v___x_5872_ = lean_unsigned_to_nat(1000000000u);
v___x_5873_ = lean_float_of_nat(v___x_5872_);
return v___x_5873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5874_, lean_object* v_a_5875_, lean_object* v_a_5876_, lean_object* v_a_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_){
_start:
{
lean_object* v___x_5887_; lean_object* v_toApplicative_5888_; lean_object* v_toFunctor_5889_; lean_object* v_toSeq_5890_; lean_object* v_toSeqLeft_5891_; lean_object* v_toSeqRight_5892_; lean_object* v___f_5893_; lean_object* v___f_5894_; lean_object* v___f_5895_; lean_object* v___f_5896_; lean_object* v___x_5897_; lean_object* v___f_5898_; lean_object* v___f_5899_; lean_object* v___f_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v_toApplicative_5904_; lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_6048_; 
v___x_5887_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5888_ = lean_ctor_get(v___x_5887_, 0);
v_toFunctor_5889_ = lean_ctor_get(v_toApplicative_5888_, 0);
v_toSeq_5890_ = lean_ctor_get(v_toApplicative_5888_, 2);
v_toSeqLeft_5891_ = lean_ctor_get(v_toApplicative_5888_, 3);
v_toSeqRight_5892_ = lean_ctor_get(v_toApplicative_5888_, 4);
v___f_5893_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5894_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5889_, 2);
v___f_5895_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5895_, 0, v_toFunctor_5889_);
v___f_5896_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5896_, 0, v_toFunctor_5889_);
v___x_5897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___f_5895_);
lean_ctor_set(v___x_5897_, 1, v___f_5896_);
lean_inc(v_toSeqRight_5892_);
v___f_5898_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5898_, 0, v_toSeqRight_5892_);
lean_inc(v_toSeqLeft_5891_);
v___f_5899_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5899_, 0, v_toSeqLeft_5891_);
lean_inc(v_toSeq_5890_);
v___f_5900_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5900_, 0, v_toSeq_5890_);
v___x_5901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5897_);
lean_ctor_set(v___x_5901_, 1, v___f_5893_);
lean_ctor_set(v___x_5901_, 2, v___f_5900_);
lean_ctor_set(v___x_5901_, 3, v___f_5899_);
lean_ctor_set(v___x_5901_, 4, v___f_5898_);
v___x_5902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5901_);
lean_ctor_set(v___x_5902_, 1, v___f_5894_);
v___x_5903_ = l_StateRefT_x27_instMonad___redArg(v___x_5902_);
v_toApplicative_5904_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_6048_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_6048_ == 0)
{
lean_object* v_unused_6049_; 
v_unused_6049_ = lean_ctor_get(v___x_5903_, 1);
lean_dec(v_unused_6049_);
v___x_5906_ = v___x_5903_;
v_isShared_5907_ = v_isSharedCheck_6048_;
goto v_resetjp_5905_;
}
else
{
lean_inc(v_toApplicative_5904_);
lean_dec(v___x_5903_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_6048_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v_toFunctor_5908_; lean_object* v_toSeq_5909_; lean_object* v_toSeqLeft_5910_; lean_object* v_toSeqRight_5911_; lean_object* v___x_5913_; uint8_t v_isShared_5914_; uint8_t v_isSharedCheck_6046_; 
v_toFunctor_5908_ = lean_ctor_get(v_toApplicative_5904_, 0);
v_toSeq_5909_ = lean_ctor_get(v_toApplicative_5904_, 2);
v_toSeqLeft_5910_ = lean_ctor_get(v_toApplicative_5904_, 3);
v_toSeqRight_5911_ = lean_ctor_get(v_toApplicative_5904_, 4);
v_isSharedCheck_6046_ = !lean_is_exclusive(v_toApplicative_5904_);
if (v_isSharedCheck_6046_ == 0)
{
lean_object* v_unused_6047_; 
v_unused_6047_ = lean_ctor_get(v_toApplicative_5904_, 1);
lean_dec(v_unused_6047_);
v___x_5913_ = v_toApplicative_5904_;
v_isShared_5914_ = v_isSharedCheck_6046_;
goto v_resetjp_5912_;
}
else
{
lean_inc(v_toSeqRight_5911_);
lean_inc(v_toSeqLeft_5910_);
lean_inc(v_toSeq_5909_);
lean_inc(v_toFunctor_5908_);
lean_dec(v_toApplicative_5904_);
v___x_5913_ = lean_box(0);
v_isShared_5914_ = v_isSharedCheck_6046_;
goto v_resetjp_5912_;
}
v_resetjp_5912_:
{
lean_object* v___f_5915_; lean_object* v___f_5916_; lean_object* v___f_5917_; lean_object* v___f_5918_; lean_object* v___x_5919_; lean_object* v___f_5920_; lean_object* v___f_5921_; lean_object* v___f_5922_; lean_object* v___x_5924_; 
v___f_5915_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5916_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5908_);
v___f_5917_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5917_, 0, v_toFunctor_5908_);
v___f_5918_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5918_, 0, v_toFunctor_5908_);
v___x_5919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___f_5917_);
lean_ctor_set(v___x_5919_, 1, v___f_5918_);
v___f_5920_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5920_, 0, v_toSeqRight_5911_);
v___f_5921_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5921_, 0, v_toSeqLeft_5910_);
v___f_5922_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5922_, 0, v_toSeq_5909_);
if (v_isShared_5914_ == 0)
{
lean_ctor_set(v___x_5913_, 4, v___f_5920_);
lean_ctor_set(v___x_5913_, 3, v___f_5921_);
lean_ctor_set(v___x_5913_, 2, v___f_5922_);
lean_ctor_set(v___x_5913_, 1, v___f_5915_);
lean_ctor_set(v___x_5913_, 0, v___x_5919_);
v___x_5924_ = v___x_5913_;
goto v_reusejp_5923_;
}
else
{
lean_object* v_reuseFailAlloc_6045_; 
v_reuseFailAlloc_6045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6045_, 0, v___x_5919_);
lean_ctor_set(v_reuseFailAlloc_6045_, 1, v___f_5915_);
lean_ctor_set(v_reuseFailAlloc_6045_, 2, v___f_5922_);
lean_ctor_set(v_reuseFailAlloc_6045_, 3, v___f_5921_);
lean_ctor_set(v_reuseFailAlloc_6045_, 4, v___f_5920_);
v___x_5924_ = v_reuseFailAlloc_6045_;
goto v_reusejp_5923_;
}
v_reusejp_5923_:
{
lean_object* v___x_5926_; 
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 1, v___f_5916_);
lean_ctor_set(v___x_5906_, 0, v___x_5924_);
v___x_5926_ = v___x_5906_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_6044_, 1, v___f_5916_);
v___x_5926_ = v_reuseFailAlloc_6044_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v_toMonadRef_5936_; lean_object* v___x_5937_; lean_object* v_options_5938_; uint8_t v_hasTrace_5939_; 
v___x_5927_ = l_StateRefT_x27_instMonad___redArg(v___x_5926_);
v___x_5928_ = l_ReaderT_instMonad___redArg(v___x_5927_);
v___x_5929_ = l_StateRefT_x27_instMonad___redArg(v___x_5928_);
v___x_5930_ = l_ReaderT_instMonad___redArg(v___x_5929_);
v___x_5931_ = l_ReaderT_instMonad___redArg(v___x_5930_);
v___x_5932_ = l_StateRefT_x27_instMonad___redArg(v___x_5931_);
v___x_5933_ = l_ReaderT_instMonad___redArg(v___x_5932_);
v___x_5934_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5935_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_5936_ = lean_ctor_get(v___x_5935_, 0);
v___x_5937_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_options_5938_ = lean_ctor_get(v_a_5884_, 2);
v_hasTrace_5939_ = lean_ctor_get_uint8(v_options_5938_, sizeof(void*)*1);
if (v_hasTrace_5939_ == 0)
{
lean_object* v_run_x27_5940_; lean_object* v___x_5941_; 
lean_dec_ref(v___x_5933_);
v_run_x27_5940_ = lean_ctor_get(v_pass_5874_, 1);
lean_inc_ref(v_run_x27_5940_);
lean_dec_ref(v_pass_5874_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc_ref(v_a_5878_);
lean_inc(v_a_5877_);
lean_inc(v_a_5876_);
lean_inc_ref(v_a_5875_);
v___x_5941_ = lean_apply_12(v_run_x27_5940_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, lean_box(0));
return v___x_5941_;
}
else
{
lean_object* v_name_5942_; lean_object* v_run_x27_5943_; lean_object* v___x_5945_; uint8_t v_isShared_5946_; uint8_t v_isSharedCheck_6043_; 
v_name_5942_ = lean_ctor_get(v_pass_5874_, 0);
v_run_x27_5943_ = lean_ctor_get(v_pass_5874_, 1);
v_isSharedCheck_6043_ = !lean_is_exclusive(v_pass_5874_);
if (v_isSharedCheck_6043_ == 0)
{
v___x_5945_ = v_pass_5874_;
v_isShared_5946_ = v_isSharedCheck_6043_;
goto v_resetjp_5944_;
}
else
{
lean_inc(v_run_x27_5943_);
lean_inc(v_name_5942_);
lean_dec(v_pass_5874_);
v___x_5945_ = lean_box(0);
v_isShared_5946_ = v_isSharedCheck_6043_;
goto v_resetjp_5944_;
}
v_resetjp_5944_:
{
lean_object* v_inheritedTraceOptions_5947_; lean_object* v___f_5948_; lean_object* v___f_5949_; lean_object* v___f_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; uint8_t v___x_5954_; lean_object* v___y_5956_; lean_object* v___y_5957_; lean_object* v_a_5958_; lean_object* v___y_5974_; lean_object* v___y_5975_; lean_object* v_a_5976_; 
v_inheritedTraceOptions_5947_ = lean_ctor_get(v_a_5884_, 13);
v___f_5948_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5948_, 0, v_name_5942_);
v___f_5949_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_5950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5951_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_5952_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5953_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_5954_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5947_, v_options_5938_, v___x_5953_);
if (v___x_5954_ == 0)
{
lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; uint8_t v___x_6041_; 
v___x_6038_ = l_Lean_KVMap_instValueBool;
v___x_6039_ = l_Lean_trace_profiler;
v___x_6040_ = l_Lean_Option_get___redArg(v___x_6038_, v_options_5938_, v___x_6039_);
v___x_6041_ = lean_unbox(v___x_6040_);
lean_dec(v___x_6040_);
if (v___x_6041_ == 0)
{
lean_object* v___x_6042_; 
lean_dec_ref(v___f_5948_);
lean_del_object(v___x_5945_);
lean_dec_ref(v___x_5933_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc_ref(v_a_5878_);
lean_inc(v_a_5877_);
lean_inc(v_a_5876_);
lean_inc_ref(v_a_5875_);
v___x_6042_ = lean_apply_12(v_run_x27_5943_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, lean_box(0));
return v___x_6042_;
}
else
{
goto v___jp_5986_;
}
}
else
{
goto v___jp_5986_;
}
v___jp_5955_:
{
lean_object* v___x_5959_; double v___x_5960_; double v___x_5961_; double v___x_5962_; double v___x_5963_; double v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5968_; 
v___x_5959_ = lean_io_mono_nanos_now();
v___x_5960_ = lean_float_of_nat(v___y_5956_);
v___x_5961_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5962_ = lean_float_div(v___x_5960_, v___x_5961_);
v___x_5963_ = lean_float_of_nat(v___x_5959_);
v___x_5964_ = lean_float_div(v___x_5963_, v___x_5961_);
v___x_5965_ = lean_box_float(v___x_5962_);
v___x_5966_ = lean_box_float(v___x_5964_);
if (v_isShared_5946_ == 0)
{
lean_ctor_set(v___x_5945_, 1, v___x_5966_);
lean_ctor_set(v___x_5945_, 0, v___x_5965_);
v___x_5968_ = v___x_5945_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5965_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___x_5966_);
v___x_5968_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
lean_object* v___x_5969_; lean_object* v___x_29258__overap_5970_; lean_object* v___x_5971_; 
v___x_5969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5969_, 0, v_a_5958_);
lean_ctor_set(v___x_5969_, 1, v___x_5968_);
lean_inc_ref(v_toMonadRef_5936_);
v___x_29258__overap_5970_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5933_, v___x_5934_, v_toMonadRef_5936_, v___f_5949_, lean_box(0), v___x_5937_, v___f_5950_, v___x_5951_, v_hasTrace_5939_, v___x_5952_, v_options_5938_, v___x_5954_, v___y_5957_, v___f_5948_, v___x_5969_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc_ref(v_a_5878_);
lean_inc(v_a_5877_);
lean_inc(v_a_5876_);
lean_inc_ref(v_a_5875_);
v___x_5971_ = lean_apply_12(v___x_29258__overap_5970_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, lean_box(0));
return v___x_5971_;
}
}
v___jp_5973_:
{
lean_object* v___x_5977_; double v___x_5978_; double v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_29279__overap_5984_; lean_object* v___x_5985_; 
v___x_5977_ = lean_io_get_num_heartbeats();
v___x_5978_ = lean_float_of_nat(v___y_5974_);
v___x_5979_ = lean_float_of_nat(v___x_5977_);
v___x_5980_ = lean_box_float(v___x_5978_);
v___x_5981_ = lean_box_float(v___x_5979_);
v___x_5982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5980_);
lean_ctor_set(v___x_5982_, 1, v___x_5981_);
v___x_5983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5983_, 0, v_a_5976_);
lean_ctor_set(v___x_5983_, 1, v___x_5982_);
lean_inc_ref(v_toMonadRef_5936_);
v___x_29279__overap_5984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5933_, v___x_5934_, v_toMonadRef_5936_, v___f_5949_, lean_box(0), v___x_5937_, v___f_5950_, v___x_5951_, v_hasTrace_5939_, v___x_5952_, v_options_5938_, v___x_5954_, v___y_5975_, v___f_5948_, v___x_5983_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc_ref(v_a_5878_);
lean_inc(v_a_5877_);
lean_inc(v_a_5876_);
lean_inc_ref(v_a_5875_);
v___x_5985_ = lean_apply_12(v___x_29279__overap_5984_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, lean_box(0));
return v___x_5985_;
}
v___jp_5986_:
{
lean_object* v___x_29235__overap_5987_; lean_object* v___x_5988_; 
lean_inc_ref(v___x_5933_);
v___x_29235__overap_5987_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5933_, v___x_5934_);
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc_ref(v_a_5878_);
lean_inc(v_a_5877_);
lean_inc(v_a_5876_);
lean_inc_ref(v_a_5875_);
v___x_5988_ = lean_apply_12(v___x_29235__overap_5987_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, lean_box(0));
if (lean_obj_tag(v___x_5988_) == 0)
{
lean_object* v_a_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; uint8_t v___x_5993_; 
v_a_5989_ = lean_ctor_get(v___x_5988_, 0);
lean_inc(v_a_5989_);
lean_dec_ref_known(v___x_5988_, 1);
v___x_5990_ = l_Lean_KVMap_instValueBool;
v___x_5991_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5992_ = l_Lean_Option_get___redArg(v___x_5990_, v_options_5938_, v___x_5991_);
v___x_5993_ = lean_unbox(v___x_5992_);
lean_dec(v___x_5992_);
if (v___x_5993_ == 0)
{
lean_object* v___x_5994_; lean_object* v___x_5995_; 
v___x_5994_ = lean_io_mono_nanos_now();
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc_ref(v_a_5878_);
lean_inc(v_a_5877_);
lean_inc(v_a_5876_);
lean_inc_ref(v_a_5875_);
v___x_5995_ = lean_apply_12(v_run_x27_5943_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, lean_box(0));
if (lean_obj_tag(v___x_5995_) == 0)
{
lean_object* v_a_5996_; lean_object* v___x_5998_; uint8_t v_isShared_5999_; uint8_t v_isSharedCheck_6003_; 
v_a_5996_ = lean_ctor_get(v___x_5995_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v___x_5995_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5998_ = v___x_5995_;
v_isShared_5999_ = v_isSharedCheck_6003_;
goto v_resetjp_5997_;
}
else
{
lean_inc(v_a_5996_);
lean_dec(v___x_5995_);
v___x_5998_ = lean_box(0);
v_isShared_5999_ = v_isSharedCheck_6003_;
goto v_resetjp_5997_;
}
v_resetjp_5997_:
{
lean_object* v___x_6001_; 
if (v_isShared_5999_ == 0)
{
lean_ctor_set_tag(v___x_5998_, 1);
v___x_6001_ = v___x_5998_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v_a_5996_);
v___x_6001_ = v_reuseFailAlloc_6002_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
v___y_5956_ = v___x_5994_;
v___y_5957_ = v_a_5989_;
v_a_5958_ = v___x_6001_;
goto v___jp_5955_;
}
}
}
else
{
lean_object* v_a_6004_; lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6011_; 
v_a_6004_ = lean_ctor_get(v___x_5995_, 0);
v_isSharedCheck_6011_ = !lean_is_exclusive(v___x_5995_);
if (v_isSharedCheck_6011_ == 0)
{
v___x_6006_ = v___x_5995_;
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_a_6004_);
lean_dec(v___x_5995_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v___x_6009_; 
if (v_isShared_6007_ == 0)
{
lean_ctor_set_tag(v___x_6006_, 0);
v___x_6009_ = v___x_6006_;
goto v_reusejp_6008_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
v___x_6009_ = v_reuseFailAlloc_6010_;
goto v_reusejp_6008_;
}
v_reusejp_6008_:
{
v___y_5956_ = v___x_5994_;
v___y_5957_ = v_a_5989_;
v_a_5958_ = v___x_6009_;
goto v___jp_5955_;
}
}
}
}
else
{
lean_object* v___x_6012_; lean_object* v___x_6013_; 
lean_del_object(v___x_5945_);
v___x_6012_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5885_);
lean_inc_ref(v_a_5884_);
lean_inc(v_a_5883_);
lean_inc_ref(v_a_5882_);
lean_inc(v_a_5881_);
lean_inc_ref(v_a_5880_);
lean_inc(v_a_5879_);
lean_inc_ref(v_a_5878_);
lean_inc(v_a_5877_);
lean_inc(v_a_5876_);
lean_inc_ref(v_a_5875_);
v___x_6013_ = lean_apply_12(v_run_x27_5943_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, lean_box(0));
if (lean_obj_tag(v___x_6013_) == 0)
{
lean_object* v_a_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6021_; 
v_a_6014_ = lean_ctor_get(v___x_6013_, 0);
v_isSharedCheck_6021_ = !lean_is_exclusive(v___x_6013_);
if (v_isSharedCheck_6021_ == 0)
{
v___x_6016_ = v___x_6013_;
v_isShared_6017_ = v_isSharedCheck_6021_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_a_6014_);
lean_dec(v___x_6013_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6021_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v___x_6019_; 
if (v_isShared_6017_ == 0)
{
lean_ctor_set_tag(v___x_6016_, 1);
v___x_6019_ = v___x_6016_;
goto v_reusejp_6018_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_a_6014_);
v___x_6019_ = v_reuseFailAlloc_6020_;
goto v_reusejp_6018_;
}
v_reusejp_6018_:
{
v___y_5974_ = v___x_6012_;
v___y_5975_ = v_a_5989_;
v_a_5976_ = v___x_6019_;
goto v___jp_5973_;
}
}
}
else
{
lean_object* v_a_6022_; lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6029_; 
v_a_6022_ = lean_ctor_get(v___x_6013_, 0);
v_isSharedCheck_6029_ = !lean_is_exclusive(v___x_6013_);
if (v_isSharedCheck_6029_ == 0)
{
v___x_6024_ = v___x_6013_;
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
else
{
lean_inc(v_a_6022_);
lean_dec(v___x_6013_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6027_; 
if (v_isShared_6025_ == 0)
{
lean_ctor_set_tag(v___x_6024_, 0);
v___x_6027_ = v___x_6024_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6028_; 
v_reuseFailAlloc_6028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
v___x_6027_ = v_reuseFailAlloc_6028_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
v___y_5974_ = v___x_6012_;
v___y_5975_ = v_a_5989_;
v_a_5976_ = v___x_6027_;
goto v___jp_5973_;
}
}
}
}
}
else
{
lean_object* v_a_6030_; lean_object* v___x_6032_; uint8_t v_isShared_6033_; uint8_t v_isSharedCheck_6037_; 
lean_dec_ref(v___f_5948_);
lean_del_object(v___x_5945_);
lean_dec_ref(v_run_x27_5943_);
lean_dec_ref(v___x_5933_);
v_a_6030_ = lean_ctor_get(v___x_5988_, 0);
v_isSharedCheck_6037_ = !lean_is_exclusive(v___x_5988_);
if (v_isSharedCheck_6037_ == 0)
{
v___x_6032_ = v___x_5988_;
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
else
{
lean_inc(v_a_6030_);
lean_dec(v___x_5988_);
v___x_6032_ = lean_box(0);
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
v_resetjp_6031_:
{
lean_object* v___x_6035_; 
if (v_isShared_6033_ == 0)
{
v___x_6035_ = v___x_6032_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_a_6030_);
v___x_6035_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
return v___x_6035_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_){
_start:
{
lean_object* v_res_6063_; 
v_res_6063_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6050_, v_a_6051_, v_a_6052_, v_a_6053_, v_a_6054_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_, v_a_6059_, v_a_6060_, v_a_6061_);
lean_dec(v_a_6061_);
lean_dec_ref(v_a_6060_);
lean_dec(v_a_6059_);
lean_dec_ref(v_a_6058_);
lean_dec(v_a_6057_);
lean_dec_ref(v_a_6056_);
lean_dec(v_a_6055_);
lean_dec_ref(v_a_6054_);
lean_dec(v_a_6053_);
lean_dec(v_a_6052_);
lean_dec_ref(v_a_6051_);
return v_res_6063_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; 
v___x_6064_ = lean_unsigned_to_nat(32u);
v___x_6065_ = lean_mk_empty_array_with_capacity(v___x_6064_);
v___x_6066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
return v___x_6066_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6067_ = ((size_t)5ULL);
v___x_6068_ = lean_unsigned_to_nat(0u);
v___x_6069_ = lean_unsigned_to_nat(32u);
v___x_6070_ = lean_mk_empty_array_with_capacity(v___x_6069_);
v___x_6071_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6072_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
lean_ctor_set(v___x_6072_, 1, v___x_6070_);
lean_ctor_set(v___x_6072_, 2, v___x_6068_);
lean_ctor_set(v___x_6072_, 3, v___x_6068_);
lean_ctor_set_usize(v___x_6072_, 4, v___x_6067_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6073_){
_start:
{
lean_object* v___x_6075_; lean_object* v_traceState_6076_; lean_object* v_traces_6077_; lean_object* v___x_6078_; lean_object* v_traceState_6079_; lean_object* v_env_6080_; lean_object* v_nextMacroScope_6081_; lean_object* v_ngen_6082_; lean_object* v_auxDeclNGen_6083_; lean_object* v_cache_6084_; lean_object* v_messages_6085_; lean_object* v_infoState_6086_; lean_object* v_snapshotTasks_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6106_; 
v___x_6075_ = lean_st_ref_get(v___y_6073_);
v_traceState_6076_ = lean_ctor_get(v___x_6075_, 4);
lean_inc_ref(v_traceState_6076_);
lean_dec(v___x_6075_);
v_traces_6077_ = lean_ctor_get(v_traceState_6076_, 0);
lean_inc_ref(v_traces_6077_);
lean_dec_ref(v_traceState_6076_);
v___x_6078_ = lean_st_ref_take(v___y_6073_);
v_traceState_6079_ = lean_ctor_get(v___x_6078_, 4);
v_env_6080_ = lean_ctor_get(v___x_6078_, 0);
v_nextMacroScope_6081_ = lean_ctor_get(v___x_6078_, 1);
v_ngen_6082_ = lean_ctor_get(v___x_6078_, 2);
v_auxDeclNGen_6083_ = lean_ctor_get(v___x_6078_, 3);
v_cache_6084_ = lean_ctor_get(v___x_6078_, 5);
v_messages_6085_ = lean_ctor_get(v___x_6078_, 6);
v_infoState_6086_ = lean_ctor_get(v___x_6078_, 7);
v_snapshotTasks_6087_ = lean_ctor_get(v___x_6078_, 8);
v_isSharedCheck_6106_ = !lean_is_exclusive(v___x_6078_);
if (v_isSharedCheck_6106_ == 0)
{
v___x_6089_ = v___x_6078_;
v_isShared_6090_ = v_isSharedCheck_6106_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_snapshotTasks_6087_);
lean_inc(v_infoState_6086_);
lean_inc(v_messages_6085_);
lean_inc(v_cache_6084_);
lean_inc(v_traceState_6079_);
lean_inc(v_auxDeclNGen_6083_);
lean_inc(v_ngen_6082_);
lean_inc(v_nextMacroScope_6081_);
lean_inc(v_env_6080_);
lean_dec(v___x_6078_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6106_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
uint64_t v_tid_6091_; lean_object* v___x_6093_; uint8_t v_isShared_6094_; uint8_t v_isSharedCheck_6104_; 
v_tid_6091_ = lean_ctor_get_uint64(v_traceState_6079_, sizeof(void*)*1);
v_isSharedCheck_6104_ = !lean_is_exclusive(v_traceState_6079_);
if (v_isSharedCheck_6104_ == 0)
{
lean_object* v_unused_6105_; 
v_unused_6105_ = lean_ctor_get(v_traceState_6079_, 0);
lean_dec(v_unused_6105_);
v___x_6093_ = v_traceState_6079_;
v_isShared_6094_ = v_isSharedCheck_6104_;
goto v_resetjp_6092_;
}
else
{
lean_dec(v_traceState_6079_);
v___x_6093_ = lean_box(0);
v_isShared_6094_ = v_isSharedCheck_6104_;
goto v_resetjp_6092_;
}
v_resetjp_6092_:
{
lean_object* v___x_6095_; lean_object* v___x_6097_; 
v___x_6095_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6094_ == 0)
{
lean_ctor_set(v___x_6093_, 0, v___x_6095_);
v___x_6097_ = v___x_6093_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6103_; 
v_reuseFailAlloc_6103_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6103_, 0, v___x_6095_);
lean_ctor_set_uint64(v_reuseFailAlloc_6103_, sizeof(void*)*1, v_tid_6091_);
v___x_6097_ = v_reuseFailAlloc_6103_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
lean_object* v___x_6099_; 
if (v_isShared_6090_ == 0)
{
lean_ctor_set(v___x_6089_, 4, v___x_6097_);
v___x_6099_ = v___x_6089_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6102_; 
v_reuseFailAlloc_6102_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_env_6080_);
lean_ctor_set(v_reuseFailAlloc_6102_, 1, v_nextMacroScope_6081_);
lean_ctor_set(v_reuseFailAlloc_6102_, 2, v_ngen_6082_);
lean_ctor_set(v_reuseFailAlloc_6102_, 3, v_auxDeclNGen_6083_);
lean_ctor_set(v_reuseFailAlloc_6102_, 4, v___x_6097_);
lean_ctor_set(v_reuseFailAlloc_6102_, 5, v_cache_6084_);
lean_ctor_set(v_reuseFailAlloc_6102_, 6, v_messages_6085_);
lean_ctor_set(v_reuseFailAlloc_6102_, 7, v_infoState_6086_);
lean_ctor_set(v_reuseFailAlloc_6102_, 8, v_snapshotTasks_6087_);
v___x_6099_ = v_reuseFailAlloc_6102_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; 
v___x_6100_ = lean_st_ref_put(v___y_6073_, v___x_6099_);
v___x_6101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6101_, 0, v_traces_6077_);
return v___x_6101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6107_, lean_object* v___y_6108_){
_start:
{
lean_object* v_res_6109_; 
v_res_6109_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6107_);
lean_dec(v___y_6107_);
return v_res_6109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_){
_start:
{
lean_object* v___x_6122_; 
v___x_6122_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6120_);
return v___x_6122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_){
_start:
{
lean_object* v_res_6135_; 
v_res_6135_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
lean_dec(v___y_6131_);
lean_dec_ref(v___y_6130_);
lean_dec(v___y_6129_);
lean_dec_ref(v___y_6128_);
lean_dec(v___y_6127_);
lean_dec_ref(v___y_6126_);
lean_dec(v___y_6125_);
lean_dec(v___y_6124_);
lean_dec_ref(v___y_6123_);
return v_res_6135_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6136_, lean_object* v_opt_6137_){
_start:
{
lean_object* v_name_6138_; lean_object* v_defValue_6139_; lean_object* v_map_6140_; lean_object* v___x_6141_; 
v_name_6138_ = lean_ctor_get(v_opt_6137_, 0);
v_defValue_6139_ = lean_ctor_get(v_opt_6137_, 1);
v_map_6140_ = lean_ctor_get(v_opts_6136_, 0);
v___x_6141_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6140_, v_name_6138_);
if (lean_obj_tag(v___x_6141_) == 0)
{
uint8_t v___x_6142_; 
v___x_6142_ = lean_unbox(v_defValue_6139_);
return v___x_6142_;
}
else
{
lean_object* v_val_6143_; 
v_val_6143_ = lean_ctor_get(v___x_6141_, 0);
lean_inc(v_val_6143_);
lean_dec_ref_known(v___x_6141_, 1);
if (lean_obj_tag(v_val_6143_) == 1)
{
uint8_t v_v_6144_; 
v_v_6144_ = lean_ctor_get_uint8(v_val_6143_, 0);
lean_dec_ref_known(v_val_6143_, 0);
return v_v_6144_;
}
else
{
uint8_t v___x_6145_; 
lean_dec(v_val_6143_);
v___x_6145_ = lean_unbox(v_defValue_6139_);
return v___x_6145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6146_, lean_object* v_opt_6147_){
_start:
{
uint8_t v_res_6148_; lean_object* v_r_6149_; 
v_res_6148_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6146_, v_opt_6147_);
lean_dec_ref(v_opt_6147_);
lean_dec_ref(v_opts_6146_);
v_r_6149_ = lean_box(v_res_6148_);
return v_r_6149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6150_, lean_object* v_msg_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_){
_start:
{
lean_object* v_ref_6157_; lean_object* v___x_6158_; lean_object* v_a_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6203_; 
v_ref_6157_ = lean_ctor_get(v___y_6154_, 5);
v___x_6158_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_);
v_a_6159_ = lean_ctor_get(v___x_6158_, 0);
v_isSharedCheck_6203_ = !lean_is_exclusive(v___x_6158_);
if (v_isSharedCheck_6203_ == 0)
{
v___x_6161_ = v___x_6158_;
v_isShared_6162_ = v_isSharedCheck_6203_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_a_6159_);
lean_dec(v___x_6158_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6203_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
lean_object* v___x_6163_; lean_object* v_traceState_6164_; lean_object* v_env_6165_; lean_object* v_nextMacroScope_6166_; lean_object* v_ngen_6167_; lean_object* v_auxDeclNGen_6168_; lean_object* v_cache_6169_; lean_object* v_messages_6170_; lean_object* v_infoState_6171_; lean_object* v_snapshotTasks_6172_; lean_object* v___x_6174_; uint8_t v_isShared_6175_; uint8_t v_isSharedCheck_6202_; 
v___x_6163_ = lean_st_ref_take(v___y_6155_);
v_traceState_6164_ = lean_ctor_get(v___x_6163_, 4);
v_env_6165_ = lean_ctor_get(v___x_6163_, 0);
v_nextMacroScope_6166_ = lean_ctor_get(v___x_6163_, 1);
v_ngen_6167_ = lean_ctor_get(v___x_6163_, 2);
v_auxDeclNGen_6168_ = lean_ctor_get(v___x_6163_, 3);
v_cache_6169_ = lean_ctor_get(v___x_6163_, 5);
v_messages_6170_ = lean_ctor_get(v___x_6163_, 6);
v_infoState_6171_ = lean_ctor_get(v___x_6163_, 7);
v_snapshotTasks_6172_ = lean_ctor_get(v___x_6163_, 8);
v_isSharedCheck_6202_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6202_ == 0)
{
v___x_6174_ = v___x_6163_;
v_isShared_6175_ = v_isSharedCheck_6202_;
goto v_resetjp_6173_;
}
else
{
lean_inc(v_snapshotTasks_6172_);
lean_inc(v_infoState_6171_);
lean_inc(v_messages_6170_);
lean_inc(v_cache_6169_);
lean_inc(v_traceState_6164_);
lean_inc(v_auxDeclNGen_6168_);
lean_inc(v_ngen_6167_);
lean_inc(v_nextMacroScope_6166_);
lean_inc(v_env_6165_);
lean_dec(v___x_6163_);
v___x_6174_ = lean_box(0);
v_isShared_6175_ = v_isSharedCheck_6202_;
goto v_resetjp_6173_;
}
v_resetjp_6173_:
{
uint64_t v_tid_6176_; lean_object* v_traces_6177_; lean_object* v___x_6179_; uint8_t v_isShared_6180_; uint8_t v_isSharedCheck_6201_; 
v_tid_6176_ = lean_ctor_get_uint64(v_traceState_6164_, sizeof(void*)*1);
v_traces_6177_ = lean_ctor_get(v_traceState_6164_, 0);
v_isSharedCheck_6201_ = !lean_is_exclusive(v_traceState_6164_);
if (v_isSharedCheck_6201_ == 0)
{
v___x_6179_ = v_traceState_6164_;
v_isShared_6180_ = v_isSharedCheck_6201_;
goto v_resetjp_6178_;
}
else
{
lean_inc(v_traces_6177_);
lean_dec(v_traceState_6164_);
v___x_6179_ = lean_box(0);
v_isShared_6180_ = v_isSharedCheck_6201_;
goto v_resetjp_6178_;
}
v_resetjp_6178_:
{
lean_object* v___x_6181_; double v___x_6182_; uint8_t v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6191_; 
v___x_6181_ = lean_box(0);
v___x_6182_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6183_ = 0;
v___x_6184_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6185_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6185_, 0, v_cls_6150_);
lean_ctor_set(v___x_6185_, 1, v___x_6181_);
lean_ctor_set(v___x_6185_, 2, v___x_6184_);
lean_ctor_set_float(v___x_6185_, sizeof(void*)*3, v___x_6182_);
lean_ctor_set_float(v___x_6185_, sizeof(void*)*3 + 8, v___x_6182_);
lean_ctor_set_uint8(v___x_6185_, sizeof(void*)*3 + 16, v___x_6183_);
v___x_6186_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6187_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6185_);
lean_ctor_set(v___x_6187_, 1, v_a_6159_);
lean_ctor_set(v___x_6187_, 2, v___x_6186_);
lean_inc(v_ref_6157_);
v___x_6188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6188_, 0, v_ref_6157_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = l_Lean_PersistentArray_push___redArg(v_traces_6177_, v___x_6188_);
if (v_isShared_6180_ == 0)
{
lean_ctor_set(v___x_6179_, 0, v___x_6189_);
v___x_6191_ = v___x_6179_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6200_; 
v_reuseFailAlloc_6200_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6200_, 0, v___x_6189_);
lean_ctor_set_uint64(v_reuseFailAlloc_6200_, sizeof(void*)*1, v_tid_6176_);
v___x_6191_ = v_reuseFailAlloc_6200_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
lean_object* v___x_6193_; 
if (v_isShared_6175_ == 0)
{
lean_ctor_set(v___x_6174_, 4, v___x_6191_);
v___x_6193_ = v___x_6174_;
goto v_reusejp_6192_;
}
else
{
lean_object* v_reuseFailAlloc_6199_; 
v_reuseFailAlloc_6199_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6199_, 0, v_env_6165_);
lean_ctor_set(v_reuseFailAlloc_6199_, 1, v_nextMacroScope_6166_);
lean_ctor_set(v_reuseFailAlloc_6199_, 2, v_ngen_6167_);
lean_ctor_set(v_reuseFailAlloc_6199_, 3, v_auxDeclNGen_6168_);
lean_ctor_set(v_reuseFailAlloc_6199_, 4, v___x_6191_);
lean_ctor_set(v_reuseFailAlloc_6199_, 5, v_cache_6169_);
lean_ctor_set(v_reuseFailAlloc_6199_, 6, v_messages_6170_);
lean_ctor_set(v_reuseFailAlloc_6199_, 7, v_infoState_6171_);
lean_ctor_set(v_reuseFailAlloc_6199_, 8, v_snapshotTasks_6172_);
v___x_6193_ = v_reuseFailAlloc_6199_;
goto v_reusejp_6192_;
}
v_reusejp_6192_:
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6197_; 
v___x_6194_ = lean_st_ref_put(v___y_6155_, v___x_6193_);
v___x_6195_ = lean_box(0);
if (v_isShared_6162_ == 0)
{
lean_ctor_set(v___x_6161_, 0, v___x_6195_);
v___x_6197_ = v___x_6161_;
goto v_reusejp_6196_;
}
else
{
lean_object* v_reuseFailAlloc_6198_; 
v_reuseFailAlloc_6198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6198_, 0, v___x_6195_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6204_, lean_object* v_msg_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_){
_start:
{
lean_object* v_res_6211_; 
v_res_6211_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6204_, v_msg_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_);
lean_dec(v___y_6209_);
lean_dec_ref(v___y_6208_);
lean_dec(v___y_6207_);
lean_dec_ref(v___y_6206_);
return v_res_6211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6212_){
_start:
{
if (lean_obj_tag(v_e_6212_) == 0)
{
uint8_t v___x_6213_; 
v___x_6213_ = 2;
return v___x_6213_;
}
else
{
lean_object* v_a_6214_; uint8_t v___x_6215_; 
v_a_6214_ = lean_ctor_get(v_e_6212_, 0);
v___x_6215_ = lean_unbox(v_a_6214_);
if (v___x_6215_ == 0)
{
uint8_t v___x_6216_; 
v___x_6216_ = 1;
return v___x_6216_;
}
else
{
uint8_t v___x_6217_; 
v___x_6217_ = 0;
return v___x_6217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6218_){
_start:
{
uint8_t v_res_6219_; lean_object* v_r_6220_; 
v_res_6219_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6218_);
lean_dec_ref(v_e_6218_);
v_r_6220_ = lean_box(v_res_6219_);
return v_r_6220_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6221_){
_start:
{
if (lean_obj_tag(v_x_6221_) == 0)
{
lean_object* v_a_6223_; lean_object* v___x_6225_; uint8_t v_isShared_6226_; uint8_t v_isSharedCheck_6230_; 
v_a_6223_ = lean_ctor_get(v_x_6221_, 0);
v_isSharedCheck_6230_ = !lean_is_exclusive(v_x_6221_);
if (v_isSharedCheck_6230_ == 0)
{
v___x_6225_ = v_x_6221_;
v_isShared_6226_ = v_isSharedCheck_6230_;
goto v_resetjp_6224_;
}
else
{
lean_inc(v_a_6223_);
lean_dec(v_x_6221_);
v___x_6225_ = lean_box(0);
v_isShared_6226_ = v_isSharedCheck_6230_;
goto v_resetjp_6224_;
}
v_resetjp_6224_:
{
lean_object* v___x_6228_; 
if (v_isShared_6226_ == 0)
{
lean_ctor_set_tag(v___x_6225_, 1);
v___x_6228_ = v___x_6225_;
goto v_reusejp_6227_;
}
else
{
lean_object* v_reuseFailAlloc_6229_; 
v_reuseFailAlloc_6229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6229_, 0, v_a_6223_);
v___x_6228_ = v_reuseFailAlloc_6229_;
goto v_reusejp_6227_;
}
v_reusejp_6227_:
{
return v___x_6228_;
}
}
}
else
{
lean_object* v_a_6231_; lean_object* v___x_6233_; uint8_t v_isShared_6234_; uint8_t v_isSharedCheck_6238_; 
v_a_6231_ = lean_ctor_get(v_x_6221_, 0);
v_isSharedCheck_6238_ = !lean_is_exclusive(v_x_6221_);
if (v_isSharedCheck_6238_ == 0)
{
v___x_6233_ = v_x_6221_;
v_isShared_6234_ = v_isSharedCheck_6238_;
goto v_resetjp_6232_;
}
else
{
lean_inc(v_a_6231_);
lean_dec(v_x_6221_);
v___x_6233_ = lean_box(0);
v_isShared_6234_ = v_isSharedCheck_6238_;
goto v_resetjp_6232_;
}
v_resetjp_6232_:
{
lean_object* v___x_6236_; 
if (v_isShared_6234_ == 0)
{
lean_ctor_set_tag(v___x_6233_, 0);
v___x_6236_ = v___x_6233_;
goto v_reusejp_6235_;
}
else
{
lean_object* v_reuseFailAlloc_6237_; 
v_reuseFailAlloc_6237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6237_, 0, v_a_6231_);
v___x_6236_ = v_reuseFailAlloc_6237_;
goto v_reusejp_6235_;
}
v_reusejp_6235_:
{
return v___x_6236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6239_, lean_object* v___y_6240_){
_start:
{
lean_object* v_res_6241_; 
v_res_6241_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6239_);
return v_res_6241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6242_, lean_object* v_opt_6243_){
_start:
{
lean_object* v_name_6244_; lean_object* v_defValue_6245_; lean_object* v_map_6246_; lean_object* v___x_6247_; 
v_name_6244_ = lean_ctor_get(v_opt_6243_, 0);
v_defValue_6245_ = lean_ctor_get(v_opt_6243_, 1);
v_map_6246_ = lean_ctor_get(v_opts_6242_, 0);
v___x_6247_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6246_, v_name_6244_);
if (lean_obj_tag(v___x_6247_) == 0)
{
lean_inc(v_defValue_6245_);
return v_defValue_6245_;
}
else
{
lean_object* v_val_6248_; 
v_val_6248_ = lean_ctor_get(v___x_6247_, 0);
lean_inc(v_val_6248_);
lean_dec_ref_known(v___x_6247_, 1);
if (lean_obj_tag(v_val_6248_) == 3)
{
lean_object* v_v_6249_; 
v_v_6249_ = lean_ctor_get(v_val_6248_, 0);
lean_inc(v_v_6249_);
lean_dec_ref_known(v_val_6248_, 1);
return v_v_6249_;
}
else
{
lean_dec(v_val_6248_);
lean_inc(v_defValue_6245_);
return v_defValue_6245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6250_, lean_object* v_opt_6251_){
_start:
{
lean_object* v_res_6252_; 
v_res_6252_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6250_, v_opt_6251_);
lean_dec_ref(v_opt_6251_);
lean_dec_ref(v_opts_6250_);
return v_res_6252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6253_, size_t v_i_6254_, lean_object* v_bs_6255_){
_start:
{
uint8_t v___x_6256_; 
v___x_6256_ = lean_usize_dec_lt(v_i_6254_, v_sz_6253_);
if (v___x_6256_ == 0)
{
return v_bs_6255_;
}
else
{
lean_object* v_v_6257_; lean_object* v_msg_6258_; lean_object* v___x_6259_; lean_object* v_bs_x27_6260_; size_t v___x_6261_; size_t v___x_6262_; lean_object* v___x_6263_; 
v_v_6257_ = lean_array_uget_borrowed(v_bs_6255_, v_i_6254_);
v_msg_6258_ = lean_ctor_get(v_v_6257_, 1);
lean_inc_ref(v_msg_6258_);
v___x_6259_ = lean_unsigned_to_nat(0u);
v_bs_x27_6260_ = lean_array_uset(v_bs_6255_, v_i_6254_, v___x_6259_);
v___x_6261_ = ((size_t)1ULL);
v___x_6262_ = lean_usize_add(v_i_6254_, v___x_6261_);
v___x_6263_ = lean_array_uset(v_bs_x27_6260_, v_i_6254_, v_msg_6258_);
v_i_6254_ = v___x_6262_;
v_bs_6255_ = v___x_6263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6265_, lean_object* v_i_6266_, lean_object* v_bs_6267_){
_start:
{
size_t v_sz_boxed_6268_; size_t v_i_boxed_6269_; lean_object* v_res_6270_; 
v_sz_boxed_6268_ = lean_unbox_usize(v_sz_6265_);
lean_dec(v_sz_6265_);
v_i_boxed_6269_ = lean_unbox_usize(v_i_6266_);
lean_dec(v_i_6266_);
v_res_6270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6268_, v_i_boxed_6269_, v_bs_6267_);
return v_res_6270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6271_, lean_object* v_data_6272_, lean_object* v_ref_6273_, lean_object* v_msg_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_){
_start:
{
lean_object* v_fileName_6280_; lean_object* v_fileMap_6281_; lean_object* v_options_6282_; lean_object* v_currRecDepth_6283_; lean_object* v_maxRecDepth_6284_; lean_object* v_ref_6285_; lean_object* v_currNamespace_6286_; lean_object* v_openDecls_6287_; lean_object* v_initHeartbeats_6288_; lean_object* v_maxHeartbeats_6289_; lean_object* v_quotContext_6290_; lean_object* v_currMacroScope_6291_; uint8_t v_diag_6292_; lean_object* v_cancelTk_x3f_6293_; uint8_t v_suppressElabErrors_6294_; lean_object* v_inheritedTraceOptions_6295_; lean_object* v___x_6296_; lean_object* v_traceState_6297_; lean_object* v_traces_6298_; lean_object* v_ref_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; size_t v_sz_6302_; size_t v___x_6303_; lean_object* v___x_6304_; lean_object* v_msg_6305_; lean_object* v___x_6306_; lean_object* v_a_6307_; lean_object* v___x_6309_; uint8_t v_isShared_6310_; uint8_t v_isSharedCheck_6344_; 
v_fileName_6280_ = lean_ctor_get(v___y_6277_, 0);
v_fileMap_6281_ = lean_ctor_get(v___y_6277_, 1);
v_options_6282_ = lean_ctor_get(v___y_6277_, 2);
v_currRecDepth_6283_ = lean_ctor_get(v___y_6277_, 3);
v_maxRecDepth_6284_ = lean_ctor_get(v___y_6277_, 4);
v_ref_6285_ = lean_ctor_get(v___y_6277_, 5);
v_currNamespace_6286_ = lean_ctor_get(v___y_6277_, 6);
v_openDecls_6287_ = lean_ctor_get(v___y_6277_, 7);
v_initHeartbeats_6288_ = lean_ctor_get(v___y_6277_, 8);
v_maxHeartbeats_6289_ = lean_ctor_get(v___y_6277_, 9);
v_quotContext_6290_ = lean_ctor_get(v___y_6277_, 10);
v_currMacroScope_6291_ = lean_ctor_get(v___y_6277_, 11);
v_diag_6292_ = lean_ctor_get_uint8(v___y_6277_, sizeof(void*)*14);
v_cancelTk_x3f_6293_ = lean_ctor_get(v___y_6277_, 12);
v_suppressElabErrors_6294_ = lean_ctor_get_uint8(v___y_6277_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_6295_ = lean_ctor_get(v___y_6277_, 13);
v___x_6296_ = lean_st_ref_get(v___y_6278_);
v_traceState_6297_ = lean_ctor_get(v___x_6296_, 4);
lean_inc_ref(v_traceState_6297_);
lean_dec(v___x_6296_);
v_traces_6298_ = lean_ctor_get(v_traceState_6297_, 0);
lean_inc_ref(v_traces_6298_);
lean_dec_ref(v_traceState_6297_);
v_ref_6299_ = l_Lean_replaceRef(v_ref_6273_, v_ref_6285_);
lean_inc_ref(v_inheritedTraceOptions_6295_);
lean_inc(v_cancelTk_x3f_6293_);
lean_inc(v_currMacroScope_6291_);
lean_inc(v_quotContext_6290_);
lean_inc(v_maxHeartbeats_6289_);
lean_inc(v_initHeartbeats_6288_);
lean_inc(v_openDecls_6287_);
lean_inc(v_currNamespace_6286_);
lean_inc(v_maxRecDepth_6284_);
lean_inc(v_currRecDepth_6283_);
lean_inc_ref(v_options_6282_);
lean_inc_ref(v_fileMap_6281_);
lean_inc_ref(v_fileName_6280_);
v___x_6300_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_6300_, 0, v_fileName_6280_);
lean_ctor_set(v___x_6300_, 1, v_fileMap_6281_);
lean_ctor_set(v___x_6300_, 2, v_options_6282_);
lean_ctor_set(v___x_6300_, 3, v_currRecDepth_6283_);
lean_ctor_set(v___x_6300_, 4, v_maxRecDepth_6284_);
lean_ctor_set(v___x_6300_, 5, v_ref_6299_);
lean_ctor_set(v___x_6300_, 6, v_currNamespace_6286_);
lean_ctor_set(v___x_6300_, 7, v_openDecls_6287_);
lean_ctor_set(v___x_6300_, 8, v_initHeartbeats_6288_);
lean_ctor_set(v___x_6300_, 9, v_maxHeartbeats_6289_);
lean_ctor_set(v___x_6300_, 10, v_quotContext_6290_);
lean_ctor_set(v___x_6300_, 11, v_currMacroScope_6291_);
lean_ctor_set(v___x_6300_, 12, v_cancelTk_x3f_6293_);
lean_ctor_set(v___x_6300_, 13, v_inheritedTraceOptions_6295_);
lean_ctor_set_uint8(v___x_6300_, sizeof(void*)*14, v_diag_6292_);
lean_ctor_set_uint8(v___x_6300_, sizeof(void*)*14 + 1, v_suppressElabErrors_6294_);
v___x_6301_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6298_);
lean_dec_ref(v_traces_6298_);
v_sz_6302_ = lean_array_size(v___x_6301_);
v___x_6303_ = ((size_t)0ULL);
v___x_6304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6302_, v___x_6303_, v___x_6301_);
v_msg_6305_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6305_, 0, v_data_6272_);
lean_ctor_set(v_msg_6305_, 1, v_msg_6274_);
lean_ctor_set(v_msg_6305_, 2, v___x_6304_);
v___x_6306_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6305_, v___y_6275_, v___y_6276_, v___x_6300_, v___y_6278_);
lean_dec_ref_known(v___x_6300_, 14);
v_a_6307_ = lean_ctor_get(v___x_6306_, 0);
v_isSharedCheck_6344_ = !lean_is_exclusive(v___x_6306_);
if (v_isSharedCheck_6344_ == 0)
{
v___x_6309_ = v___x_6306_;
v_isShared_6310_ = v_isSharedCheck_6344_;
goto v_resetjp_6308_;
}
else
{
lean_inc(v_a_6307_);
lean_dec(v___x_6306_);
v___x_6309_ = lean_box(0);
v_isShared_6310_ = v_isSharedCheck_6344_;
goto v_resetjp_6308_;
}
v_resetjp_6308_:
{
lean_object* v___x_6311_; lean_object* v_traceState_6312_; lean_object* v_env_6313_; lean_object* v_nextMacroScope_6314_; lean_object* v_ngen_6315_; lean_object* v_auxDeclNGen_6316_; lean_object* v_cache_6317_; lean_object* v_messages_6318_; lean_object* v_infoState_6319_; lean_object* v_snapshotTasks_6320_; lean_object* v___x_6322_; uint8_t v_isShared_6323_; uint8_t v_isSharedCheck_6343_; 
v___x_6311_ = lean_st_ref_take(v___y_6278_);
v_traceState_6312_ = lean_ctor_get(v___x_6311_, 4);
v_env_6313_ = lean_ctor_get(v___x_6311_, 0);
v_nextMacroScope_6314_ = lean_ctor_get(v___x_6311_, 1);
v_ngen_6315_ = lean_ctor_get(v___x_6311_, 2);
v_auxDeclNGen_6316_ = lean_ctor_get(v___x_6311_, 3);
v_cache_6317_ = lean_ctor_get(v___x_6311_, 5);
v_messages_6318_ = lean_ctor_get(v___x_6311_, 6);
v_infoState_6319_ = lean_ctor_get(v___x_6311_, 7);
v_snapshotTasks_6320_ = lean_ctor_get(v___x_6311_, 8);
v_isSharedCheck_6343_ = !lean_is_exclusive(v___x_6311_);
if (v_isSharedCheck_6343_ == 0)
{
v___x_6322_ = v___x_6311_;
v_isShared_6323_ = v_isSharedCheck_6343_;
goto v_resetjp_6321_;
}
else
{
lean_inc(v_snapshotTasks_6320_);
lean_inc(v_infoState_6319_);
lean_inc(v_messages_6318_);
lean_inc(v_cache_6317_);
lean_inc(v_traceState_6312_);
lean_inc(v_auxDeclNGen_6316_);
lean_inc(v_ngen_6315_);
lean_inc(v_nextMacroScope_6314_);
lean_inc(v_env_6313_);
lean_dec(v___x_6311_);
v___x_6322_ = lean_box(0);
v_isShared_6323_ = v_isSharedCheck_6343_;
goto v_resetjp_6321_;
}
v_resetjp_6321_:
{
uint64_t v_tid_6324_; lean_object* v___x_6326_; uint8_t v_isShared_6327_; uint8_t v_isSharedCheck_6341_; 
v_tid_6324_ = lean_ctor_get_uint64(v_traceState_6312_, sizeof(void*)*1);
v_isSharedCheck_6341_ = !lean_is_exclusive(v_traceState_6312_);
if (v_isSharedCheck_6341_ == 0)
{
lean_object* v_unused_6342_; 
v_unused_6342_ = lean_ctor_get(v_traceState_6312_, 0);
lean_dec(v_unused_6342_);
v___x_6326_ = v_traceState_6312_;
v_isShared_6327_ = v_isSharedCheck_6341_;
goto v_resetjp_6325_;
}
else
{
lean_dec(v_traceState_6312_);
v___x_6326_ = lean_box(0);
v_isShared_6327_ = v_isSharedCheck_6341_;
goto v_resetjp_6325_;
}
v_resetjp_6325_:
{
lean_object* v___x_6328_; lean_object* v___x_6329_; lean_object* v___x_6331_; 
v___x_6328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6328_, 0, v_ref_6273_);
lean_ctor_set(v___x_6328_, 1, v_a_6307_);
v___x_6329_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6271_, v___x_6328_);
if (v_isShared_6327_ == 0)
{
lean_ctor_set(v___x_6326_, 0, v___x_6329_);
v___x_6331_ = v___x_6326_;
goto v_reusejp_6330_;
}
else
{
lean_object* v_reuseFailAlloc_6340_; 
v_reuseFailAlloc_6340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6340_, 0, v___x_6329_);
lean_ctor_set_uint64(v_reuseFailAlloc_6340_, sizeof(void*)*1, v_tid_6324_);
v___x_6331_ = v_reuseFailAlloc_6340_;
goto v_reusejp_6330_;
}
v_reusejp_6330_:
{
lean_object* v___x_6333_; 
if (v_isShared_6323_ == 0)
{
lean_ctor_set(v___x_6322_, 4, v___x_6331_);
v___x_6333_ = v___x_6322_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6339_; 
v_reuseFailAlloc_6339_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_env_6313_);
lean_ctor_set(v_reuseFailAlloc_6339_, 1, v_nextMacroScope_6314_);
lean_ctor_set(v_reuseFailAlloc_6339_, 2, v_ngen_6315_);
lean_ctor_set(v_reuseFailAlloc_6339_, 3, v_auxDeclNGen_6316_);
lean_ctor_set(v_reuseFailAlloc_6339_, 4, v___x_6331_);
lean_ctor_set(v_reuseFailAlloc_6339_, 5, v_cache_6317_);
lean_ctor_set(v_reuseFailAlloc_6339_, 6, v_messages_6318_);
lean_ctor_set(v_reuseFailAlloc_6339_, 7, v_infoState_6319_);
lean_ctor_set(v_reuseFailAlloc_6339_, 8, v_snapshotTasks_6320_);
v___x_6333_ = v_reuseFailAlloc_6339_;
goto v_reusejp_6332_;
}
v_reusejp_6332_:
{
lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6337_; 
v___x_6334_ = lean_st_ref_put(v___y_6278_, v___x_6333_);
v___x_6335_ = lean_box(0);
if (v_isShared_6310_ == 0)
{
lean_ctor_set(v___x_6309_, 0, v___x_6335_);
v___x_6337_ = v___x_6309_;
goto v_reusejp_6336_;
}
else
{
lean_object* v_reuseFailAlloc_6338_; 
v_reuseFailAlloc_6338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6338_, 0, v___x_6335_);
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
lean_object* v_fst_6380_; lean_object* v_snd_6381_; lean_object* v___y_6383_; lean_object* v___y_6384_; lean_object* v_data_6385_; lean_object* v_fst_6396_; lean_object* v_snd_6397_; lean_object* v___x_6398_; uint8_t v___x_6399_; lean_object* v___y_6401_; lean_object* v_a_6402_; uint8_t v___y_6417_; double v___y_6448_; 
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
lean_object* v___x_6453_; uint8_t v___x_6454_; 
v___x_6453_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6454_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6363_, v___x_6453_);
if (v___x_6454_ == 0)
{
lean_object* v___x_6455_; lean_object* v___x_6456_; double v___x_6457_; double v___x_6458_; double v___x_6459_; 
v___x_6455_ = l_Lean_trace_profiler_threshold;
v___x_6456_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6363_, v___x_6455_);
v___x_6457_ = lean_float_of_nat(v___x_6456_);
v___x_6458_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6459_ = lean_float_div(v___x_6457_, v___x_6458_);
v___y_6448_ = v___x_6459_;
goto v___jp_6447_;
}
else
{
lean_object* v___x_6460_; lean_object* v___x_6461_; double v___x_6462_; 
v___x_6460_ = l_Lean_trace_profiler_threshold;
v___x_6461_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6363_, v___x_6460_);
v___x_6462_ = lean_float_of_nat(v___x_6461_);
v___y_6448_ = v___x_6462_;
goto v___jp_6447_;
}
}
v___jp_6382_:
{
lean_object* v___x_6386_; 
lean_inc(v___y_6383_);
v___x_6386_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6365_, v_data_6385_, v___y_6383_, v___y_6384_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_);
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
v___y_6383_ = v___y_6401_;
v___y_6384_ = v_a_6402_;
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
v___y_6383_ = v___y_6401_;
v___y_6384_ = v_a_6402_;
v_data_6385_ = v_data_6408_;
goto v___jp_6382_;
}
}
v___jp_6411_:
{
lean_object* v_ref_6412_; lean_object* v___x_6413_; 
v_ref_6412_ = lean_ctor_get(v___y_6377_, 5);
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
lean_object* v___x_6418_; lean_object* v_traceState_6419_; lean_object* v_env_6420_; lean_object* v_nextMacroScope_6421_; lean_object* v_ngen_6422_; lean_object* v_auxDeclNGen_6423_; lean_object* v_cache_6424_; lean_object* v_messages_6425_; lean_object* v_infoState_6426_; lean_object* v_snapshotTasks_6427_; lean_object* v___x_6429_; uint8_t v_isShared_6430_; uint8_t v_isSharedCheck_6446_; 
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
v_messages_6425_ = lean_ctor_get(v___x_6418_, 6);
v_infoState_6426_ = lean_ctor_get(v___x_6418_, 7);
v_snapshotTasks_6427_ = lean_ctor_get(v___x_6418_, 8);
v_isSharedCheck_6446_ = !lean_is_exclusive(v___x_6418_);
if (v_isSharedCheck_6446_ == 0)
{
v___x_6429_ = v___x_6418_;
v_isShared_6430_ = v_isSharedCheck_6446_;
goto v_resetjp_6428_;
}
else
{
lean_inc(v_snapshotTasks_6427_);
lean_inc(v_infoState_6426_);
lean_inc(v_messages_6425_);
lean_inc(v_cache_6424_);
lean_inc(v_traceState_6419_);
lean_inc(v_auxDeclNGen_6423_);
lean_inc(v_ngen_6422_);
lean_inc(v_nextMacroScope_6421_);
lean_inc(v_env_6420_);
lean_dec(v___x_6418_);
v___x_6429_ = lean_box(0);
v_isShared_6430_ = v_isSharedCheck_6446_;
goto v_resetjp_6428_;
}
v_resetjp_6428_:
{
uint64_t v_tid_6431_; lean_object* v_traces_6432_; lean_object* v___x_6434_; uint8_t v_isShared_6435_; uint8_t v_isSharedCheck_6445_; 
v_tid_6431_ = lean_ctor_get_uint64(v_traceState_6419_, sizeof(void*)*1);
v_traces_6432_ = lean_ctor_get(v_traceState_6419_, 0);
v_isSharedCheck_6445_ = !lean_is_exclusive(v_traceState_6419_);
if (v_isSharedCheck_6445_ == 0)
{
v___x_6434_ = v_traceState_6419_;
v_isShared_6435_ = v_isSharedCheck_6445_;
goto v_resetjp_6433_;
}
else
{
lean_inc(v_traces_6432_);
lean_dec(v_traceState_6419_);
v___x_6434_ = lean_box(0);
v_isShared_6435_ = v_isSharedCheck_6445_;
goto v_resetjp_6433_;
}
v_resetjp_6433_:
{
lean_object* v___x_6436_; lean_object* v___x_6438_; 
v___x_6436_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6365_, v_traces_6432_);
lean_dec_ref(v_traces_6432_);
if (v_isShared_6435_ == 0)
{
lean_ctor_set(v___x_6434_, 0, v___x_6436_);
v___x_6438_ = v___x_6434_;
goto v_reusejp_6437_;
}
else
{
lean_object* v_reuseFailAlloc_6444_; 
v_reuseFailAlloc_6444_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6444_, 0, v___x_6436_);
lean_ctor_set_uint64(v_reuseFailAlloc_6444_, sizeof(void*)*1, v_tid_6431_);
v___x_6438_ = v_reuseFailAlloc_6444_;
goto v_reusejp_6437_;
}
v_reusejp_6437_:
{
lean_object* v___x_6440_; 
if (v_isShared_6430_ == 0)
{
lean_ctor_set(v___x_6429_, 4, v___x_6438_);
v___x_6440_ = v___x_6429_;
goto v_reusejp_6439_;
}
else
{
lean_object* v_reuseFailAlloc_6443_; 
v_reuseFailAlloc_6443_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6443_, 0, v_env_6420_);
lean_ctor_set(v_reuseFailAlloc_6443_, 1, v_nextMacroScope_6421_);
lean_ctor_set(v_reuseFailAlloc_6443_, 2, v_ngen_6422_);
lean_ctor_set(v_reuseFailAlloc_6443_, 3, v_auxDeclNGen_6423_);
lean_ctor_set(v_reuseFailAlloc_6443_, 4, v___x_6438_);
lean_ctor_set(v_reuseFailAlloc_6443_, 5, v_cache_6424_);
lean_ctor_set(v_reuseFailAlloc_6443_, 6, v_messages_6425_);
lean_ctor_set(v_reuseFailAlloc_6443_, 7, v_infoState_6426_);
lean_ctor_set(v_reuseFailAlloc_6443_, 8, v_snapshotTasks_6427_);
v___x_6440_ = v_reuseFailAlloc_6443_;
goto v_reusejp_6439_;
}
v_reusejp_6439_:
{
lean_object* v___x_6441_; lean_object* v___x_6442_; 
v___x_6441_ = lean_st_ref_put(v___y_6378_, v___x_6440_);
v___x_6442_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6380_);
return v___x_6442_;
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
v___jp_6447_:
{
double v___x_6449_; double v___x_6450_; double v___x_6451_; uint8_t v___x_6452_; 
v___x_6449_ = lean_unbox_float(v_snd_6397_);
v___x_6450_ = lean_unbox_float(v_fst_6396_);
v___x_6451_ = lean_float_sub(v___x_6449_, v___x_6450_);
v___x_6452_ = lean_float_decLt(v___y_6448_, v___x_6451_);
v___y_6417_ = v___x_6452_;
goto v___jp_6416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6463_ = _args[0];
lean_object* v_collapsed_6464_ = _args[1];
lean_object* v_tag_6465_ = _args[2];
lean_object* v_opts_6466_ = _args[3];
lean_object* v_clsEnabled_6467_ = _args[4];
lean_object* v_oldTraces_6468_ = _args[5];
lean_object* v_msg_6469_ = _args[6];
lean_object* v_resStartStop_6470_ = _args[7];
lean_object* v___y_6471_ = _args[8];
lean_object* v___y_6472_ = _args[9];
lean_object* v___y_6473_ = _args[10];
lean_object* v___y_6474_ = _args[11];
lean_object* v___y_6475_ = _args[12];
lean_object* v___y_6476_ = _args[13];
lean_object* v___y_6477_ = _args[14];
lean_object* v___y_6478_ = _args[15];
lean_object* v___y_6479_ = _args[16];
lean_object* v___y_6480_ = _args[17];
lean_object* v___y_6481_ = _args[18];
lean_object* v___y_6482_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6483_; uint8_t v_clsEnabled_boxed_6484_; lean_object* v_res_6485_; 
v_collapsed_boxed_6483_ = lean_unbox(v_collapsed_6464_);
v_clsEnabled_boxed_6484_ = lean_unbox(v_clsEnabled_6467_);
v_res_6485_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6463_, v_collapsed_boxed_6483_, v_tag_6465_, v_opts_6466_, v_clsEnabled_boxed_6484_, v_oldTraces_6468_, v_msg_6469_, v_resStartStop_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_);
lean_dec(v___y_6481_);
lean_dec_ref(v___y_6480_);
lean_dec(v___y_6479_);
lean_dec_ref(v___y_6478_);
lean_dec(v___y_6477_);
lean_dec_ref(v___y_6476_);
lean_dec(v___y_6475_);
lean_dec_ref(v___y_6474_);
lean_dec(v___y_6473_);
lean_dec(v___y_6472_);
lean_dec_ref(v___y_6471_);
lean_dec_ref(v_opts_6466_);
return v_res_6485_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6490_; lean_object* v___x_6491_; 
v___x_6490_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6491_ = l_Lean_stringToMessageData(v___x_6490_);
return v___x_6491_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6492_, lean_object* v_b_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_){
_start:
{
if (lean_obj_tag(v_as_x27_6492_) == 0)
{
lean_object* v___x_6506_; 
v___x_6506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6506_, 0, v_b_6493_);
return v___x_6506_;
}
else
{
lean_object* v_head_6507_; lean_object* v_options_6508_; lean_object* v_tail_6509_; lean_object* v_name_6510_; lean_object* v_run_x27_6511_; lean_object* v_inheritedTraceOptions_6512_; uint8_t v_hasTrace_6513_; lean_object* v___x_6514_; uint8_t v___y_6516_; lean_object* v___x_6521_; lean_object* v___y_6523_; 
lean_dec_ref(v_b_6493_);
v_head_6507_ = lean_ctor_get(v_as_x27_6492_, 0);
v_options_6508_ = lean_ctor_get(v___y_6503_, 2);
v_tail_6509_ = lean_ctor_get(v_as_x27_6492_, 1);
v_name_6510_ = lean_ctor_get(v_head_6507_, 0);
v_run_x27_6511_ = lean_ctor_get(v_head_6507_, 1);
v_inheritedTraceOptions_6512_ = lean_ctor_get(v___y_6503_, 13);
v_hasTrace_6513_ = lean_ctor_get_uint8(v_options_6508_, sizeof(void*)*1);
v___x_6514_ = lean_box(0);
v___x_6521_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6513_ == 0)
{
lean_object* v___x_6551_; 
lean_inc_ref(v_run_x27_6511_);
lean_inc(v___y_6504_);
lean_inc_ref(v___y_6503_);
lean_inc(v___y_6502_);
lean_inc_ref(v___y_6501_);
lean_inc(v___y_6500_);
lean_inc_ref(v___y_6499_);
lean_inc(v___y_6498_);
lean_inc_ref(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc_ref(v___y_6494_);
v___x_6551_ = lean_apply_12(v_run_x27_6511_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, lean_box(0));
v___y_6523_ = v___x_6551_;
goto v___jp_6522_;
}
else
{
lean_object* v___f_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; uint8_t v___x_6556_; lean_object* v___y_6558_; lean_object* v___y_6559_; lean_object* v_a_6560_; lean_object* v___y_6573_; lean_object* v___y_6574_; lean_object* v_a_6575_; 
lean_inc(v_name_6510_);
v___f_6552_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6552_, 0, v_name_6510_);
v___x_6553_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_6554_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6555_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_6556_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6512_, v_options_6508_, v___x_6555_);
if (v___x_6556_ == 0)
{
lean_object* v___x_6625_; uint8_t v___x_6626_; 
v___x_6625_ = l_Lean_trace_profiler;
v___x_6626_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6508_, v___x_6625_);
if (v___x_6626_ == 0)
{
lean_object* v___x_6627_; 
lean_dec_ref(v___f_6552_);
lean_inc_ref(v_run_x27_6511_);
lean_inc(v___y_6504_);
lean_inc_ref(v___y_6503_);
lean_inc(v___y_6502_);
lean_inc_ref(v___y_6501_);
lean_inc(v___y_6500_);
lean_inc_ref(v___y_6499_);
lean_inc(v___y_6498_);
lean_inc_ref(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc_ref(v___y_6494_);
v___x_6627_ = lean_apply_12(v_run_x27_6511_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, lean_box(0));
v___y_6523_ = v___x_6627_;
goto v___jp_6522_;
}
else
{
goto v___jp_6584_;
}
}
else
{
goto v___jp_6584_;
}
v___jp_6557_:
{
lean_object* v___x_6561_; double v___x_6562_; double v___x_6563_; double v___x_6564_; double v___x_6565_; double v___x_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; 
v___x_6561_ = lean_io_mono_nanos_now();
v___x_6562_ = lean_float_of_nat(v___y_6558_);
v___x_6563_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6564_ = lean_float_div(v___x_6562_, v___x_6563_);
v___x_6565_ = lean_float_of_nat(v___x_6561_);
v___x_6566_ = lean_float_div(v___x_6565_, v___x_6563_);
v___x_6567_ = lean_box_float(v___x_6564_);
v___x_6568_ = lean_box_float(v___x_6566_);
v___x_6569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6569_, 0, v___x_6567_);
lean_ctor_set(v___x_6569_, 1, v___x_6568_);
v___x_6570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6570_, 0, v_a_6560_);
lean_ctor_set(v___x_6570_, 1, v___x_6569_);
v___x_6571_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6553_, v_hasTrace_6513_, v___x_6554_, v_options_6508_, v___x_6556_, v___y_6559_, v___f_6552_, v___x_6570_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_);
v___y_6523_ = v___x_6571_;
goto v___jp_6522_;
}
v___jp_6572_:
{
lean_object* v___x_6576_; double v___x_6577_; double v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; 
v___x_6576_ = lean_io_get_num_heartbeats();
v___x_6577_ = lean_float_of_nat(v___y_6573_);
v___x_6578_ = lean_float_of_nat(v___x_6576_);
v___x_6579_ = lean_box_float(v___x_6577_);
v___x_6580_ = lean_box_float(v___x_6578_);
v___x_6581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6581_, 0, v___x_6579_);
lean_ctor_set(v___x_6581_, 1, v___x_6580_);
v___x_6582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6582_, 0, v_a_6575_);
lean_ctor_set(v___x_6582_, 1, v___x_6581_);
v___x_6583_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6553_, v_hasTrace_6513_, v___x_6554_, v_options_6508_, v___x_6556_, v___y_6574_, v___f_6552_, v___x_6582_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_);
v___y_6523_ = v___x_6583_;
goto v___jp_6522_;
}
v___jp_6584_:
{
lean_object* v___x_6585_; lean_object* v_a_6586_; lean_object* v___x_6587_; uint8_t v___x_6588_; 
v___x_6585_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6504_);
v_a_6586_ = lean_ctor_get(v___x_6585_, 0);
lean_inc(v_a_6586_);
lean_dec_ref(v___x_6585_);
v___x_6587_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6588_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6508_, v___x_6587_);
if (v___x_6588_ == 0)
{
lean_object* v___x_6589_; lean_object* v___x_6590_; 
v___x_6589_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_6511_);
lean_inc(v___y_6504_);
lean_inc_ref(v___y_6503_);
lean_inc(v___y_6502_);
lean_inc_ref(v___y_6501_);
lean_inc(v___y_6500_);
lean_inc_ref(v___y_6499_);
lean_inc(v___y_6498_);
lean_inc_ref(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc_ref(v___y_6494_);
v___x_6590_ = lean_apply_12(v_run_x27_6511_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, lean_box(0));
if (lean_obj_tag(v___x_6590_) == 0)
{
lean_object* v_a_6591_; lean_object* v___x_6593_; uint8_t v_isShared_6594_; uint8_t v_isSharedCheck_6598_; 
v_a_6591_ = lean_ctor_get(v___x_6590_, 0);
v_isSharedCheck_6598_ = !lean_is_exclusive(v___x_6590_);
if (v_isSharedCheck_6598_ == 0)
{
v___x_6593_ = v___x_6590_;
v_isShared_6594_ = v_isSharedCheck_6598_;
goto v_resetjp_6592_;
}
else
{
lean_inc(v_a_6591_);
lean_dec(v___x_6590_);
v___x_6593_ = lean_box(0);
v_isShared_6594_ = v_isSharedCheck_6598_;
goto v_resetjp_6592_;
}
v_resetjp_6592_:
{
lean_object* v___x_6596_; 
if (v_isShared_6594_ == 0)
{
lean_ctor_set_tag(v___x_6593_, 1);
v___x_6596_ = v___x_6593_;
goto v_reusejp_6595_;
}
else
{
lean_object* v_reuseFailAlloc_6597_; 
v_reuseFailAlloc_6597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6597_, 0, v_a_6591_);
v___x_6596_ = v_reuseFailAlloc_6597_;
goto v_reusejp_6595_;
}
v_reusejp_6595_:
{
v___y_6558_ = v___x_6589_;
v___y_6559_ = v_a_6586_;
v_a_6560_ = v___x_6596_;
goto v___jp_6557_;
}
}
}
else
{
lean_object* v_a_6599_; lean_object* v___x_6601_; uint8_t v_isShared_6602_; uint8_t v_isSharedCheck_6606_; 
v_a_6599_ = lean_ctor_get(v___x_6590_, 0);
v_isSharedCheck_6606_ = !lean_is_exclusive(v___x_6590_);
if (v_isSharedCheck_6606_ == 0)
{
v___x_6601_ = v___x_6590_;
v_isShared_6602_ = v_isSharedCheck_6606_;
goto v_resetjp_6600_;
}
else
{
lean_inc(v_a_6599_);
lean_dec(v___x_6590_);
v___x_6601_ = lean_box(0);
v_isShared_6602_ = v_isSharedCheck_6606_;
goto v_resetjp_6600_;
}
v_resetjp_6600_:
{
lean_object* v___x_6604_; 
if (v_isShared_6602_ == 0)
{
lean_ctor_set_tag(v___x_6601_, 0);
v___x_6604_ = v___x_6601_;
goto v_reusejp_6603_;
}
else
{
lean_object* v_reuseFailAlloc_6605_; 
v_reuseFailAlloc_6605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6605_, 0, v_a_6599_);
v___x_6604_ = v_reuseFailAlloc_6605_;
goto v_reusejp_6603_;
}
v_reusejp_6603_:
{
v___y_6558_ = v___x_6589_;
v___y_6559_ = v_a_6586_;
v_a_6560_ = v___x_6604_;
goto v___jp_6557_;
}
}
}
}
else
{
lean_object* v___x_6607_; lean_object* v___x_6608_; 
v___x_6607_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_6511_);
lean_inc(v___y_6504_);
lean_inc_ref(v___y_6503_);
lean_inc(v___y_6502_);
lean_inc_ref(v___y_6501_);
lean_inc(v___y_6500_);
lean_inc_ref(v___y_6499_);
lean_inc(v___y_6498_);
lean_inc_ref(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc(v___y_6495_);
lean_inc_ref(v___y_6494_);
v___x_6608_ = lean_apply_12(v_run_x27_6511_, v___y_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, lean_box(0));
if (lean_obj_tag(v___x_6608_) == 0)
{
lean_object* v_a_6609_; lean_object* v___x_6611_; uint8_t v_isShared_6612_; uint8_t v_isSharedCheck_6616_; 
v_a_6609_ = lean_ctor_get(v___x_6608_, 0);
v_isSharedCheck_6616_ = !lean_is_exclusive(v___x_6608_);
if (v_isSharedCheck_6616_ == 0)
{
v___x_6611_ = v___x_6608_;
v_isShared_6612_ = v_isSharedCheck_6616_;
goto v_resetjp_6610_;
}
else
{
lean_inc(v_a_6609_);
lean_dec(v___x_6608_);
v___x_6611_ = lean_box(0);
v_isShared_6612_ = v_isSharedCheck_6616_;
goto v_resetjp_6610_;
}
v_resetjp_6610_:
{
lean_object* v___x_6614_; 
if (v_isShared_6612_ == 0)
{
lean_ctor_set_tag(v___x_6611_, 1);
v___x_6614_ = v___x_6611_;
goto v_reusejp_6613_;
}
else
{
lean_object* v_reuseFailAlloc_6615_; 
v_reuseFailAlloc_6615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6615_, 0, v_a_6609_);
v___x_6614_ = v_reuseFailAlloc_6615_;
goto v_reusejp_6613_;
}
v_reusejp_6613_:
{
v___y_6573_ = v___x_6607_;
v___y_6574_ = v_a_6586_;
v_a_6575_ = v___x_6614_;
goto v___jp_6572_;
}
}
}
else
{
lean_object* v_a_6617_; lean_object* v___x_6619_; uint8_t v_isShared_6620_; uint8_t v_isSharedCheck_6624_; 
v_a_6617_ = lean_ctor_get(v___x_6608_, 0);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6608_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6619_ = v___x_6608_;
v_isShared_6620_ = v_isSharedCheck_6624_;
goto v_resetjp_6618_;
}
else
{
lean_inc(v_a_6617_);
lean_dec(v___x_6608_);
v___x_6619_ = lean_box(0);
v_isShared_6620_ = v_isSharedCheck_6624_;
goto v_resetjp_6618_;
}
v_resetjp_6618_:
{
lean_object* v___x_6622_; 
if (v_isShared_6620_ == 0)
{
lean_ctor_set_tag(v___x_6619_, 0);
v___x_6622_ = v___x_6619_;
goto v_reusejp_6621_;
}
else
{
lean_object* v_reuseFailAlloc_6623_; 
v_reuseFailAlloc_6623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6623_, 0, v_a_6617_);
v___x_6622_ = v_reuseFailAlloc_6623_;
goto v_reusejp_6621_;
}
v_reusejp_6621_:
{
v___y_6573_ = v___x_6607_;
v___y_6574_ = v_a_6586_;
v_a_6575_ = v___x_6622_;
goto v___jp_6572_;
}
}
}
}
}
}
v___jp_6515_:
{
lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; 
v___x_6517_ = lean_box(v___y_6516_);
v___x_6518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6518_, 0, v___x_6517_);
v___x_6519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6519_, 0, v___x_6518_);
lean_ctor_set(v___x_6519_, 1, v___x_6514_);
v___x_6520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6520_, 0, v___x_6519_);
return v___x_6520_;
}
v___jp_6522_:
{
if (lean_obj_tag(v___y_6523_) == 0)
{
lean_object* v_a_6524_; uint8_t v___x_6525_; 
v_a_6524_ = lean_ctor_get(v___y_6523_, 0);
lean_inc(v_a_6524_);
lean_dec_ref_known(v___y_6523_, 1);
v___x_6525_ = lean_unbox(v_a_6524_);
if (v___x_6525_ == 0)
{
lean_dec(v_a_6524_);
v_as_x27_6492_ = v_tail_6509_;
v_b_6493_ = v___x_6521_;
goto _start;
}
else
{
if (v_hasTrace_6513_ == 0)
{
uint8_t v___x_6527_; 
v___x_6527_ = lean_unbox(v_a_6524_);
lean_dec(v_a_6524_);
v___y_6516_ = v___x_6527_;
goto v___jp_6515_;
}
else
{
lean_object* v___x_6528_; lean_object* v___x_6529_; uint8_t v___x_6530_; 
v___x_6528_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_6529_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_6530_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6512_, v_options_6508_, v___x_6529_);
if (v___x_6530_ == 0)
{
uint8_t v___x_6531_; 
v___x_6531_ = lean_unbox(v_a_6524_);
lean_dec(v_a_6524_);
v___y_6516_ = v___x_6531_;
goto v___jp_6515_;
}
else
{
lean_object* v___x_6532_; lean_object* v___x_6533_; 
v___x_6532_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_6533_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6528_, v___x_6532_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_);
if (lean_obj_tag(v___x_6533_) == 0)
{
uint8_t v___x_6534_; 
lean_dec_ref_known(v___x_6533_, 1);
v___x_6534_ = lean_unbox(v_a_6524_);
lean_dec(v_a_6524_);
v___y_6516_ = v___x_6534_;
goto v___jp_6515_;
}
else
{
lean_object* v_a_6535_; lean_object* v___x_6537_; uint8_t v_isShared_6538_; uint8_t v_isSharedCheck_6542_; 
lean_dec(v_a_6524_);
v_a_6535_ = lean_ctor_get(v___x_6533_, 0);
v_isSharedCheck_6542_ = !lean_is_exclusive(v___x_6533_);
if (v_isSharedCheck_6542_ == 0)
{
v___x_6537_ = v___x_6533_;
v_isShared_6538_ = v_isSharedCheck_6542_;
goto v_resetjp_6536_;
}
else
{
lean_inc(v_a_6535_);
lean_dec(v___x_6533_);
v___x_6537_ = lean_box(0);
v_isShared_6538_ = v_isSharedCheck_6542_;
goto v_resetjp_6536_;
}
v_resetjp_6536_:
{
lean_object* v___x_6540_; 
if (v_isShared_6538_ == 0)
{
v___x_6540_ = v___x_6537_;
goto v_reusejp_6539_;
}
else
{
lean_object* v_reuseFailAlloc_6541_; 
v_reuseFailAlloc_6541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6541_, 0, v_a_6535_);
v___x_6540_ = v_reuseFailAlloc_6541_;
goto v_reusejp_6539_;
}
v_reusejp_6539_:
{
return v___x_6540_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6543_; lean_object* v___x_6545_; uint8_t v_isShared_6546_; uint8_t v_isSharedCheck_6550_; 
v_a_6543_ = lean_ctor_get(v___y_6523_, 0);
v_isSharedCheck_6550_ = !lean_is_exclusive(v___y_6523_);
if (v_isSharedCheck_6550_ == 0)
{
v___x_6545_ = v___y_6523_;
v_isShared_6546_ = v_isSharedCheck_6550_;
goto v_resetjp_6544_;
}
else
{
lean_inc(v_a_6543_);
lean_dec(v___y_6523_);
v___x_6545_ = lean_box(0);
v_isShared_6546_ = v_isSharedCheck_6550_;
goto v_resetjp_6544_;
}
v_resetjp_6544_:
{
lean_object* v___x_6548_; 
if (v_isShared_6546_ == 0)
{
v___x_6548_ = v___x_6545_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_a_6543_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_6628_, lean_object* v_b_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_, lean_object* v___y_6640_, lean_object* v___y_6641_){
_start:
{
lean_object* v_res_6642_; 
v_res_6642_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6628_, v_b_6629_, v___y_6630_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
lean_dec(v___y_6640_);
lean_dec_ref(v___y_6639_);
lean_dec(v___y_6638_);
lean_dec_ref(v___y_6637_);
lean_dec(v___y_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
lean_dec(v___y_6632_);
lean_dec(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec(v_as_x27_6628_);
return v_res_6642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_6645_; lean_object* v___x_6646_; 
v___x_6645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_6646_ = l_Lean_stringToMessageData(v___x_6645_);
return v___x_6646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_6648_; lean_object* v___x_6649_; 
v___x_6648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_6649_ = l_Lean_stringToMessageData(v___x_6648_);
return v___x_6649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_6650_, lean_object* v_a_6651_, lean_object* v_a_6652_, lean_object* v_a_6653_, lean_object* v_a_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_, lean_object* v_a_6657_, lean_object* v_a_6658_, lean_object* v_a_6659_, lean_object* v_a_6660_, lean_object* v_a_6661_){
_start:
{
lean_object* v___x_6663_; lean_object* v___x_6664_; 
v___x_6663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_6664_ = l_Lean_Core_checkSystem(v___x_6663_, v_a_6660_, v_a_6661_);
if (lean_obj_tag(v___x_6664_) == 0)
{
lean_object* v___x_6665_; lean_object* v_caches_6666_; lean_object* v_typeAnalysis_6667_; lean_object* v_target_6668_; lean_object* v_hypotheses_6669_; lean_object* v___x_6671_; uint8_t v_isShared_6672_; uint8_t v_isSharedCheck_6752_; 
lean_dec_ref_known(v___x_6664_, 1);
v___x_6665_ = lean_st_ref_take(v_a_6652_);
v_caches_6666_ = lean_ctor_get(v___x_6665_, 0);
v_typeAnalysis_6667_ = lean_ctor_get(v___x_6665_, 1);
v_target_6668_ = lean_ctor_get(v___x_6665_, 2);
v_hypotheses_6669_ = lean_ctor_get(v___x_6665_, 3);
v_isSharedCheck_6752_ = !lean_is_exclusive(v___x_6665_);
if (v_isSharedCheck_6752_ == 0)
{
v___x_6671_ = v___x_6665_;
v_isShared_6672_ = v_isSharedCheck_6752_;
goto v_resetjp_6670_;
}
else
{
lean_inc(v_hypotheses_6669_);
lean_inc(v_target_6668_);
lean_inc(v_typeAnalysis_6667_);
lean_inc(v_caches_6666_);
lean_dec(v___x_6665_);
v___x_6671_ = lean_box(0);
v_isShared_6672_ = v_isSharedCheck_6752_;
goto v_resetjp_6670_;
}
v_resetjp_6670_:
{
uint8_t v___x_6673_; lean_object* v___x_6675_; 
v___x_6673_ = 0;
if (v_isShared_6672_ == 0)
{
v___x_6675_ = v___x_6671_;
goto v_reusejp_6674_;
}
else
{
lean_object* v_reuseFailAlloc_6751_; 
v_reuseFailAlloc_6751_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_caches_6666_);
lean_ctor_set(v_reuseFailAlloc_6751_, 1, v_typeAnalysis_6667_);
lean_ctor_set(v_reuseFailAlloc_6751_, 2, v_target_6668_);
lean_ctor_set(v_reuseFailAlloc_6751_, 3, v_hypotheses_6669_);
v___x_6675_ = v_reuseFailAlloc_6751_;
goto v_reusejp_6674_;
}
v_reusejp_6674_:
{
lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; 
lean_ctor_set_uint8(v___x_6675_, sizeof(void*)*4, v___x_6673_);
v___x_6676_ = lean_st_ref_put(v_a_6652_, v___x_6675_);
v___x_6677_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_6678_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_6650_, v___x_6677_, v_a_6651_, v_a_6652_, v_a_6653_, v_a_6654_, v_a_6655_, v_a_6656_, v_a_6657_, v_a_6658_, v_a_6659_, v_a_6660_, v_a_6661_);
if (lean_obj_tag(v___x_6678_) == 0)
{
lean_object* v_a_6679_; lean_object* v___x_6681_; uint8_t v_isShared_6682_; uint8_t v_isSharedCheck_6742_; 
v_a_6679_ = lean_ctor_get(v___x_6678_, 0);
v_isSharedCheck_6742_ = !lean_is_exclusive(v___x_6678_);
if (v_isSharedCheck_6742_ == 0)
{
v___x_6681_ = v___x_6678_;
v_isShared_6682_ = v_isSharedCheck_6742_;
goto v_resetjp_6680_;
}
else
{
lean_inc(v_a_6679_);
lean_dec(v___x_6678_);
v___x_6681_ = lean_box(0);
v_isShared_6682_ = v_isSharedCheck_6742_;
goto v_resetjp_6680_;
}
v_resetjp_6680_:
{
lean_object* v_fst_6683_; 
v_fst_6683_ = lean_ctor_get(v_a_6679_, 0);
lean_inc(v_fst_6683_);
lean_dec(v_a_6679_);
if (lean_obj_tag(v_fst_6683_) == 0)
{
lean_object* v___x_6684_; uint8_t v_didChange_6685_; 
v___x_6684_ = lean_st_ref_get(v_a_6652_);
v_didChange_6685_ = lean_ctor_get_uint8(v___x_6684_, sizeof(void*)*4);
lean_dec(v___x_6684_);
if (v_didChange_6685_ == 0)
{
lean_object* v_options_6686_; uint8_t v_hasTrace_6687_; 
v_options_6686_ = lean_ctor_get(v_a_6660_, 2);
v_hasTrace_6687_ = lean_ctor_get_uint8(v_options_6686_, sizeof(void*)*1);
if (v_hasTrace_6687_ == 0)
{
lean_object* v___x_6688_; lean_object* v___x_6690_; 
v___x_6688_ = lean_box(v_didChange_6685_);
if (v_isShared_6682_ == 0)
{
lean_ctor_set(v___x_6681_, 0, v___x_6688_);
v___x_6690_ = v___x_6681_;
goto v_reusejp_6689_;
}
else
{
lean_object* v_reuseFailAlloc_6691_; 
v_reuseFailAlloc_6691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6691_, 0, v___x_6688_);
v___x_6690_ = v_reuseFailAlloc_6691_;
goto v_reusejp_6689_;
}
v_reusejp_6689_:
{
return v___x_6690_;
}
}
else
{
lean_object* v_inheritedTraceOptions_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; uint8_t v___x_6695_; 
v_inheritedTraceOptions_6692_ = lean_ctor_get(v_a_6660_, 13);
v___x_6693_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_6694_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_6695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6692_, v_options_6686_, v___x_6694_);
if (v___x_6695_ == 0)
{
lean_object* v___x_6696_; lean_object* v___x_6698_; 
v___x_6696_ = lean_box(v_didChange_6685_);
if (v_isShared_6682_ == 0)
{
lean_ctor_set(v___x_6681_, 0, v___x_6696_);
v___x_6698_ = v___x_6681_;
goto v_reusejp_6697_;
}
else
{
lean_object* v_reuseFailAlloc_6699_; 
v_reuseFailAlloc_6699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6699_, 0, v___x_6696_);
v___x_6698_ = v_reuseFailAlloc_6699_;
goto v_reusejp_6697_;
}
v_reusejp_6697_:
{
return v___x_6698_;
}
}
else
{
lean_object* v___x_6700_; lean_object* v___x_6701_; 
lean_del_object(v___x_6681_);
v___x_6700_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6701_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6693_, v___x_6700_, v_a_6658_, v_a_6659_, v_a_6660_, v_a_6661_);
if (lean_obj_tag(v___x_6701_) == 0)
{
lean_object* v___x_6703_; uint8_t v_isShared_6704_; uint8_t v_isSharedCheck_6709_; 
v_isSharedCheck_6709_ = !lean_is_exclusive(v___x_6701_);
if (v_isSharedCheck_6709_ == 0)
{
lean_object* v_unused_6710_; 
v_unused_6710_ = lean_ctor_get(v___x_6701_, 0);
lean_dec(v_unused_6710_);
v___x_6703_ = v___x_6701_;
v_isShared_6704_ = v_isSharedCheck_6709_;
goto v_resetjp_6702_;
}
else
{
lean_dec(v___x_6701_);
v___x_6703_ = lean_box(0);
v_isShared_6704_ = v_isSharedCheck_6709_;
goto v_resetjp_6702_;
}
v_resetjp_6702_:
{
lean_object* v___x_6705_; lean_object* v___x_6707_; 
v___x_6705_ = lean_box(v_didChange_6685_);
if (v_isShared_6704_ == 0)
{
lean_ctor_set(v___x_6703_, 0, v___x_6705_);
v___x_6707_ = v___x_6703_;
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
else
{
lean_object* v_a_6711_; lean_object* v___x_6713_; uint8_t v_isShared_6714_; uint8_t v_isSharedCheck_6718_; 
v_a_6711_ = lean_ctor_get(v___x_6701_, 0);
v_isSharedCheck_6718_ = !lean_is_exclusive(v___x_6701_);
if (v_isSharedCheck_6718_ == 0)
{
v___x_6713_ = v___x_6701_;
v_isShared_6714_ = v_isSharedCheck_6718_;
goto v_resetjp_6712_;
}
else
{
lean_inc(v_a_6711_);
lean_dec(v___x_6701_);
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
lean_object* v_options_6719_; uint8_t v_hasTrace_6720_; 
lean_del_object(v___x_6681_);
v_options_6719_ = lean_ctor_get(v_a_6660_, 2);
v_hasTrace_6720_ = lean_ctor_get_uint8(v_options_6719_, sizeof(void*)*1);
if (v_hasTrace_6720_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; uint8_t v___x_6725_; 
v_inheritedTraceOptions_6722_ = lean_ctor_get(v_a_6660_, 13);
v___x_6723_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14));
v___x_6724_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___x_6725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6722_, v_options_6719_, v___x_6724_);
if (v___x_6725_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6727_; lean_object* v___x_6728_; 
v___x_6727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6728_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6723_, v___x_6727_, v_a_6658_, v_a_6659_, v_a_6660_, v_a_6661_);
if (lean_obj_tag(v___x_6728_) == 0)
{
lean_dec_ref_known(v___x_6728_, 1);
goto _start;
}
else
{
lean_object* v_a_6730_; lean_object* v___x_6732_; uint8_t v_isShared_6733_; uint8_t v_isSharedCheck_6737_; 
v_a_6730_ = lean_ctor_get(v___x_6728_, 0);
v_isSharedCheck_6737_ = !lean_is_exclusive(v___x_6728_);
if (v_isSharedCheck_6737_ == 0)
{
v___x_6732_ = v___x_6728_;
v_isShared_6733_ = v_isSharedCheck_6737_;
goto v_resetjp_6731_;
}
else
{
lean_inc(v_a_6730_);
lean_dec(v___x_6728_);
v___x_6732_ = lean_box(0);
v_isShared_6733_ = v_isSharedCheck_6737_;
goto v_resetjp_6731_;
}
v_resetjp_6731_:
{
lean_object* v___x_6735_; 
if (v_isShared_6733_ == 0)
{
v___x_6735_ = v___x_6732_;
goto v_reusejp_6734_;
}
else
{
lean_object* v_reuseFailAlloc_6736_; 
v_reuseFailAlloc_6736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6736_, 0, v_a_6730_);
v___x_6735_ = v_reuseFailAlloc_6736_;
goto v_reusejp_6734_;
}
v_reusejp_6734_:
{
return v___x_6735_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_6738_; lean_object* v___x_6740_; 
v_val_6738_ = lean_ctor_get(v_fst_6683_, 0);
lean_inc(v_val_6738_);
lean_dec_ref_known(v_fst_6683_, 1);
if (v_isShared_6682_ == 0)
{
lean_ctor_set(v___x_6681_, 0, v_val_6738_);
v___x_6740_ = v___x_6681_;
goto v_reusejp_6739_;
}
else
{
lean_object* v_reuseFailAlloc_6741_; 
v_reuseFailAlloc_6741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6741_, 0, v_val_6738_);
v___x_6740_ = v_reuseFailAlloc_6741_;
goto v_reusejp_6739_;
}
v_reusejp_6739_:
{
return v___x_6740_;
}
}
}
}
else
{
lean_object* v_a_6743_; lean_object* v___x_6745_; uint8_t v_isShared_6746_; uint8_t v_isSharedCheck_6750_; 
v_a_6743_ = lean_ctor_get(v___x_6678_, 0);
v_isSharedCheck_6750_ = !lean_is_exclusive(v___x_6678_);
if (v_isSharedCheck_6750_ == 0)
{
v___x_6745_ = v___x_6678_;
v_isShared_6746_ = v_isSharedCheck_6750_;
goto v_resetjp_6744_;
}
else
{
lean_inc(v_a_6743_);
lean_dec(v___x_6678_);
v___x_6745_ = lean_box(0);
v_isShared_6746_ = v_isSharedCheck_6750_;
goto v_resetjp_6744_;
}
v_resetjp_6744_:
{
lean_object* v___x_6748_; 
if (v_isShared_6746_ == 0)
{
v___x_6748_ = v___x_6745_;
goto v_reusejp_6747_;
}
else
{
lean_object* v_reuseFailAlloc_6749_; 
v_reuseFailAlloc_6749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6749_, 0, v_a_6743_);
v___x_6748_ = v_reuseFailAlloc_6749_;
goto v_reusejp_6747_;
}
v_reusejp_6747_:
{
return v___x_6748_;
}
}
}
}
}
}
else
{
lean_object* v_a_6753_; lean_object* v___x_6755_; uint8_t v_isShared_6756_; uint8_t v_isSharedCheck_6760_; 
v_a_6753_ = lean_ctor_get(v___x_6664_, 0);
v_isSharedCheck_6760_ = !lean_is_exclusive(v___x_6664_);
if (v_isSharedCheck_6760_ == 0)
{
v___x_6755_ = v___x_6664_;
v_isShared_6756_ = v_isSharedCheck_6760_;
goto v_resetjp_6754_;
}
else
{
lean_inc(v_a_6753_);
lean_dec(v___x_6664_);
v___x_6755_ = lean_box(0);
v_isShared_6756_ = v_isSharedCheck_6760_;
goto v_resetjp_6754_;
}
v_resetjp_6754_:
{
lean_object* v___x_6758_; 
if (v_isShared_6756_ == 0)
{
v___x_6758_ = v___x_6755_;
goto v_reusejp_6757_;
}
else
{
lean_object* v_reuseFailAlloc_6759_; 
v_reuseFailAlloc_6759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6759_, 0, v_a_6753_);
v___x_6758_ = v_reuseFailAlloc_6759_;
goto v_reusejp_6757_;
}
v_reusejp_6757_:
{
return v___x_6758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6761_, lean_object* v_a_6762_, lean_object* v_a_6763_, lean_object* v_a_6764_, lean_object* v_a_6765_, lean_object* v_a_6766_, lean_object* v_a_6767_, lean_object* v_a_6768_, lean_object* v_a_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_, lean_object* v_a_6773_){
_start:
{
lean_object* v_res_6774_; 
v_res_6774_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6761_, v_a_6762_, v_a_6763_, v_a_6764_, v_a_6765_, v_a_6766_, v_a_6767_, v_a_6768_, v_a_6769_, v_a_6770_, v_a_6771_, v_a_6772_);
lean_dec(v_a_6772_);
lean_dec_ref(v_a_6771_);
lean_dec(v_a_6770_);
lean_dec_ref(v_a_6769_);
lean_dec(v_a_6768_);
lean_dec_ref(v_a_6767_);
lean_dec(v_a_6766_);
lean_dec_ref(v_a_6765_);
lean_dec(v_a_6764_);
lean_dec(v_a_6763_);
lean_dec_ref(v_a_6762_);
lean_dec(v_passes_6761_);
return v_res_6774_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6775_, lean_object* v_msg_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_){
_start:
{
lean_object* v___x_6789_; 
v___x_6789_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6775_, v_msg_6776_, v___y_6784_, v___y_6785_, v___y_6786_, v___y_6787_);
return v___x_6789_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6790_, lean_object* v_msg_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_, lean_object* v___y_6803_){
_start:
{
lean_object* v_res_6804_; 
v_res_6804_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6790_, v_msg_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_, v___y_6802_);
lean_dec(v___y_6802_);
lean_dec_ref(v___y_6801_);
lean_dec(v___y_6800_);
lean_dec_ref(v___y_6799_);
lean_dec(v___y_6798_);
lean_dec_ref(v___y_6797_);
lean_dec(v___y_6796_);
lean_dec_ref(v___y_6795_);
lean_dec(v___y_6794_);
lean_dec(v___y_6793_);
lean_dec_ref(v___y_6792_);
return v_res_6804_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6805_, lean_object* v_x_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_, lean_object* v___y_6809_, lean_object* v___y_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_, lean_object* v___y_6816_, lean_object* v___y_6817_){
_start:
{
lean_object* v___x_6819_; 
v___x_6819_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6806_);
return v___x_6819_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6820_, lean_object* v_x_6821_, lean_object* v___y_6822_, lean_object* v___y_6823_, lean_object* v___y_6824_, lean_object* v___y_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_){
_start:
{
lean_object* v_res_6834_; 
v_res_6834_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6820_, v_x_6821_, v___y_6822_, v___y_6823_, v___y_6824_, v___y_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_);
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
return v_res_6834_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6835_, lean_object* v_as_x27_6836_, lean_object* v_b_6837_, lean_object* v_a_6838_, lean_object* v___y_6839_, lean_object* v___y_6840_, lean_object* v___y_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_, lean_object* v___y_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_){
_start:
{
lean_object* v___x_6851_; 
v___x_6851_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6836_, v_b_6837_, v___y_6839_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_, v___y_6845_, v___y_6846_, v___y_6847_, v___y_6848_, v___y_6849_);
return v___x_6851_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6852_, lean_object* v_as_x27_6853_, lean_object* v_b_6854_, lean_object* v_a_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_){
_start:
{
lean_object* v_res_6868_; 
v_res_6868_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6852_, v_as_x27_6853_, v_b_6854_, v_a_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_);
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
lean_dec(v_as_x27_6853_);
lean_dec(v_as_6852_);
return v_res_6868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6869_, lean_object* v_data_6870_, lean_object* v_ref_6871_, lean_object* v_msg_6872_, lean_object* v___y_6873_, lean_object* v___y_6874_, lean_object* v___y_6875_, lean_object* v___y_6876_, lean_object* v___y_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_, lean_object* v___y_6880_, lean_object* v___y_6881_, lean_object* v___y_6882_, lean_object* v___y_6883_){
_start:
{
lean_object* v___x_6885_; 
v___x_6885_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6869_, v_data_6870_, v_ref_6871_, v_msg_6872_, v___y_6880_, v___y_6881_, v___y_6882_, v___y_6883_);
return v___x_6885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6886_, lean_object* v_data_6887_, lean_object* v_ref_6888_, lean_object* v_msg_6889_, lean_object* v___y_6890_, lean_object* v___y_6891_, lean_object* v___y_6892_, lean_object* v___y_6893_, lean_object* v___y_6894_, lean_object* v___y_6895_, lean_object* v___y_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_, lean_object* v___y_6899_, lean_object* v___y_6900_, lean_object* v___y_6901_){
_start:
{
lean_object* v_res_6902_; 
v_res_6902_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6886_, v_data_6887_, v_ref_6888_, v_msg_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_, v___y_6894_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_, v___y_6899_, v___y_6900_);
lean_dec(v___y_6900_);
lean_dec_ref(v___y_6899_);
lean_dec(v___y_6898_);
lean_dec_ref(v___y_6897_);
lean_dec(v___y_6896_);
lean_dec_ref(v___y_6895_);
lean_dec(v___y_6894_);
lean_dec_ref(v___y_6893_);
lean_dec(v___y_6892_);
lean_dec(v___y_6891_);
lean_dec_ref(v___y_6890_);
return v_res_6902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6903_, lean_object* v_a_6904_, lean_object* v_a_6905_, lean_object* v_a_6906_, lean_object* v_a_6907_, lean_object* v_a_6908_, lean_object* v_a_6909_, lean_object* v_a_6910_, lean_object* v_a_6911_, lean_object* v_a_6912_, lean_object* v_a_6913_, lean_object* v_a_6914_){
_start:
{
lean_object* v___x_6916_; 
v___x_6916_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6903_, v_a_6904_, v_a_6905_, v_a_6906_, v_a_6907_, v_a_6908_, v_a_6909_, v_a_6910_, v_a_6911_, v_a_6912_, v_a_6913_, v_a_6914_);
if (lean_obj_tag(v___x_6916_) == 0)
{
lean_object* v_a_6917_; lean_object* v___x_6918_; lean_object* v___x_6920_; uint8_t v_isShared_6921_; uint8_t v_isSharedCheck_6925_; 
v_a_6917_ = lean_ctor_get(v___x_6916_, 0);
lean_inc(v_a_6917_);
lean_dec_ref_known(v___x_6916_, 1);
v___x_6918_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_6904_, v_a_6905_);
v_isSharedCheck_6925_ = !lean_is_exclusive(v___x_6918_);
if (v_isSharedCheck_6925_ == 0)
{
lean_object* v_unused_6926_; 
v_unused_6926_ = lean_ctor_get(v___x_6918_, 0);
lean_dec(v_unused_6926_);
v___x_6920_ = v___x_6918_;
v_isShared_6921_ = v_isSharedCheck_6925_;
goto v_resetjp_6919_;
}
else
{
lean_dec(v___x_6918_);
v___x_6920_ = lean_box(0);
v_isShared_6921_ = v_isSharedCheck_6925_;
goto v_resetjp_6919_;
}
v_resetjp_6919_:
{
lean_object* v___x_6923_; 
if (v_isShared_6921_ == 0)
{
lean_ctor_set(v___x_6920_, 0, v_a_6917_);
v___x_6923_ = v___x_6920_;
goto v_reusejp_6922_;
}
else
{
lean_object* v_reuseFailAlloc_6924_; 
v_reuseFailAlloc_6924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_a_6917_);
v___x_6923_ = v_reuseFailAlloc_6924_;
goto v_reusejp_6922_;
}
v_reusejp_6922_:
{
return v___x_6923_;
}
}
}
else
{
return v___x_6916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_, lean_object* v_a_6930_, lean_object* v_a_6931_, lean_object* v_a_6932_, lean_object* v_a_6933_, lean_object* v_a_6934_, lean_object* v_a_6935_, lean_object* v_a_6936_, lean_object* v_a_6937_, lean_object* v_a_6938_, lean_object* v_a_6939_){
_start:
{
lean_object* v_res_6940_; 
v_res_6940_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6927_, v_a_6928_, v_a_6929_, v_a_6930_, v_a_6931_, v_a_6932_, v_a_6933_, v_a_6934_, v_a_6935_, v_a_6936_, v_a_6937_, v_a_6938_);
lean_dec(v_a_6938_);
lean_dec_ref(v_a_6937_);
lean_dec(v_a_6936_);
lean_dec_ref(v_a_6935_);
lean_dec(v_a_6934_);
lean_dec_ref(v_a_6933_);
lean_dec(v_a_6932_);
lean_dec_ref(v_a_6931_);
lean_dec(v_a_6930_);
lean_dec(v_a_6929_);
lean_dec_ref(v_a_6928_);
lean_dec(v_passes_6927_);
return v_res_6940_;
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
