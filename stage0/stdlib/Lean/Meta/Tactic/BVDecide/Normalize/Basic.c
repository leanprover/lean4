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
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_instExceptToTraceResultBool___redArg___lam__0___boxed(lean_object*);
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
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v_target_887_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
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
v___x_900_ = v_reuseFailAlloc_903_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_st_ref_put(v_a_888_, v___x_900_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_898_);
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
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_box(0);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 2, v_target_910_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
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
v___x_933_ = v_reuseFailAlloc_936_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_st_ref_put(v_a_912_, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_931_);
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
v___x_953_ = l_instMonadControlReaderT___redArg();
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1(void){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2(void){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_instMonadEIO___redArg();
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
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_mvarId_1058_; lean_object* v___x_1059_; lean_object* v___x_5100__overap_1060_; lean_object* v___x_1061_; 
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
v___x_5100__overap_1060_ = l_Lean_MVarId_withContext___redArg(v___x_1015_, v___x_1057_, v_mvarId_1058_, v___x_1059_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_a_966_);
lean_inc_ref(v_a_965_);
lean_inc(v_a_964_);
v___x_1061_ = lean_apply_10(v___x_5100__overap_1060_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
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
lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1069_; 
v_fst_1066_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_fst_1066_);
v_snd_1067_ = lean_ctor_get(v_a_1062_, 1);
lean_inc(v_snd_1067_);
lean_dec(v_a_1062_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_snd_1067_);
v___x_1069_ = v___x_978_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_snd_1067_);
v___x_1069_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; lean_object* v_caches_1071_; lean_object* v_typeAnalysis_1072_; lean_object* v_hypotheses_1073_; uint8_t v_didChange_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1086_; 
v___x_1070_ = lean_st_ref_take(v_a_963_);
v_caches_1071_ = lean_ctor_get(v___x_1070_, 0);
v_typeAnalysis_1072_ = lean_ctor_get(v___x_1070_, 1);
v_hypotheses_1073_ = lean_ctor_get(v___x_1070_, 3);
v_didChange_1074_ = lean_ctor_get_uint8(v___x_1070_, sizeof(void*)*4);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v___x_1070_, 2);
lean_dec(v_unused_1087_);
v___x_1076_ = v___x_1070_;
v_isShared_1077_ = v_isSharedCheck_1086_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_hypotheses_1073_);
lean_inc(v_typeAnalysis_1072_);
lean_inc(v_caches_1071_);
lean_dec(v___x_1070_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1086_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 2, v___x_1069_);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_caches_1071_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_typeAnalysis_1072_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_hypotheses_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*4, v_didChange_1074_);
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
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_mvarId_1218_; lean_object* v___x_1219_; lean_object* v___x_5171__overap_1220_; lean_object* v___x_1221_; 
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
v___x_5171__overap_1220_ = l_Lean_MVarId_withContext___redArg(v___x_1175_, v___x_1217_, v_mvarId_1218_, v___x_1219_);
lean_inc(v_a_1132_);
lean_inc_ref(v_a_1131_);
lean_inc(v_a_1130_);
lean_inc_ref(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc_ref(v_a_1127_);
lean_inc(v_a_1126_);
lean_inc_ref(v_a_1125_);
lean_inc(v_a_1124_);
v___x_1221_ = lean_apply_10(v___x_5171__overap_1220_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, lean_box(0));
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
lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___x_1229_; 
v_fst_1226_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_fst_1226_);
v_snd_1227_ = lean_ctor_get(v_a_1222_, 1);
lean_inc(v_snd_1227_);
lean_dec(v_a_1222_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_snd_1227_);
v___x_1229_ = v___x_1138_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_snd_1227_);
v___x_1229_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v_caches_1231_; lean_object* v_typeAnalysis_1232_; lean_object* v_hypotheses_1233_; uint8_t v_didChange_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1246_; 
v___x_1230_ = lean_st_ref_take(v_a_1123_);
v_caches_1231_ = lean_ctor_get(v___x_1230_, 0);
v_typeAnalysis_1232_ = lean_ctor_get(v___x_1230_, 1);
v_hypotheses_1233_ = lean_ctor_get(v___x_1230_, 3);
v_didChange_1234_ = lean_ctor_get_uint8(v___x_1230_, sizeof(void*)*4);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1230_, 2);
lean_dec(v_unused_1247_);
v___x_1236_ = v___x_1230_;
v_isShared_1237_ = v_isSharedCheck_1246_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_hypotheses_1233_);
lean_inc(v_typeAnalysis_1232_);
lean_inc(v_caches_1231_);
lean_dec(v___x_1230_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1246_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 2, v___x_1229_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_caches_1231_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_typeAnalysis_1232_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_hypotheses_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1245_, sizeof(void*)*4, v_didChange_1234_);
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
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v_target_1435_; 
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_st_ref_get(v_a_1415_);
v_target_1435_ = lean_ctor_get(v___x_1434_, 2);
lean_inc_ref(v_target_1435_);
lean_dec(v___x_1434_);
if (lean_obj_tag(v_target_1435_) == 1)
{
lean_object* v_goal_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1477_; 
lean_del_object(v___x_1431_);
v_goal_1436_ = lean_ctor_get(v_target_1435_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_target_1435_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1438_ = v_target_1435_;
v_isShared_1439_ = v_isSharedCheck_1477_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_goal_1436_);
lean_dec(v_target_1435_);
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
lean_object* v_snd_1447_; lean_object* v___x_1449_; 
v_snd_1447_ = lean_ctor_get(v_a_1443_, 1);
lean_inc(v_snd_1447_);
lean_dec(v_a_1443_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v_snd_1447_);
v___x_1449_ = v___x_1438_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_snd_1447_);
v___x_1449_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v_caches_1451_; lean_object* v_typeAnalysis_1452_; lean_object* v_hypotheses_1453_; uint8_t v_didChange_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1465_; 
v___x_1450_ = lean_st_ref_take(v_a_1415_);
v_caches_1451_ = lean_ctor_get(v___x_1450_, 0);
v_typeAnalysis_1452_ = lean_ctor_get(v___x_1450_, 1);
v_hypotheses_1453_ = lean_ctor_get(v___x_1450_, 3);
v_didChange_1454_ = lean_ctor_get_uint8(v___x_1450_, sizeof(void*)*4);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1450_, 2);
lean_dec(v_unused_1466_);
v___x_1456_ = v___x_1450_;
v_isShared_1457_ = v_isSharedCheck_1465_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_hypotheses_1453_);
lean_inc(v_typeAnalysis_1452_);
lean_inc(v_caches_1451_);
lean_dec(v___x_1450_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1465_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 2, v___x_1449_);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_caches_1451_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_typeAnalysis_1452_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_hypotheses_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*4, v_didChange_1454_);
v___x_1459_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_st_ref_put(v_a_1415_, v___x_1459_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1433_);
v___x_1462_ = v___x_1445_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1433_);
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
lean_dec_ref(v_target_1435_);
lean_dec_ref(v_falseProof_1414_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1479_ = v___x_1431_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1433_);
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
lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1575_; 
v___x_1572_ = lean_box(0);
v___x_1573_ = 0;
if (v_isShared_1571_ == 0)
{
v___x_1575_ = v___x_1570_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_caches_1565_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_typeAnalysis_1566_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_target_1567_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_hypotheses_1568_);
v___x_1575_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*4, v___x_1573_);
v___x_1576_ = lean_st_ref_put(v_a_1562_, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1572_);
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
lean_object* v___x_1603_; uint8_t v___x_1604_; lean_object* v___x_1606_; 
v___x_1603_ = lean_box(0);
v___x_1604_ = 0;
if (v_isShared_1602_ == 0)
{
v___x_1606_ = v___x_1601_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_caches_1596_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_typeAnalysis_1597_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_target_1598_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_hypotheses_1599_);
v___x_1606_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*4, v___x_1604_);
v___x_1607_ = lean_st_ref_put(v_a_1584_, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1603_);
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
lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1637_; 
v___x_1634_ = lean_box(0);
v___x_1635_ = 1;
if (v_isShared_1633_ == 0)
{
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_caches_1627_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_typeAnalysis_1628_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_target_1629_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_hypotheses_1630_);
v___x_1637_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*4, v___x_1635_);
v___x_1638_ = lean_st_ref_put(v_a_1624_, v___x_1637_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1634_);
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
lean_object* v___x_1665_; uint8_t v___x_1666_; lean_object* v___x_1668_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = 1;
if (v_isShared_1664_ == 0)
{
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_caches_1658_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_typeAnalysis_1659_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_target_1660_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_hypotheses_1661_);
v___x_1668_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*4, v___x_1666_);
v___x_1669_ = lean_st_ref_put(v_a_1646_, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1665_);
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
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_box(0);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v_caches_1722_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
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
v___x_1735_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_st_ref_put(v_a_1723_, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1733_);
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
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = lean_box(0);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v_caches_1745_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
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
v___x_1768_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_st_ref_put(v_a_1747_, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1766_);
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
v___x_1788_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1807_ = lean_box(0);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1798_);
v___x_1809_ = v___x_1805_;
goto v_reusejp_1808_;
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
v___x_1809_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_st_ref_put(v_a_1794_, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1807_);
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
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v_typeAnalysis_1894_; lean_object* v_interestingStructures_1895_; lean_object* v_uninteresting_1896_; uint8_t v___x_1897_; 
v___x_1891_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1892_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1893_ = lean_st_ref_get(v_a_1889_);
v_typeAnalysis_1894_ = lean_ctor_get(v___x_1893_, 1);
lean_inc_ref(v_typeAnalysis_1894_);
lean_dec(v___x_1893_);
v_interestingStructures_1895_ = lean_ctor_get(v_typeAnalysis_1894_, 0);
lean_inc_ref(v_interestingStructures_1895_);
v_uninteresting_1896_ = lean_ctor_get(v_typeAnalysis_1894_, 3);
lean_inc_ref(v_uninteresting_1896_);
lean_dec_ref(v_typeAnalysis_1894_);
lean_inc(v_n_1888_);
v___x_1897_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1891_, v___x_1892_, v_uninteresting_1896_, v_n_1888_);
lean_dec_ref(v_uninteresting_1896_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; 
v___x_1898_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1891_, v___x_1892_, v_interestingStructures_1895_, v_n_1888_);
lean_dec_ref(v_interestingStructures_1895_);
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
lean_dec_ref(v_interestingStructures_1895_);
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
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_typeAnalysis_1926_; lean_object* v_interestingStructures_1927_; lean_object* v_uninteresting_1928_; uint8_t v___x_1929_; 
v___x_1923_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1924_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1925_ = lean_st_ref_get(v_a_1912_);
v_typeAnalysis_1926_ = lean_ctor_get(v___x_1925_, 1);
lean_inc_ref(v_typeAnalysis_1926_);
lean_dec(v___x_1925_);
v_interestingStructures_1927_ = lean_ctor_get(v_typeAnalysis_1926_, 0);
lean_inc_ref(v_interestingStructures_1927_);
v_uninteresting_1928_ = lean_ctor_get(v_typeAnalysis_1926_, 3);
lean_inc_ref(v_uninteresting_1928_);
lean_dec_ref(v_typeAnalysis_1926_);
lean_inc(v_n_1910_);
v___x_1929_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1923_, v___x_1924_, v_uninteresting_1928_, v_n_1910_);
lean_dec_ref(v_uninteresting_1928_);
if (v___x_1929_ == 0)
{
uint8_t v___x_1930_; 
v___x_1930_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1923_, v___x_1924_, v_interestingStructures_1927_, v_n_1910_);
lean_dec_ref(v_interestingStructures_1927_);
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
lean_dec_ref(v_interestingStructures_1927_);
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
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_apply_1(v_f_1952_, v_typeAnalysis_1957_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___x_1965_);
v___x_1967_ = v___x_1962_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_caches_1956_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_target_1958_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_hypotheses_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1970_, sizeof(void*)*4, v_didChange_1960_);
v___x_1967_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_st_ref_put(v_a_1953_, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1964_);
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
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = lean_apply_1(v_f_1976_, v_typeAnalysis_1991_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v___x_1999_);
v___x_2001_ = v___x_1996_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_caches_1990_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_target_1992_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_hypotheses_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2004_, sizeof(void*)*4, v_didChange_1994_);
v___x_2001_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_st_ref_put(v_a_1978_, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1998_);
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
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v_typeAnalysis_2026_; lean_object* v_caches_2027_; lean_object* v_target_2028_; lean_object* v_hypotheses_2029_; uint8_t v_didChange_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2052_; 
v___x_2023_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2024_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2025_ = lean_st_ref_take(v_a_2021_);
v_typeAnalysis_2026_ = lean_ctor_get(v___x_2025_, 1);
v_caches_2027_ = lean_ctor_get(v___x_2025_, 0);
v_target_2028_ = lean_ctor_get(v___x_2025_, 2);
v_hypotheses_2029_ = lean_ctor_get(v___x_2025_, 3);
v_didChange_2030_ = lean_ctor_get_uint8(v___x_2025_, sizeof(void*)*4);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2032_ = v___x_2025_;
v_isShared_2033_ = v_isSharedCheck_2052_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_hypotheses_2029_);
lean_inc(v_target_2028_);
lean_inc(v_typeAnalysis_2026_);
lean_inc(v_caches_2027_);
lean_dec(v___x_2025_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2052_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_interestingStructures_2034_; lean_object* v_interestingEnums_2035_; lean_object* v_interestingMatchers_2036_; lean_object* v_uninteresting_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2051_; 
v_interestingStructures_2034_ = lean_ctor_get(v_typeAnalysis_2026_, 0);
v_interestingEnums_2035_ = lean_ctor_get(v_typeAnalysis_2026_, 1);
v_interestingMatchers_2036_ = lean_ctor_get(v_typeAnalysis_2026_, 2);
v_uninteresting_2037_ = lean_ctor_get(v_typeAnalysis_2026_, 3);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_typeAnalysis_2026_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2039_ = v_typeAnalysis_2026_;
v_isShared_2040_ = v_isSharedCheck_2051_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_uninteresting_2037_);
lean_inc(v_interestingMatchers_2036_);
lean_inc(v_interestingEnums_2035_);
lean_inc(v_interestingStructures_2034_);
lean_dec(v_typeAnalysis_2026_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2051_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2023_, v___x_2024_, v_interestingStructures_2034_, v_n_2020_, v___x_2041_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2042_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_interestingEnums_2035_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_interestingMatchers_2036_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_uninteresting_2037_);
v___x_2044_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v___x_2044_);
v___x_2046_ = v___x_2032_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_caches_2027_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_target_2028_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_hypotheses_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*4, v_didChange_2030_);
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
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_typeAnalysis_2073_; lean_object* v_caches_2074_; lean_object* v_target_2075_; lean_object* v_hypotheses_2076_; uint8_t v_didChange_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2099_; 
v___x_2070_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2071_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2072_ = lean_st_ref_take(v_a_2059_);
v_typeAnalysis_2073_ = lean_ctor_get(v___x_2072_, 1);
v_caches_2074_ = lean_ctor_get(v___x_2072_, 0);
v_target_2075_ = lean_ctor_get(v___x_2072_, 2);
v_hypotheses_2076_ = lean_ctor_get(v___x_2072_, 3);
v_didChange_2077_ = lean_ctor_get_uint8(v___x_2072_, sizeof(void*)*4);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2079_ = v___x_2072_;
v_isShared_2080_ = v_isSharedCheck_2099_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_hypotheses_2076_);
lean_inc(v_target_2075_);
lean_inc(v_typeAnalysis_2073_);
lean_inc(v_caches_2074_);
lean_dec(v___x_2072_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2099_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v_interestingStructures_2081_; lean_object* v_interestingEnums_2082_; lean_object* v_interestingMatchers_2083_; lean_object* v_uninteresting_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2098_; 
v_interestingStructures_2081_ = lean_ctor_get(v_typeAnalysis_2073_, 0);
v_interestingEnums_2082_ = lean_ctor_get(v_typeAnalysis_2073_, 1);
v_interestingMatchers_2083_ = lean_ctor_get(v_typeAnalysis_2073_, 2);
v_uninteresting_2084_ = lean_ctor_get(v_typeAnalysis_2073_, 3);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_typeAnalysis_2073_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2086_ = v_typeAnalysis_2073_;
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_uninteresting_2084_);
lean_inc(v_interestingMatchers_2083_);
lean_inc(v_interestingEnums_2082_);
lean_inc(v_interestingStructures_2081_);
lean_dec(v_typeAnalysis_2073_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2088_ = lean_box(0);
v___x_2089_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2070_, v___x_2071_, v_interestingStructures_2081_, v_n_2057_, v___x_2088_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2089_);
v___x_2091_ = v___x_2086_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_interestingEnums_2082_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_interestingMatchers_2083_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_uninteresting_2084_);
v___x_2091_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_2091_);
v___x_2093_ = v___x_2079_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_caches_2074_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_target_2075_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_hypotheses_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2096_, sizeof(void*)*4, v_didChange_2077_);
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
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_typeAnalysis_2120_; lean_object* v_caches_2121_; lean_object* v_target_2122_; lean_object* v_hypotheses_2123_; uint8_t v_didChange_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2146_; 
v___x_2117_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2118_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2119_ = lean_st_ref_take(v_a_2115_);
v_typeAnalysis_2120_ = lean_ctor_get(v___x_2119_, 1);
v_caches_2121_ = lean_ctor_get(v___x_2119_, 0);
v_target_2122_ = lean_ctor_get(v___x_2119_, 2);
v_hypotheses_2123_ = lean_ctor_get(v___x_2119_, 3);
v_didChange_2124_ = lean_ctor_get_uint8(v___x_2119_, sizeof(void*)*4);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2126_ = v___x_2119_;
v_isShared_2127_ = v_isSharedCheck_2146_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_hypotheses_2123_);
lean_inc(v_target_2122_);
lean_inc(v_typeAnalysis_2120_);
lean_inc(v_caches_2121_);
lean_dec(v___x_2119_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2146_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_interestingStructures_2128_; lean_object* v_interestingEnums_2129_; lean_object* v_interestingMatchers_2130_; lean_object* v_uninteresting_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2145_; 
v_interestingStructures_2128_ = lean_ctor_get(v_typeAnalysis_2120_, 0);
v_interestingEnums_2129_ = lean_ctor_get(v_typeAnalysis_2120_, 1);
v_interestingMatchers_2130_ = lean_ctor_get(v_typeAnalysis_2120_, 2);
v_uninteresting_2131_ = lean_ctor_get(v_typeAnalysis_2120_, 3);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_typeAnalysis_2120_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2133_ = v_typeAnalysis_2120_;
v_isShared_2134_ = v_isSharedCheck_2145_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_uninteresting_2131_);
lean_inc(v_interestingMatchers_2130_);
lean_inc(v_interestingEnums_2129_);
lean_inc(v_interestingStructures_2128_);
lean_dec(v_typeAnalysis_2120_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2145_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2135_ = lean_box(0);
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2117_, v___x_2118_, v_interestingEnums_2129_, v_n_2114_, v___x_2135_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v___x_2136_);
v___x_2138_ = v___x_2133_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_interestingStructures_2128_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_interestingMatchers_2130_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_uninteresting_2131_);
v___x_2138_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 1, v___x_2138_);
v___x_2140_ = v___x_2126_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_caches_2121_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_target_2122_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_hypotheses_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*4, v_didChange_2124_);
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
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v_typeAnalysis_2167_; lean_object* v_caches_2168_; lean_object* v_target_2169_; lean_object* v_hypotheses_2170_; uint8_t v_didChange_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2193_; 
v___x_2164_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2165_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2166_ = lean_st_ref_take(v_a_2153_);
v_typeAnalysis_2167_ = lean_ctor_get(v___x_2166_, 1);
v_caches_2168_ = lean_ctor_get(v___x_2166_, 0);
v_target_2169_ = lean_ctor_get(v___x_2166_, 2);
v_hypotheses_2170_ = lean_ctor_get(v___x_2166_, 3);
v_didChange_2171_ = lean_ctor_get_uint8(v___x_2166_, sizeof(void*)*4);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2173_ = v___x_2166_;
v_isShared_2174_ = v_isSharedCheck_2193_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_hypotheses_2170_);
lean_inc(v_target_2169_);
lean_inc(v_typeAnalysis_2167_);
lean_inc(v_caches_2168_);
lean_dec(v___x_2166_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2193_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_interestingStructures_2175_; lean_object* v_interestingEnums_2176_; lean_object* v_interestingMatchers_2177_; lean_object* v_uninteresting_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2192_; 
v_interestingStructures_2175_ = lean_ctor_get(v_typeAnalysis_2167_, 0);
v_interestingEnums_2176_ = lean_ctor_get(v_typeAnalysis_2167_, 1);
v_interestingMatchers_2177_ = lean_ctor_get(v_typeAnalysis_2167_, 2);
v_uninteresting_2178_ = lean_ctor_get(v_typeAnalysis_2167_, 3);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_typeAnalysis_2167_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2180_ = v_typeAnalysis_2167_;
v_isShared_2181_ = v_isSharedCheck_2192_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_uninteresting_2178_);
lean_inc(v_interestingMatchers_2177_);
lean_inc(v_interestingEnums_2176_);
lean_inc(v_interestingStructures_2175_);
lean_dec(v_typeAnalysis_2167_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2192_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2182_ = lean_box(0);
v___x_2183_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2164_, v___x_2165_, v_interestingEnums_2176_, v_n_2151_, v___x_2182_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 1, v___x_2183_);
v___x_2185_ = v___x_2180_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_interestingStructures_2175_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_interestingMatchers_2177_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_uninteresting_2178_);
v___x_2185_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2187_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v___x_2185_);
v___x_2187_ = v___x_2173_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_caches_2168_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_target_2169_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_hypotheses_2170_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*4, v_didChange_2171_);
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
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v_typeAnalysis_2215_; lean_object* v_caches_2216_; lean_object* v_target_2217_; lean_object* v_hypotheses_2218_; uint8_t v_didChange_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2241_; 
v___x_2212_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2213_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2214_ = lean_st_ref_take(v_a_2210_);
v_typeAnalysis_2215_ = lean_ctor_get(v___x_2214_, 1);
v_caches_2216_ = lean_ctor_get(v___x_2214_, 0);
v_target_2217_ = lean_ctor_get(v___x_2214_, 2);
v_hypotheses_2218_ = lean_ctor_get(v___x_2214_, 3);
v_didChange_2219_ = lean_ctor_get_uint8(v___x_2214_, sizeof(void*)*4);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2221_ = v___x_2214_;
v_isShared_2222_ = v_isSharedCheck_2241_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_hypotheses_2218_);
lean_inc(v_target_2217_);
lean_inc(v_typeAnalysis_2215_);
lean_inc(v_caches_2216_);
lean_dec(v___x_2214_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2241_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v_interestingStructures_2223_; lean_object* v_interestingEnums_2224_; lean_object* v_interestingMatchers_2225_; lean_object* v_uninteresting_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2240_; 
v_interestingStructures_2223_ = lean_ctor_get(v_typeAnalysis_2215_, 0);
v_interestingEnums_2224_ = lean_ctor_get(v_typeAnalysis_2215_, 1);
v_interestingMatchers_2225_ = lean_ctor_get(v_typeAnalysis_2215_, 2);
v_uninteresting_2226_ = lean_ctor_get(v_typeAnalysis_2215_, 3);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_typeAnalysis_2215_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2228_ = v_typeAnalysis_2215_;
v_isShared_2229_ = v_isSharedCheck_2240_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_uninteresting_2226_);
lean_inc(v_interestingMatchers_2225_);
lean_inc(v_interestingEnums_2224_);
lean_inc(v_interestingStructures_2223_);
lean_dec(v_typeAnalysis_2215_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2240_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2230_ = lean_box(0);
v___x_2231_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2212_, v___x_2213_, v_interestingMatchers_2225_, v_n_2208_, v_k_2209_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 2, v___x_2231_);
v___x_2233_ = v___x_2228_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_interestingStructures_2223_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_interestingEnums_2224_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_uninteresting_2226_);
v___x_2233_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v___x_2233_);
v___x_2235_ = v___x_2221_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_caches_2216_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_target_2217_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_hypotheses_2218_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*4, v_didChange_2219_);
v___x_2235_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_st_ref_put(v_a_2210_, v___x_2235_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2230_);
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
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_typeAnalysis_2264_; lean_object* v_caches_2265_; lean_object* v_target_2266_; lean_object* v_hypotheses_2267_; uint8_t v_didChange_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2290_; 
v___x_2261_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2262_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2263_ = lean_st_ref_take(v_a_2250_);
v_typeAnalysis_2264_ = lean_ctor_get(v___x_2263_, 1);
v_caches_2265_ = lean_ctor_get(v___x_2263_, 0);
v_target_2266_ = lean_ctor_get(v___x_2263_, 2);
v_hypotheses_2267_ = lean_ctor_get(v___x_2263_, 3);
v_didChange_2268_ = lean_ctor_get_uint8(v___x_2263_, sizeof(void*)*4);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2270_ = v___x_2263_;
v_isShared_2271_ = v_isSharedCheck_2290_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_hypotheses_2267_);
lean_inc(v_target_2266_);
lean_inc(v_typeAnalysis_2264_);
lean_inc(v_caches_2265_);
lean_dec(v___x_2263_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2290_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v_interestingStructures_2272_; lean_object* v_interestingEnums_2273_; lean_object* v_interestingMatchers_2274_; lean_object* v_uninteresting_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2289_; 
v_interestingStructures_2272_ = lean_ctor_get(v_typeAnalysis_2264_, 0);
v_interestingEnums_2273_ = lean_ctor_get(v_typeAnalysis_2264_, 1);
v_interestingMatchers_2274_ = lean_ctor_get(v_typeAnalysis_2264_, 2);
v_uninteresting_2275_ = lean_ctor_get(v_typeAnalysis_2264_, 3);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_typeAnalysis_2264_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2277_ = v_typeAnalysis_2264_;
v_isShared_2278_ = v_isSharedCheck_2289_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_uninteresting_2275_);
lean_inc(v_interestingMatchers_2274_);
lean_inc(v_interestingEnums_2273_);
lean_inc(v_interestingStructures_2272_);
lean_dec(v_typeAnalysis_2264_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2289_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2261_, v___x_2262_, v_interestingMatchers_2274_, v_n_2247_, v_k_2248_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 2, v___x_2280_);
v___x_2282_ = v___x_2277_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_interestingStructures_2272_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_interestingEnums_2273_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_uninteresting_2275_);
v___x_2282_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2284_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v___x_2282_);
v___x_2284_ = v___x_2270_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_caches_2265_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_target_2266_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_hypotheses_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2287_, sizeof(void*)*4, v_didChange_2268_);
v___x_2284_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_st_ref_put(v_a_2250_, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2279_);
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
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_typeAnalysis_2312_; lean_object* v_caches_2313_; lean_object* v_target_2314_; lean_object* v_hypotheses_2315_; uint8_t v_didChange_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2338_; 
v___x_2309_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2310_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2311_ = lean_st_ref_take(v_a_2307_);
v_typeAnalysis_2312_ = lean_ctor_get(v___x_2311_, 1);
v_caches_2313_ = lean_ctor_get(v___x_2311_, 0);
v_target_2314_ = lean_ctor_get(v___x_2311_, 2);
v_hypotheses_2315_ = lean_ctor_get(v___x_2311_, 3);
v_didChange_2316_ = lean_ctor_get_uint8(v___x_2311_, sizeof(void*)*4);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2318_ = v___x_2311_;
v_isShared_2319_ = v_isSharedCheck_2338_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_hypotheses_2315_);
lean_inc(v_target_2314_);
lean_inc(v_typeAnalysis_2312_);
lean_inc(v_caches_2313_);
lean_dec(v___x_2311_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2338_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_interestingStructures_2320_; lean_object* v_interestingEnums_2321_; lean_object* v_interestingMatchers_2322_; lean_object* v_uninteresting_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2337_; 
v_interestingStructures_2320_ = lean_ctor_get(v_typeAnalysis_2312_, 0);
v_interestingEnums_2321_ = lean_ctor_get(v_typeAnalysis_2312_, 1);
v_interestingMatchers_2322_ = lean_ctor_get(v_typeAnalysis_2312_, 2);
v_uninteresting_2323_ = lean_ctor_get(v_typeAnalysis_2312_, 3);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_typeAnalysis_2312_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2325_ = v_typeAnalysis_2312_;
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_uninteresting_2323_);
lean_inc(v_interestingMatchers_2322_);
lean_inc(v_interestingEnums_2321_);
lean_inc(v_interestingStructures_2320_);
lean_dec(v_typeAnalysis_2312_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = lean_box(0);
v___x_2328_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2309_, v___x_2310_, v_uninteresting_2323_, v_n_2306_, v___x_2327_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 3, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_interestingStructures_2320_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_interestingEnums_2321_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_interestingMatchers_2322_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 1, v___x_2330_);
v___x_2332_ = v___x_2318_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_caches_2313_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_target_2314_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_hypotheses_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*4, v_didChange_2316_);
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
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_typeAnalysis_2359_; lean_object* v_caches_2360_; lean_object* v_target_2361_; lean_object* v_hypotheses_2362_; uint8_t v_didChange_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2385_; 
v___x_2356_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2357_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2358_ = lean_st_ref_take(v_a_2345_);
v_typeAnalysis_2359_ = lean_ctor_get(v___x_2358_, 1);
v_caches_2360_ = lean_ctor_get(v___x_2358_, 0);
v_target_2361_ = lean_ctor_get(v___x_2358_, 2);
v_hypotheses_2362_ = lean_ctor_get(v___x_2358_, 3);
v_didChange_2363_ = lean_ctor_get_uint8(v___x_2358_, sizeof(void*)*4);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2365_ = v___x_2358_;
v_isShared_2366_ = v_isSharedCheck_2385_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_hypotheses_2362_);
lean_inc(v_target_2361_);
lean_inc(v_typeAnalysis_2359_);
lean_inc(v_caches_2360_);
lean_dec(v___x_2358_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2385_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v_interestingStructures_2367_; lean_object* v_interestingEnums_2368_; lean_object* v_interestingMatchers_2369_; lean_object* v_uninteresting_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2384_; 
v_interestingStructures_2367_ = lean_ctor_get(v_typeAnalysis_2359_, 0);
v_interestingEnums_2368_ = lean_ctor_get(v_typeAnalysis_2359_, 1);
v_interestingMatchers_2369_ = lean_ctor_get(v_typeAnalysis_2359_, 2);
v_uninteresting_2370_ = lean_ctor_get(v_typeAnalysis_2359_, 3);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_typeAnalysis_2359_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2372_ = v_typeAnalysis_2359_;
v_isShared_2373_ = v_isSharedCheck_2384_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_uninteresting_2370_);
lean_inc(v_interestingMatchers_2369_);
lean_inc(v_interestingEnums_2368_);
lean_inc(v_interestingStructures_2367_);
lean_dec(v_typeAnalysis_2359_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2384_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2374_ = lean_box(0);
v___x_2375_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2356_, v___x_2357_, v_uninteresting_2370_, v_n_2343_, v___x_2374_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 3, v___x_2375_);
v___x_2377_ = v___x_2372_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_interestingStructures_2367_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_interestingEnums_2368_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v_interestingMatchers_2369_);
lean_ctor_set(v_reuseFailAlloc_2383_, 3, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 1, v___x_2377_);
v___x_2379_ = v___x_2365_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_caches_2360_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_target_2361_);
lean_ctor_set(v_reuseFailAlloc_2382_, 3, v_hypotheses_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2382_, sizeof(void*)*4, v_didChange_2363_);
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
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_array_push(v_hypotheses_2727_, v_hyp_2708_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 3, v___x_2733_);
v___x_2735_ = v___x_2730_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_caches_2724_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_typeAnalysis_2725_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_target_2726_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v___x_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, sizeof(void*)*4, v_didChange_2728_);
v___x_2735_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_st_ref_put(v___y_2722_, v___x_2735_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2732_);
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
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v_toCold_2789_; lean_object* v_options_2790_; uint8_t v_hasTrace_2791_; 
v___x_2780_ = l_StateRefT_x27_instMonad___redArg(v___x_2779_);
v___x_2781_ = l_ReaderT_instMonad___redArg(v___x_2780_);
v___x_2782_ = l_StateRefT_x27_instMonad___redArg(v___x_2781_);
v___x_2783_ = l_ReaderT_instMonad___redArg(v___x_2782_);
v___x_2784_ = l_ReaderT_instMonad___redArg(v___x_2783_);
v___x_2785_ = l_StateRefT_x27_instMonad___redArg(v___x_2784_);
v___x_2786_ = l_ReaderT_instMonad___redArg(v___x_2785_);
v___x_2787_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2788_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toCold_2789_ = lean_ctor_get(v_a_2718_, 0);
v_options_2790_ = lean_ctor_get(v_toCold_2789_, 2);
v_hasTrace_2791_ = lean_ctor_get_uint8(v_options_2790_, sizeof(void*)*1);
if (v_hasTrace_2791_ == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_object* v_toMonadRef_2792_; lean_object* v_inheritedTraceOptions_2793_; lean_object* v_cls_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v_toMonadRef_2792_ = lean_ctor_get(v___x_2788_, 0);
v_inheritedTraceOptions_2793_ = lean_ctor_get(v_toCold_2789_, 11);
v_cls_2794_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2795_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2793_, v_options_2790_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_dec_ref(v___x_2786_);
v___y_2722_ = v_a_2710_;
goto v___jp_2721_;
}
else
{
lean_object* v_type_2797_; lean_object* v___f_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_5398__overap_2802_; lean_object* v___x_2803_; 
v_type_2797_ = lean_ctor_get(v_hyp_2708_, 1);
v___f_2798_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_2799_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_2797_);
v___x_2800_ = l_Lean_MessageData_ofExpr(v_type_2797_);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
lean_inc_ref(v_toMonadRef_2792_);
v___x_5398__overap_2802_ = l_Lean_addTrace___redArg(v___x_2786_, v___x_2787_, v_toMonadRef_2792_, v___f_2798_, v_cls_2794_, v___x_2801_);
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
v___x_2803_ = lean_apply_12(v___x_5398__overap_2802_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, lean_box(0));
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
lean_object* v_toCold_2845_; lean_object* v_options_2846_; uint8_t v_hasTrace_2847_; 
v_toCold_2845_ = lean_ctor_get(v___y_2839_, 0);
v_options_2846_ = lean_ctor_get(v_toCold_2845_, 2);
v_hasTrace_2847_ = lean_ctor_get_uint8(v_options_2846_, sizeof(void*)*1);
if (v_hasTrace_2847_ == 0)
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
lean_object* v_inheritedTraceOptions_2848_; lean_object* v_cls_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_inheritedTraceOptions_2848_ = lean_ctor_get(v_toCold_2845_, 11);
v_cls_2849_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2850_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2851_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2848_, v_options_2846_, v___x_2850_);
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
lean_object* v_type_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_6389__overap_2856_; lean_object* v___x_2857_; 
v_type_2852_ = lean_ctor_get(v___y_2829_, 1);
lean_inc_ref(v_type_2852_);
lean_dec_ref(v___y_2829_);
v___x_2853_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2854_ = l_Lean_MessageData_ofExpr(v_type_2852_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_6389__overap_2856_ = l_Lean_addTrace___redArg(v___x_2824_, v___x_2825_, v_toMonadRef_2826_, v___f_2827_, v_cls_2849_, v___x_2855_);
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
v___x_2857_ = lean_apply_12(v___x_6389__overap_2856_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, lean_box(0));
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
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2900_ = lean_box(0);
v___x_2901_ = l_Array_append___redArg(v_hypotheses_2895_, v_hyps_2877_);
lean_dec_ref(v_hyps_2877_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 3, v___x_2901_);
v___x_2903_ = v___x_2898_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_caches_2892_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_typeAnalysis_2893_);
lean_ctor_set(v_reuseFailAlloc_2906_, 2, v_target_2894_);
lean_ctor_set(v_reuseFailAlloc_2906_, 3, v___x_2901_);
lean_ctor_set_uint8(v_reuseFailAlloc_2906_, sizeof(void*)*4, v_didChange_2896_);
v___x_2903_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_st_ref_put(v_a_2879_, v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2900_);
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
size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_6041__overap_2969_; lean_object* v___x_2970_; 
v___x_2967_ = ((size_t)0ULL);
v___x_2968_ = lean_usize_of_nat(v___x_2961_);
lean_inc_ref(v_hyps_2877_);
v___x_6041__overap_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2956_, v___f_2964_, v_hyps_2877_, v___x_2967_, v___x_2968_, v___x_2965_);
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
v___x_2970_ = lean_apply_12(v___x_6041__overap_2969_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, lean_box(0));
v___y_2909_ = v___x_2970_;
goto v___jp_2908_;
}
}
else
{
size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_6044__overap_2973_; lean_object* v___x_2974_; 
v___x_2971_ = ((size_t)0ULL);
v___x_2972_ = lean_usize_of_nat(v___x_2961_);
lean_inc_ref(v_hyps_2877_);
v___x_6044__overap_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2956_, v___f_2964_, v_hyps_2877_, v___x_2971_, v___x_2972_, v___x_2965_);
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
v___x_2974_ = lean_apply_12(v___x_6044__overap_2973_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, lean_box(0));
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
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = lean_box(0);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 3, v_hyps_3031_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
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
v___x_3054_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_st_ref_put(v___y_3033_, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3052_);
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
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3098_ = lean_box(0);
v___x_3099_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 3, v___x_3099_);
v___x_3101_ = v___x_3096_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_caches_3091_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_typeAnalysis_3092_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_target_3093_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v___x_3099_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*4, v_didChange_3094_);
v___x_3101_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_st_ref_put(v___y_3079_, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3098_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_inst_3137_, lean_object* v_toPure_3138_, lean_object* v_cls_3139_, lean_object* v_toBind_3140_, lean_object* v_____do__lift_3141_){
_start:
{
lean_object* v_getOptionsUnrestricted_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; 
v_getOptionsUnrestricted_3142_ = lean_ctor_get(v_inst_3137_, 1);
lean_inc(v_getOptionsUnrestricted_3142_);
lean_dec_ref(v_inst_3137_);
v___f_3143_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3143_, 0, v_toPure_3138_);
lean_closure_set(v___f_3143_, 1, v_cls_3139_);
lean_closure_set(v___f_3143_, 2, v_____do__lift_3141_);
v___x_3144_ = lean_apply_4(v_toBind_3140_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3142_, v___f_3143_);
return v___x_3144_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3147_ = l_Lean_stringToMessageData(v___x_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3148_, lean_object* v_a_3149_, lean_object* v___y_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_cls_3155_, uint8_t v_____do__lift_3156_){
_start:
{
if (v_____do__lift_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_dec(v_cls_3155_);
lean_dec(v_inst_3154_);
lean_dec_ref(v_inst_3153_);
lean_dec_ref(v_inst_3152_);
lean_dec_ref(v_inst_3151_);
lean_dec_ref(v___y_3150_);
lean_dec_ref(v_a_3149_);
v___x_3157_ = lean_box(0);
v___x_3158_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3157_);
return v___x_3158_;
}
else
{
lean_object* v_type_3159_; lean_object* v_type_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_dec(v_toPure_3148_);
v_type_3159_ = lean_ctor_get(v_a_3149_, 1);
lean_inc_ref(v_type_3159_);
lean_dec_ref(v_a_3149_);
v_type_3160_ = lean_ctor_get(v___y_3150_, 1);
lean_inc_ref(v_type_3160_);
lean_dec_ref(v___y_3150_);
v___x_3161_ = l_Lean_MessageData_ofExpr(v_type_3159_);
v___x_3162_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = l_Lean_MessageData_ofExpr(v_type_3160_);
v___x_3165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = l_Lean_addTrace___redArg(v_inst_3151_, v_inst_3152_, v_inst_3153_, v_inst_3154_, v_cls_3155_, v___x_3165_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3167_, lean_object* v_a_3168_, lean_object* v___y_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_cls_3174_, lean_object* v_____do__lift_3175_){
_start:
{
uint8_t v_____do__lift_3040__boxed_3176_; lean_object* v_res_3177_; 
v_____do__lift_3040__boxed_3176_ = lean_unbox(v_____do__lift_3175_);
v_res_3177_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3167_, v_a_3168_, v___y_3169_, v_inst_3170_, v_inst_3171_, v_inst_3172_, v_inst_3173_, v_cls_3174_, v_____do__lift_3040__boxed_3176_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_toPure_3180_, lean_object* v_toBind_3181_, lean_object* v_a_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_x_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_getInheritedTraceOptions_3188_; lean_object* v_cls_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_getInheritedTraceOptions_3188_ = lean_ctor_get(v_inst_3178_, 2);
lean_inc(v_getInheritedTraceOptions_3188_);
v_cls_3189_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3181_, 2);
lean_inc(v_toPure_3180_);
v___f_3190_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3190_, 0, v_inst_3179_);
lean_closure_set(v___f_3190_, 1, v_toPure_3180_);
lean_closure_set(v___f_3190_, 2, v_cls_3189_);
lean_closure_set(v___f_3190_, 3, v_toBind_3181_);
v___f_3191_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3191_, 0, v_toPure_3180_);
lean_closure_set(v___f_3191_, 1, v_a_3182_);
lean_closure_set(v___f_3191_, 2, v___y_3187_);
lean_closure_set(v___f_3191_, 3, v_inst_3183_);
lean_closure_set(v___f_3191_, 4, v_inst_3178_);
lean_closure_set(v___f_3191_, 5, v_inst_3184_);
lean_closure_set(v___f_3191_, 6, v_inst_3185_);
lean_closure_set(v___f_3191_, 7, v_cls_3189_);
v___x_3192_ = lean_apply_4(v_toBind_3181_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3188_, v___f_3190_);
v___x_3193_ = lean_apply_4(v_toBind_3181_, lean_box(0), lean_box(0), v___x_3192_, v___f_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3194_, lean_object* v_res_3195_, lean_object* v_____r_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_apply_2(v_toPure_3194_, lean_box(0), v_res_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3198_, lean_object* v_toBind_3199_, lean_object* v___f_3200_, lean_object* v_____r_3201_){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3203_ = lean_apply_2(v_inst_3198_, lean_box(0), v___x_3202_);
v___x_3204_ = lean_apply_4(v_toBind_3199_, lean_box(0), lean_box(0), v___x_3203_, v___f_3200_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3205_, lean_object* v_____r_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_apply_1(v___f_3205_, v_____r_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3208_, lean_object* v_type_3209_, lean_object* v_type_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_cls_3215_, lean_object* v_toBind_3216_, lean_object* v___f_3217_, uint8_t v_____do__lift_3218_){
_start:
{
if (v_____do__lift_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_dec(v___f_3217_);
lean_dec(v_toBind_3216_);
lean_dec(v_cls_3215_);
lean_dec(v_inst_3214_);
lean_dec_ref(v_inst_3213_);
lean_dec_ref(v_inst_3212_);
lean_dec_ref(v_inst_3211_);
lean_dec_ref(v_type_3210_);
lean_dec_ref(v_type_3209_);
v___x_3219_ = lean_box(0);
v___x_3220_ = lean_apply_1(v___f_3208_, v___x_3219_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec(v___f_3208_);
v___x_3221_ = l_Lean_MessageData_ofExpr(v_type_3209_);
v___x_3222_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3221_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = l_Lean_MessageData_ofExpr(v_type_3210_);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = l_Lean_addTrace___redArg(v_inst_3211_, v_inst_3212_, v_inst_3213_, v_inst_3214_, v_cls_3215_, v___x_3225_);
v___x_3227_ = lean_apply_4(v_toBind_3216_, lean_box(0), lean_box(0), v___x_3226_, v___f_3217_);
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3228_, lean_object* v_type_3229_, lean_object* v_type_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_cls_3235_, lean_object* v_toBind_3236_, lean_object* v___f_3237_, lean_object* v_____do__lift_3238_){
_start:
{
uint8_t v_____do__lift_3140__boxed_3239_; lean_object* v_res_3240_; 
v_____do__lift_3140__boxed_3239_ = lean_unbox(v_____do__lift_3238_);
v_res_3240_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3228_, v_type_3229_, v_type_3230_, v_inst_3231_, v_inst_3232_, v_inst_3233_, v_inst_3234_, v_cls_3235_, v_toBind_3236_, v___f_3237_, v_____do__lift_3140__boxed_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3241_, lean_object* v_inst_3242_, lean_object* v_toBind_3243_, lean_object* v_inst_3244_, lean_object* v___f_3245_, lean_object* v_a_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v___f_3251_, lean_object* v_res_3252_){
_start:
{
lean_object* v___x_3253_; lean_object* v_zero_3254_; uint8_t v_isZero_3255_; 
v___x_3253_ = lean_array_get_size(v_res_3252_);
v_zero_3254_ = lean_unsigned_to_nat(0u);
v_isZero_3255_ = lean_nat_dec_eq(v___x_3253_, v_zero_3254_);
if (v_isZero_3255_ == 1)
{
lean_object* v___f_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
lean_dec(v___f_3251_);
lean_dec(v_inst_3250_);
lean_dec_ref(v_inst_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec_ref(v_inst_3247_);
lean_dec_ref(v_a_3246_);
lean_inc_ref(v_res_3252_);
lean_inc(v_toPure_3241_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3256_, 0, v_toPure_3241_);
lean_closure_set(v___f_3256_, 1, v_res_3252_);
lean_inc(v_toBind_3243_);
v___f_3257_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3257_, 0, v_inst_3242_);
lean_closure_set(v___f_3257_, 1, v_toBind_3243_);
lean_closure_set(v___f_3257_, 2, v___f_3256_);
v___x_3258_ = lean_box(0);
v___x_3259_ = lean_nat_dec_lt(v_zero_3254_, v___x_3253_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec_ref(v_res_3252_);
lean_dec(v___f_3245_);
lean_dec_ref(v_inst_3244_);
v___x_3260_ = lean_apply_2(v_toPure_3241_, lean_box(0), v___x_3258_);
v___x_3261_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3260_, v___f_3257_);
return v___x_3261_;
}
else
{
uint8_t v___x_3262_; 
v___x_3262_ = lean_nat_dec_le(v___x_3253_, v___x_3253_);
if (v___x_3262_ == 0)
{
if (v___x_3259_ == 0)
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
lean_dec_ref(v_res_3252_);
lean_dec(v___f_3245_);
lean_dec_ref(v_inst_3244_);
v___x_3263_ = lean_apply_2(v_toPure_3241_, lean_box(0), v___x_3258_);
v___x_3264_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3263_, v___f_3257_);
return v___x_3264_;
}
else
{
size_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec(v_toPure_3241_);
v___x_3265_ = ((size_t)0ULL);
v___x_3266_ = lean_usize_of_nat(v___x_3253_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3244_, v___f_3245_, v_res_3252_, v___x_3265_, v___x_3266_, v___x_3258_);
v___x_3268_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3267_, v___f_3257_);
return v___x_3268_;
}
}
else
{
size_t v___x_3269_; size_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec(v_toPure_3241_);
v___x_3269_ = ((size_t)0ULL);
v___x_3270_ = lean_usize_of_nat(v___x_3253_);
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3244_, v___f_3245_, v_res_3252_, v___x_3269_, v___x_3270_, v___x_3258_);
v___x_3272_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3271_, v___f_3257_);
return v___x_3272_;
}
}
}
else
{
lean_object* v_one_3273_; lean_object* v_n_3274_; uint8_t v_isZero_3275_; 
lean_dec(v___f_3245_);
v_one_3273_ = lean_unsigned_to_nat(1u);
v_n_3274_ = lean_nat_sub(v___x_3253_, v_one_3273_);
v_isZero_3275_ = lean_nat_dec_eq(v_n_3274_, v_zero_3254_);
lean_dec(v_n_3274_);
if (v_isZero_3275_ == 1)
{
lean_object* v_newHyp_3276_; lean_object* v_type_3277_; lean_object* v_type_3278_; uint8_t v___x_3279_; 
lean_dec(v___f_3251_);
v_newHyp_3276_ = lean_array_fget_borrowed(v_res_3252_, v_zero_3254_);
v_type_3277_ = lean_ctor_get(v_newHyp_3276_, 1);
v_type_3278_ = lean_ctor_get(v_a_3246_, 1);
lean_inc_ref(v_type_3278_);
lean_dec_ref(v_a_3246_);
v___x_3279_ = lean_expr_eqv(v_type_3277_, v_type_3278_);
if (v___x_3279_ == 0)
{
lean_object* v_getInheritedTraceOptions_3280_; lean_object* v___f_3281_; lean_object* v___f_3282_; lean_object* v___f_3283_; lean_object* v_cls_3284_; lean_object* v___f_3285_; lean_object* v___f_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_inc_ref(v_type_3277_);
v_getInheritedTraceOptions_3280_ = lean_ctor_get(v_inst_3247_, 2);
lean_inc(v_getInheritedTraceOptions_3280_);
lean_inc(v_toPure_3241_);
v___f_3281_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3281_, 0, v_toPure_3241_);
lean_closure_set(v___f_3281_, 1, v_res_3252_);
lean_inc_n(v_toBind_3243_, 4);
v___f_3282_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3282_, 0, v_inst_3242_);
lean_closure_set(v___f_3282_, 1, v_toBind_3243_);
lean_closure_set(v___f_3282_, 2, v___f_3281_);
lean_inc_ref(v___f_3282_);
v___f_3283_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3283_, 0, v___f_3282_);
v_cls_3284_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3285_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3285_, 0, v_inst_3248_);
lean_closure_set(v___f_3285_, 1, v_toPure_3241_);
lean_closure_set(v___f_3285_, 2, v_cls_3284_);
lean_closure_set(v___f_3285_, 3, v_toBind_3243_);
v___f_3286_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3286_, 0, v___f_3282_);
lean_closure_set(v___f_3286_, 1, v_type_3278_);
lean_closure_set(v___f_3286_, 2, v_type_3277_);
lean_closure_set(v___f_3286_, 3, v_inst_3244_);
lean_closure_set(v___f_3286_, 4, v_inst_3247_);
lean_closure_set(v___f_3286_, 5, v_inst_3249_);
lean_closure_set(v___f_3286_, 6, v_inst_3250_);
lean_closure_set(v___f_3286_, 7, v_cls_3284_);
lean_closure_set(v___f_3286_, 8, v_toBind_3243_);
lean_closure_set(v___f_3286_, 9, v___f_3283_);
v___x_3287_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3280_, v___f_3285_);
v___x_3288_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3287_, v___f_3286_);
return v___x_3288_;
}
else
{
lean_object* v___x_3289_; 
lean_dec_ref(v_type_3278_);
lean_dec(v_inst_3250_);
lean_dec_ref(v_inst_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec_ref(v_inst_3247_);
lean_dec_ref(v_inst_3244_);
lean_dec(v_toBind_3243_);
lean_dec(v_inst_3242_);
v___x_3289_ = lean_apply_2(v_toPure_3241_, lean_box(0), v_res_3252_);
return v___x_3289_;
}
}
else
{
lean_object* v___f_3290_; lean_object* v___f_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
lean_dec(v_inst_3250_);
lean_dec_ref(v_inst_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec_ref(v_inst_3247_);
lean_dec_ref(v_a_3246_);
lean_inc_ref(v_res_3252_);
lean_inc(v_toPure_3241_);
v___f_3290_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3290_, 0, v_toPure_3241_);
lean_closure_set(v___f_3290_, 1, v_res_3252_);
lean_inc(v_toBind_3243_);
v___f_3291_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3291_, 0, v_inst_3242_);
lean_closure_set(v___f_3291_, 1, v_toBind_3243_);
lean_closure_set(v___f_3291_, 2, v___f_3290_);
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_nat_dec_lt(v_zero_3254_, v___x_3253_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec_ref(v_res_3252_);
lean_dec(v___f_3251_);
lean_dec_ref(v_inst_3244_);
v___x_3294_ = lean_apply_2(v_toPure_3241_, lean_box(0), v___x_3292_);
v___x_3295_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3294_, v___f_3291_);
return v___x_3295_;
}
else
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_nat_dec_le(v___x_3253_, v___x_3253_);
if (v___x_3296_ == 0)
{
if (v___x_3293_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec_ref(v_res_3252_);
lean_dec(v___f_3251_);
lean_dec_ref(v_inst_3244_);
v___x_3297_ = lean_apply_2(v_toPure_3241_, lean_box(0), v___x_3292_);
v___x_3298_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3297_, v___f_3291_);
return v___x_3298_;
}
else
{
size_t v___x_3299_; size_t v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec(v_toPure_3241_);
v___x_3299_ = ((size_t)0ULL);
v___x_3300_ = lean_usize_of_nat(v___x_3253_);
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3244_, v___f_3251_, v_res_3252_, v___x_3299_, v___x_3300_, v___x_3292_);
v___x_3302_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3301_, v___f_3291_);
return v___x_3302_;
}
}
else
{
size_t v___x_3303_; size_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v_toPure_3241_);
v___x_3303_ = ((size_t)0ULL);
v___x_3304_ = lean_usize_of_nat(v___x_3253_);
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3244_, v___f_3251_, v_res_3252_, v___x_3303_, v___x_3304_, v___x_3292_);
v___x_3306_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3305_, v___f_3291_);
return v___x_3306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3307_, lean_object* v_toPure_3308_, lean_object* v_____do__lift_3309_){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = l_Array_append___redArg(v_bs_3307_, v_____do__lift_3309_);
v___x_3311_ = lean_apply_2(v_toPure_3308_, lean_box(0), v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3312_, lean_object* v_toPure_3313_, lean_object* v_____do__lift_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3312_, v_toPure_3313_, v_____do__lift_3314_);
lean_dec_ref(v_____do__lift_3314_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_toPure_3318_, lean_object* v_toBind_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_f_3324_, lean_object* v_bs_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v___f_3327_; lean_object* v___f_3328_; lean_object* v___f_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_inc(v_inst_3322_);
lean_inc_ref(v_inst_3321_);
lean_inc_ref(v_inst_3320_);
lean_inc_ref_n(v_a_3326_, 2);
lean_inc_n(v_toBind_3319_, 3);
lean_inc_n(v_toPure_3318_, 2);
lean_inc_ref(v_inst_3317_);
lean_inc_ref(v_inst_3316_);
v___f_3327_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3327_, 0, v_inst_3316_);
lean_closure_set(v___f_3327_, 1, v_inst_3317_);
lean_closure_set(v___f_3327_, 2, v_toPure_3318_);
lean_closure_set(v___f_3327_, 3, v_toBind_3319_);
lean_closure_set(v___f_3327_, 4, v_a_3326_);
lean_closure_set(v___f_3327_, 5, v_inst_3320_);
lean_closure_set(v___f_3327_, 6, v_inst_3321_);
lean_closure_set(v___f_3327_, 7, v_inst_3322_);
lean_inc_ref(v___f_3327_);
v___f_3328_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3328_, 0, v_toPure_3318_);
lean_closure_set(v___f_3328_, 1, v_inst_3323_);
lean_closure_set(v___f_3328_, 2, v_toBind_3319_);
lean_closure_set(v___f_3328_, 3, v_inst_3320_);
lean_closure_set(v___f_3328_, 4, v___f_3327_);
lean_closure_set(v___f_3328_, 5, v_a_3326_);
lean_closure_set(v___f_3328_, 6, v_inst_3316_);
lean_closure_set(v___f_3328_, 7, v_inst_3317_);
lean_closure_set(v___f_3328_, 8, v_inst_3321_);
lean_closure_set(v___f_3328_, 9, v_inst_3322_);
lean_closure_set(v___f_3328_, 10, v___f_3327_);
v___f_3329_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3329_, 0, v_bs_3325_);
lean_closure_set(v___f_3329_, 1, v_toPure_3318_);
v___x_3330_ = lean_apply_1(v_f_3324_, v_a_3326_);
v___x_3331_ = lean_apply_4(v_toBind_3319_, lean_box(0), lean_box(0), v___x_3330_, v___f_3328_);
v___x_3332_ = lean_apply_4(v_toBind_3319_, lean_box(0), lean_box(0), v___x_3331_, v___f_3329_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3335_, lean_object* v_toPure_3336_, lean_object* v_toBind_3337_, lean_object* v___f_3338_, lean_object* v_inst_3339_, lean_object* v___f_3340_, lean_object* v_____r_3341_){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v___x_3342_ = lean_unsigned_to_nat(0u);
v___x_3343_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3344_ = lean_array_get_size(v_hyps_3335_);
v___x_3345_ = lean_nat_dec_lt(v___x_3342_, v___x_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec(v___f_3340_);
lean_dec_ref(v_inst_3339_);
lean_dec_ref(v_hyps_3335_);
v___x_3346_ = lean_apply_2(v_toPure_3336_, lean_box(0), v___x_3343_);
v___x_3347_ = lean_apply_4(v_toBind_3337_, lean_box(0), lean_box(0), v___x_3346_, v___f_3338_);
return v___x_3347_;
}
else
{
size_t v___x_3348_; size_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec(v_toPure_3336_);
v___x_3348_ = ((size_t)0ULL);
v___x_3349_ = lean_usize_of_nat(v___x_3344_);
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3339_, v___f_3340_, v_hyps_3335_, v___x_3348_, v___x_3349_, v___x_3343_);
v___x_3351_ = lean_apply_4(v_toBind_3337_, lean_box(0), lean_box(0), v___x_3350_, v___f_3338_);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3352_, lean_object* v_toBind_3353_, lean_object* v___f_3354_, lean_object* v_inst_3355_, lean_object* v___f_3356_, lean_object* v_inst_3357_, lean_object* v___f_3358_, lean_object* v_hyps_3359_){
_start:
{
lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_inc(v_toBind_3353_);
v___f_3360_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3360_, 0, v_hyps_3359_);
lean_closure_set(v___f_3360_, 1, v_toPure_3352_);
lean_closure_set(v___f_3360_, 2, v_toBind_3353_);
lean_closure_set(v___f_3360_, 3, v___f_3354_);
lean_closure_set(v___f_3360_, 4, v_inst_3355_);
lean_closure_set(v___f_3360_, 5, v___f_3356_);
v___x_3361_ = lean_apply_2(v_inst_3357_, lean_box(0), v___f_3358_);
v___x_3362_ = lean_apply_4(v_toBind_3353_, lean_box(0), lean_box(0), v___x_3361_, v___f_3360_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3364_, lean_object* v_inst_3365_, lean_object* v_inst_3366_, lean_object* v_inst_3367_, lean_object* v_inst_3368_, lean_object* v_inst_3369_, lean_object* v_f_3370_){
_start:
{
lean_object* v_toApplicative_3371_; lean_object* v_toBind_3372_; lean_object* v_toPure_3373_; lean_object* v___f_3374_; lean_object* v___f_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___f_3378_; lean_object* v___f_3379_; lean_object* v___x_3380_; 
v_toApplicative_3371_ = lean_ctor_get(v_inst_3364_, 0);
v_toBind_3372_ = lean_ctor_get(v_inst_3364_, 1);
lean_inc_n(v_toBind_3372_, 3);
v_toPure_3373_ = lean_ctor_get(v_toApplicative_3371_, 1);
lean_inc_n(v_toPure_3373_, 2);
lean_inc_n(v_inst_3369_, 3);
v___f_3374_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3374_, 0, v_inst_3369_);
v___f_3375_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3376_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3377_ = lean_apply_2(v_inst_3369_, lean_box(0), v___x_3376_);
lean_inc_ref(v_inst_3364_);
v___f_3378_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3378_, 0, v_inst_3365_);
lean_closure_set(v___f_3378_, 1, v_inst_3366_);
lean_closure_set(v___f_3378_, 2, v_toPure_3373_);
lean_closure_set(v___f_3378_, 3, v_toBind_3372_);
lean_closure_set(v___f_3378_, 4, v_inst_3364_);
lean_closure_set(v___f_3378_, 5, v_inst_3368_);
lean_closure_set(v___f_3378_, 6, v_inst_3367_);
lean_closure_set(v___f_3378_, 7, v_inst_3369_);
lean_closure_set(v___f_3378_, 8, v_f_3370_);
v___f_3379_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3379_, 0, v_toPure_3373_);
lean_closure_set(v___f_3379_, 1, v_toBind_3372_);
lean_closure_set(v___f_3379_, 2, v___f_3374_);
lean_closure_set(v___f_3379_, 3, v_inst_3364_);
lean_closure_set(v___f_3379_, 4, v___f_3378_);
lean_closure_set(v___f_3379_, 5, v_inst_3369_);
lean_closure_set(v___f_3379_, 6, v___f_3375_);
v___x_3380_ = lean_apply_4(v_toBind_3372_, lean_box(0), lean_box(0), v___x_3377_, v___f_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3381_, lean_object* v_inst_3382_, lean_object* v_inst_3383_, lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_inst_3387_, lean_object* v_f_3388_){
_start:
{
lean_object* v_toApplicative_3389_; lean_object* v_toBind_3390_; lean_object* v_toPure_3391_; lean_object* v___f_3392_; lean_object* v___f_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___f_3396_; lean_object* v___f_3397_; lean_object* v___x_3398_; 
v_toApplicative_3389_ = lean_ctor_get(v_inst_3382_, 0);
v_toBind_3390_ = lean_ctor_get(v_inst_3382_, 1);
lean_inc_n(v_toBind_3390_, 3);
v_toPure_3391_ = lean_ctor_get(v_toApplicative_3389_, 1);
lean_inc_n(v_toPure_3391_, 2);
lean_inc_n(v_inst_3387_, 3);
v___f_3392_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3392_, 0, v_inst_3387_);
v___f_3393_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3394_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3395_ = lean_apply_2(v_inst_3387_, lean_box(0), v___x_3394_);
lean_inc_ref(v_inst_3382_);
v___f_3396_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3396_, 0, v_inst_3383_);
lean_closure_set(v___f_3396_, 1, v_inst_3384_);
lean_closure_set(v___f_3396_, 2, v_toPure_3391_);
lean_closure_set(v___f_3396_, 3, v_toBind_3390_);
lean_closure_set(v___f_3396_, 4, v_inst_3382_);
lean_closure_set(v___f_3396_, 5, v_inst_3386_);
lean_closure_set(v___f_3396_, 6, v_inst_3385_);
lean_closure_set(v___f_3396_, 7, v_inst_3387_);
lean_closure_set(v___f_3396_, 8, v_f_3388_);
v___f_3397_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3397_, 0, v_toPure_3391_);
lean_closure_set(v___f_3397_, 1, v_toBind_3390_);
lean_closure_set(v___f_3397_, 2, v___f_3392_);
lean_closure_set(v___f_3397_, 3, v_inst_3382_);
lean_closure_set(v___f_3397_, 4, v___f_3396_);
lean_closure_set(v___f_3397_, 5, v_inst_3387_);
lean_closure_set(v___f_3397_, 6, v___f_3393_);
v___x_3398_ = lean_apply_4(v_toBind_3390_, lean_box(0), lean_box(0), v___x_3395_, v___f_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3399_, lean_object* v_____r_3400_){
_start:
{
uint8_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = 0;
v___x_3402_ = lean_box(v___x_3401_);
v___x_3403_ = lean_apply_2(v_toPure_3399_, lean_box(0), v___x_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_snd_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; lean_object* v_caches_3418_; lean_object* v_typeAnalysis_3419_; lean_object* v_target_3420_; uint8_t v_didChange_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3431_; 
v___x_3417_ = lean_st_ref_take(v___y_3406_);
v_caches_3418_ = lean_ctor_get(v___x_3417_, 0);
v_typeAnalysis_3419_ = lean_ctor_get(v___x_3417_, 1);
v_target_3420_ = lean_ctor_get(v___x_3417_, 2);
v_didChange_3421_ = lean_ctor_get_uint8(v___x_3417_, sizeof(void*)*4);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v___x_3417_, 3);
lean_dec(v_unused_3432_);
v___x_3423_ = v___x_3417_;
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_target_3420_);
lean_inc(v_typeAnalysis_3419_);
lean_inc(v_caches_3418_);
lean_dec(v___x_3417_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3425_ = lean_box(0);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 3, v_snd_3404_);
v___x_3427_ = v___x_3423_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_caches_3418_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_typeAnalysis_3419_);
lean_ctor_set(v_reuseFailAlloc_3430_, 2, v_target_3420_);
lean_ctor_set(v_reuseFailAlloc_3430_, 3, v_snd_3404_);
lean_ctor_set_uint8(v_reuseFailAlloc_3430_, sizeof(void*)*4, v_didChange_3421_);
v___x_3427_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_st_ref_put(v___y_3406_, v___x_3427_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3425_);
return v___x_3429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed(lean_object* v_snd_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(v_snd_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_inst_3447_, lean_object* v_toBind_3448_, lean_object* v___f_3449_, lean_object* v_toPure_3450_, lean_object* v_____s_3451_){
_start:
{
lean_object* v_fst_3452_; 
v_fst_3452_ = lean_ctor_get(v_____s_3451_, 0);
if (lean_obj_tag(v_fst_3452_) == 0)
{
lean_object* v_snd_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_dec(v_toPure_3450_);
v_snd_3453_ = lean_ctor_get(v_____s_3451_, 1);
lean_inc(v_snd_3453_);
lean_dec_ref(v_____s_3451_);
v___f_3454_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_3454_, 0, v_snd_3453_);
v___x_3455_ = lean_apply_2(v_inst_3447_, lean_box(0), v___f_3454_);
v___x_3456_ = lean_apply_4(v_toBind_3448_, lean_box(0), lean_box(0), v___x_3455_, v___f_3449_);
return v___x_3456_;
}
else
{
lean_object* v_val_3457_; lean_object* v___x_3458_; 
lean_inc_ref(v_fst_3452_);
lean_dec_ref(v_____s_3451_);
lean_dec(v___f_3449_);
lean_dec(v_toBind_3448_);
lean_dec(v_inst_3447_);
v_val_3457_ = lean_ctor_get(v_fst_3452_, 0);
lean_inc(v_val_3457_);
lean_dec_ref_known(v_fst_3452_, 1);
v___x_3458_ = lean_apply_2(v_toPure_3450_, lean_box(0), v_val_3457_);
return v___x_3458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_toPure_3459_, lean_object* v_____do__lift_3460_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_apply_2(v_toPure_3459_, lean_box(0), v_____do__lift_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3462_, lean_object* v_next_3463_, lean_object* v_G_3464_, lean_object* v_____do__lift_3465_){
_start:
{
if (lean_obj_tag(v_____do__lift_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; 
lean_dec(v_G_3464_);
v_a_3466_ = lean_ctor_get(v_____do__lift_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v_____do__lift_3465_, 1);
v___x_3467_ = lean_apply_2(v_toPure_3462_, lean_box(0), v_a_3466_);
return v___x_3467_;
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v_toPure_3462_);
v_a_3468_ = lean_ctor_get(v_____do__lift_3465_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v_____do__lift_3465_, 1);
v___x_3469_ = lean_unsigned_to_nat(1u);
v___x_3470_ = lean_nat_add(v_next_3463_, v___x_3469_);
v___x_3471_ = lean_apply_4(v_G_3464_, v___x_3470_, v_a_3468_, lean_box(0), lean_box(0));
return v___x_3471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3472_, lean_object* v_next_3473_, lean_object* v_G_3474_, lean_object* v_____do__lift_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3472_, v_next_3473_, v_G_3474_, v_____do__lift_3475_);
lean_dec(v_next_3473_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(uint8_t v___x_3477_, lean_object* v_snd_3478_, lean_object* v_toPure_3479_, lean_object* v_____r_3480_){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3481_ = lean_box(v___x_3477_);
v___x_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
lean_ctor_set(v___x_3483_, 1, v_snd_3478_);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
v___x_3485_ = lean_apply_2(v_toPure_3479_, lean_box(0), v___x_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed(lean_object* v___x_3486_, lean_object* v_snd_3487_, lean_object* v_toPure_3488_, lean_object* v_____r_3489_){
_start:
{
uint8_t v___x_1675__boxed_3490_; lean_object* v_res_3491_; 
v___x_1675__boxed_3490_ = lean_unbox(v___x_3486_);
v_res_3491_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_1675__boxed_3490_, v_snd_3487_, v_toPure_3488_, v_____r_3489_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_snd_3492_, lean_object* v_newHyp_3493_, lean_object* v___x_3494_, lean_object* v_toPure_3495_, lean_object* v_____r_3496_){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3497_ = lean_array_push(v_snd_3492_, v_newHyp_3493_);
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3494_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
v___x_3500_ = lean_apply_2(v_toPure_3495_, lean_box(0), v___x_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_toPure_3501_, lean_object* v___x_3502_, lean_object* v_____do__lift_3503_, lean_object* v_____do__lift_3504_){
_start:
{
uint8_t v_hasTrace_3505_; 
v_hasTrace_3505_ = lean_ctor_get_uint8(v_____do__lift_3504_, sizeof(void*)*1);
if (v_hasTrace_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_dec(v___x_3502_);
v___x_3506_ = lean_box(v_hasTrace_3505_);
v___x_3507_ = lean_apply_2(v_toPure_3501_, lean_box(0), v___x_3506_);
return v___x_3507_;
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3508_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3509_ = l_Lean_Name_append(v___x_3508_, v___x_3502_);
v___x_3510_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3503_, v_____do__lift_3504_, v___x_3509_);
lean_dec(v___x_3509_);
v___x_3511_ = lean_box(v___x_3510_);
v___x_3512_ = lean_apply_2(v_toPure_3501_, lean_box(0), v___x_3511_);
return v___x_3512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed(lean_object* v_toPure_3513_, lean_object* v___x_3514_, lean_object* v_____do__lift_3515_, lean_object* v_____do__lift_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(v_toPure_3513_, v___x_3514_, v_____do__lift_3515_, v_____do__lift_3516_);
lean_dec_ref(v_____do__lift_3516_);
lean_dec_ref(v_____do__lift_3515_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v_inst_3518_, lean_object* v_toPure_3519_, lean_object* v___x_3520_, lean_object* v_toBind_3521_, lean_object* v_____do__lift_3522_){
_start:
{
lean_object* v_getOptionsUnrestricted_3523_; lean_object* v___f_3524_; lean_object* v___x_3525_; 
v_getOptionsUnrestricted_3523_ = lean_ctor_get(v_inst_3518_, 1);
lean_inc(v_getOptionsUnrestricted_3523_);
lean_dec_ref(v_inst_3518_);
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_3524_, 0, v_toPure_3519_);
lean_closure_set(v___f_3524_, 1, v___x_3520_);
lean_closure_set(v___f_3524_, 2, v_____do__lift_3522_);
v___x_3525_ = lean_apply_4(v_toBind_3521_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3523_, v___f_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object* v___f_3526_, lean_object* v___x_3527_, lean_object* v_type_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_toMonadRef_3531_, lean_object* v_inst_3532_, lean_object* v___x_3533_, lean_object* v_toBind_3534_, lean_object* v___f_3535_, uint8_t v_____do__lift_3536_){
_start:
{
if (v_____do__lift_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec(v___f_3535_);
lean_dec(v_toBind_3534_);
lean_dec(v___x_3533_);
lean_dec(v_inst_3532_);
lean_dec_ref(v_toMonadRef_3531_);
lean_dec_ref(v_inst_3530_);
lean_dec_ref(v_inst_3529_);
lean_dec_ref(v_type_3528_);
lean_dec_ref(v___x_3527_);
v___x_3537_ = lean_box(0);
v___x_3538_ = lean_apply_1(v___f_3526_, v___x_3537_);
return v___x_3538_;
}
else
{
lean_object* v_type_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec(v___f_3526_);
v_type_3539_ = lean_ctor_get(v___x_3527_, 1);
lean_inc_ref(v_type_3539_);
lean_dec_ref(v___x_3527_);
v___x_3540_ = l_Lean_MessageData_ofExpr(v_type_3539_);
v___x_3541_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = l_Lean_MessageData_ofExpr(v_type_3528_);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = l_Lean_addTrace___redArg(v_inst_3529_, v_inst_3530_, v_toMonadRef_3531_, v_inst_3532_, v___x_3533_, v___x_3544_);
v___x_3546_ = lean_apply_4(v_toBind_3534_, lean_box(0), lean_box(0), v___x_3545_, v___f_3535_);
return v___x_3546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___f_3547_, lean_object* v___x_3548_, lean_object* v_type_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_toMonadRef_3552_, lean_object* v_inst_3553_, lean_object* v___x_3554_, lean_object* v_toBind_3555_, lean_object* v___f_3556_, lean_object* v_____do__lift_3557_){
_start:
{
uint8_t v_____do__lift_1750__boxed_3558_; lean_object* v_res_3559_; 
v_____do__lift_1750__boxed_3558_ = lean_unbox(v_____do__lift_3557_);
v_res_3559_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3547_, v___x_3548_, v_type_3549_, v_inst_3550_, v_inst_3551_, v_toMonadRef_3552_, v_inst_3553_, v___x_3554_, v_toBind_3555_, v___f_3556_, v_____do__lift_1750__boxed_3558_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v___x_3560_, lean_object* v_snd_3561_, lean_object* v___x_3562_, lean_object* v_toPure_3563_, lean_object* v_inst_3564_, lean_object* v_toBind_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_toMonadRef_3569_, lean_object* v_inst_3570_, lean_object* v___f_3571_, lean_object* v_newHyp_3572_){
_start:
{
lean_object* v_type_3573_; lean_object* v_value_3574_; uint8_t v___x_3575_; 
v_type_3573_ = lean_ctor_get(v_newHyp_3572_, 1);
v_value_3574_ = lean_ctor_get(v_newHyp_3572_, 2);
lean_inc_ref(v_type_3573_);
v___x_3575_ = l_Lean_Expr_isFalse(v_type_3573_);
if (v___x_3575_ == 0)
{
lean_object* v_type_3576_; lean_object* v___f_3577_; lean_object* v___f_3578_; lean_object* v___f_3579_; lean_object* v___f_3580_; uint8_t v___x_3588_; 
lean_dec(v___f_3571_);
v_type_3576_ = lean_ctor_get(v___x_3560_, 1);
lean_inc(v_toPure_3563_);
lean_inc(v___x_3562_);
lean_inc_ref(v_newHyp_3572_);
lean_inc(v_snd_3561_);
v___f_3577_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3577_, 0, v_snd_3561_);
lean_closure_set(v___f_3577_, 1, v_newHyp_3572_);
lean_closure_set(v___f_3577_, 2, v___x_3562_);
lean_closure_set(v___f_3577_, 3, v_toPure_3563_);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3578_, 0, v___f_3577_);
lean_inc(v_toBind_3565_);
v___f_3579_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3579_, 0, v_inst_3564_);
lean_closure_set(v___f_3579_, 1, v_toBind_3565_);
lean_closure_set(v___f_3579_, 2, v___f_3578_);
lean_inc_ref(v___f_3579_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3580_, 0, v___f_3579_);
v___x_3588_ = lean_expr_eqv(v_type_3576_, v_type_3573_);
if (v___x_3588_ == 0)
{
lean_inc_ref(v_type_3573_);
lean_dec_ref(v_newHyp_3572_);
lean_dec(v___x_3562_);
lean_dec(v_snd_3561_);
goto v___jp_3581_;
}
else
{
if (v___x_3575_ == 0)
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_dec_ref(v___f_3580_);
lean_dec_ref(v___f_3579_);
lean_dec(v_inst_3570_);
lean_dec_ref(v_toMonadRef_3569_);
lean_dec_ref(v_inst_3568_);
lean_dec_ref(v_inst_3567_);
lean_dec_ref(v_inst_3566_);
lean_dec(v_toBind_3565_);
lean_dec_ref(v___x_3560_);
v___x_3589_ = lean_box(0);
v___x_3590_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3561_, v_newHyp_3572_, v___x_3562_, v_toPure_3563_, v___x_3589_);
return v___x_3590_;
}
else
{
lean_inc_ref(v_type_3573_);
lean_dec_ref(v_newHyp_3572_);
lean_dec(v___x_3562_);
lean_dec(v_snd_3561_);
goto v___jp_3581_;
}
}
v___jp_3581_:
{
lean_object* v_getInheritedTraceOptions_3582_; lean_object* v___x_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_getInheritedTraceOptions_3582_ = lean_ctor_get(v_inst_3566_, 2);
lean_inc(v_getInheritedTraceOptions_3582_);
v___x_3583_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3565_, 3);
v___f_3584_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3584_, 0, v_inst_3567_);
lean_closure_set(v___f_3584_, 1, v_toPure_3563_);
lean_closure_set(v___f_3584_, 2, v___x_3583_);
lean_closure_set(v___f_3584_, 3, v_toBind_3565_);
v___f_3585_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3585_, 0, v___f_3579_);
lean_closure_set(v___f_3585_, 1, v___x_3560_);
lean_closure_set(v___f_3585_, 2, v_type_3573_);
lean_closure_set(v___f_3585_, 3, v_inst_3568_);
lean_closure_set(v___f_3585_, 4, v_inst_3566_);
lean_closure_set(v___f_3585_, 5, v_toMonadRef_3569_);
lean_closure_set(v___f_3585_, 6, v_inst_3570_);
lean_closure_set(v___f_3585_, 7, v___x_3583_);
lean_closure_set(v___f_3585_, 8, v_toBind_3565_);
lean_closure_set(v___f_3585_, 9, v___f_3580_);
v___x_3586_ = lean_apply_4(v_toBind_3565_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3582_, v___f_3584_);
v___x_3587_ = lean_apply_4(v_toBind_3565_, lean_box(0), lean_box(0), v___x_3586_, v___f_3585_);
return v___x_3587_;
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_inc_ref(v_value_3574_);
lean_dec_ref(v_newHyp_3572_);
lean_dec(v_inst_3570_);
lean_dec_ref(v_toMonadRef_3569_);
lean_dec_ref(v_inst_3568_);
lean_dec_ref(v_inst_3567_);
lean_dec_ref(v_inst_3566_);
lean_dec(v_toPure_3563_);
lean_dec(v___x_3562_);
lean_dec(v_snd_3561_);
lean_dec_ref(v___x_3560_);
v___x_3591_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3591_, 0, v_value_3574_);
v___x_3592_ = lean_apply_2(v_inst_3564_, lean_box(0), v___x_3591_);
v___x_3593_ = lean_apply_4(v_toBind_3565_, lean_box(0), lean_box(0), v___x_3592_, v___f_3571_);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3594_, lean_object* v_toPure_3595_, lean_object* v_hyps_3596_, lean_object* v___x_3597_, lean_object* v_inst_3598_, lean_object* v_toBind_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_toMonadRef_3603_, lean_object* v_inst_3604_, lean_object* v_f_3605_, lean_object* v___f_3606_, lean_object* v_next_3607_, lean_object* v_acc_3608_, lean_object* v_h_3609_, lean_object* v_G_3610_){
_start:
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_nat_dec_lt(v_next_3607_, v___x_3594_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; 
lean_dec(v_G_3610_);
lean_dec(v_next_3607_);
lean_dec(v___f_3606_);
lean_dec(v_f_3605_);
lean_dec(v_inst_3604_);
lean_dec_ref(v_toMonadRef_3603_);
lean_dec_ref(v_inst_3602_);
lean_dec_ref(v_inst_3601_);
lean_dec_ref(v_inst_3600_);
lean_dec(v_toBind_3599_);
lean_dec(v_inst_3598_);
lean_dec(v___x_3597_);
v___x_3612_ = lean_apply_2(v_toPure_3595_, lean_box(0), v_acc_3608_);
return v___x_3612_;
}
else
{
lean_object* v_snd_3613_; lean_object* v___f_3614_; lean_object* v___x_3615_; lean_object* v___f_3616_; lean_object* v___x_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_snd_3613_ = lean_ctor_get(v_acc_3608_, 1);
lean_inc_n(v_snd_3613_, 2);
lean_dec_ref(v_acc_3608_);
lean_inc(v_next_3607_);
lean_inc_n(v_toPure_3595_, 2);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3614_, 0, v_toPure_3595_);
lean_closure_set(v___f_3614_, 1, v_next_3607_);
lean_closure_set(v___f_3614_, 2, v_G_3610_);
v___x_3615_ = lean_box(v___x_3611_);
v___f_3616_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3616_, 0, v___x_3615_);
lean_closure_set(v___f_3616_, 1, v_snd_3613_);
lean_closure_set(v___f_3616_, 2, v_toPure_3595_);
v___x_3617_ = lean_array_fget_borrowed(v_hyps_3596_, v_next_3607_);
lean_inc_n(v_toBind_3599_, 3);
lean_inc_n(v___x_3617_, 2);
v___f_3618_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9), 13, 12);
lean_closure_set(v___f_3618_, 0, v___x_3617_);
lean_closure_set(v___f_3618_, 1, v_snd_3613_);
lean_closure_set(v___f_3618_, 2, v___x_3597_);
lean_closure_set(v___f_3618_, 3, v_toPure_3595_);
lean_closure_set(v___f_3618_, 4, v_inst_3598_);
lean_closure_set(v___f_3618_, 5, v_toBind_3599_);
lean_closure_set(v___f_3618_, 6, v_inst_3600_);
lean_closure_set(v___f_3618_, 7, v_inst_3601_);
lean_closure_set(v___f_3618_, 8, v_inst_3602_);
lean_closure_set(v___f_3618_, 9, v_toMonadRef_3603_);
lean_closure_set(v___f_3618_, 10, v_inst_3604_);
lean_closure_set(v___f_3618_, 11, v___f_3616_);
v___x_3619_ = lean_apply_2(v_f_3605_, v_next_3607_, v___x_3617_);
v___x_3620_ = lean_apply_4(v_toBind_3599_, lean_box(0), lean_box(0), v___x_3619_, v___f_3618_);
v___x_3621_ = lean_apply_4(v_toBind_3599_, lean_box(0), lean_box(0), v___x_3620_, v___f_3606_);
v___x_3622_ = lean_apply_4(v_toBind_3599_, lean_box(0), lean_box(0), v___x_3621_, v___f_3614_);
return v___x_3622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3623_ = _args[0];
lean_object* v_toPure_3624_ = _args[1];
lean_object* v_hyps_3625_ = _args[2];
lean_object* v___x_3626_ = _args[3];
lean_object* v_inst_3627_ = _args[4];
lean_object* v_toBind_3628_ = _args[5];
lean_object* v_inst_3629_ = _args[6];
lean_object* v_inst_3630_ = _args[7];
lean_object* v_inst_3631_ = _args[8];
lean_object* v_toMonadRef_3632_ = _args[9];
lean_object* v_inst_3633_ = _args[10];
lean_object* v_f_3634_ = _args[11];
lean_object* v___f_3635_ = _args[12];
lean_object* v_next_3636_ = _args[13];
lean_object* v_acc_3637_ = _args[14];
lean_object* v_h_3638_ = _args[15];
lean_object* v_G_3639_ = _args[16];
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3623_, v_toPure_3624_, v_hyps_3625_, v___x_3626_, v_inst_3627_, v_toBind_3628_, v_inst_3629_, v_inst_3630_, v_inst_3631_, v_toMonadRef_3632_, v_inst_3633_, v_f_3634_, v___f_3635_, v_next_3636_, v_acc_3637_, v_h_3638_, v_G_3639_);
lean_dec_ref(v_hyps_3625_);
lean_dec(v___x_3623_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3641_, lean_object* v_inst_3642_, lean_object* v_toBind_3643_, lean_object* v_inst_3644_, lean_object* v_inst_3645_, lean_object* v_inst_3646_, lean_object* v_toMonadRef_3647_, lean_object* v_inst_3648_, lean_object* v_f_3649_, lean_object* v___f_3650_, lean_object* v___f_3651_, lean_object* v_hyps_3652_){
_start:
{
lean_object* v___x_3653_; lean_object* v_newHyps_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___f_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3653_ = lean_array_get_size(v_hyps_3652_);
v_newHyps_3654_ = lean_mk_empty_array_with_capacity(v___x_3653_);
v___x_3655_ = lean_unsigned_to_nat(0u);
v___x_3656_ = lean_box(0);
lean_inc(v_toBind_3643_);
v___f_3657_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3657_, 0, v___x_3653_);
lean_closure_set(v___f_3657_, 1, v_toPure_3641_);
lean_closure_set(v___f_3657_, 2, v_hyps_3652_);
lean_closure_set(v___f_3657_, 3, v___x_3656_);
lean_closure_set(v___f_3657_, 4, v_inst_3642_);
lean_closure_set(v___f_3657_, 5, v_toBind_3643_);
lean_closure_set(v___f_3657_, 6, v_inst_3644_);
lean_closure_set(v___f_3657_, 7, v_inst_3645_);
lean_closure_set(v___f_3657_, 8, v_inst_3646_);
lean_closure_set(v___f_3657_, 9, v_toMonadRef_3647_);
lean_closure_set(v___f_3657_, 10, v_inst_3648_);
lean_closure_set(v___f_3657_, 11, v_f_3649_);
lean_closure_set(v___f_3657_, 12, v___f_3650_);
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v_newHyps_3654_);
v___x_3659_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3657_, v___x_3655_, v___x_3658_, lean_box(0));
v___x_3660_ = lean_apply_4(v_toBind_3643_, lean_box(0), lean_box(0), v___x_3659_, v___f_3651_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3661_, lean_object* v_inst_3662_, lean_object* v_inst_3663_, lean_object* v_inst_3664_, lean_object* v_inst_3665_, lean_object* v_inst_3666_, lean_object* v_f_3667_){
_start:
{
lean_object* v_toApplicative_3668_; lean_object* v_toBind_3669_; lean_object* v_toPure_3670_; lean_object* v_toMonadRef_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___f_3676_; lean_object* v___f_3677_; lean_object* v___x_3678_; 
v_toApplicative_3668_ = lean_ctor_get(v_inst_3661_, 0);
v_toBind_3669_ = lean_ctor_get(v_inst_3661_, 1);
lean_inc_n(v_toBind_3669_, 3);
v_toPure_3670_ = lean_ctor_get(v_toApplicative_3668_, 1);
lean_inc_n(v_toPure_3670_, 4);
v_toMonadRef_3671_ = lean_ctor_get(v_inst_3663_, 1);
lean_inc_ref(v_toMonadRef_3671_);
lean_dec_ref(v_inst_3663_);
v___x_3672_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3662_, 2);
v___x_3673_ = lean_apply_2(v_inst_3662_, lean_box(0), v___x_3672_);
v___f_3674_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3674_, 0, v_toPure_3670_);
v___f_3675_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3675_, 0, v_inst_3662_);
lean_closure_set(v___f_3675_, 1, v_toBind_3669_);
lean_closure_set(v___f_3675_, 2, v___f_3674_);
lean_closure_set(v___f_3675_, 3, v_toPure_3670_);
v___f_3676_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3676_, 0, v_toPure_3670_);
v___f_3677_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3677_, 0, v_toPure_3670_);
lean_closure_set(v___f_3677_, 1, v_inst_3662_);
lean_closure_set(v___f_3677_, 2, v_toBind_3669_);
lean_closure_set(v___f_3677_, 3, v_inst_3664_);
lean_closure_set(v___f_3677_, 4, v_inst_3665_);
lean_closure_set(v___f_3677_, 5, v_inst_3661_);
lean_closure_set(v___f_3677_, 6, v_toMonadRef_3671_);
lean_closure_set(v___f_3677_, 7, v_inst_3666_);
lean_closure_set(v___f_3677_, 8, v_f_3667_);
lean_closure_set(v___f_3677_, 9, v___f_3676_);
lean_closure_set(v___f_3677_, 10, v___f_3675_);
v___x_3678_ = lean_apply_4(v_toBind_3669_, lean_box(0), lean_box(0), v___x_3673_, v___f_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3679_, lean_object* v_inst_3680_, lean_object* v_inst_3681_, lean_object* v_inst_3682_, lean_object* v_inst_3683_, lean_object* v_inst_3684_, lean_object* v_inst_3685_, lean_object* v_inst_3686_, lean_object* v_inst_3687_, lean_object* v_f_3688_){
_start:
{
lean_object* v_toApplicative_3689_; lean_object* v_toBind_3690_; lean_object* v_toPure_3691_; lean_object* v_toMonadRef_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; 
v_toApplicative_3689_ = lean_ctor_get(v_inst_3680_, 0);
v_toBind_3690_ = lean_ctor_get(v_inst_3680_, 1);
lean_inc_n(v_toBind_3690_, 3);
v_toPure_3691_ = lean_ctor_get(v_toApplicative_3689_, 1);
lean_inc_n(v_toPure_3691_, 4);
v_toMonadRef_3692_ = lean_ctor_get(v_inst_3682_, 1);
lean_inc_ref(v_toMonadRef_3692_);
lean_dec_ref(v_inst_3682_);
v___x_3693_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3681_, 2);
v___x_3694_ = lean_apply_2(v_inst_3681_, lean_box(0), v___x_3693_);
v___f_3695_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3695_, 0, v_toPure_3691_);
v___f_3696_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3696_, 0, v_inst_3681_);
lean_closure_set(v___f_3696_, 1, v_toBind_3690_);
lean_closure_set(v___f_3696_, 2, v___f_3695_);
lean_closure_set(v___f_3696_, 3, v_toPure_3691_);
v___f_3697_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3697_, 0, v_toPure_3691_);
v___f_3698_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3698_, 0, v_toPure_3691_);
lean_closure_set(v___f_3698_, 1, v_inst_3681_);
lean_closure_set(v___f_3698_, 2, v_toBind_3690_);
lean_closure_set(v___f_3698_, 3, v_inst_3684_);
lean_closure_set(v___f_3698_, 4, v_inst_3685_);
lean_closure_set(v___f_3698_, 5, v_inst_3680_);
lean_closure_set(v___f_3698_, 6, v_toMonadRef_3692_);
lean_closure_set(v___f_3698_, 7, v_inst_3686_);
lean_closure_set(v___f_3698_, 8, v_f_3688_);
lean_closure_set(v___f_3698_, 9, v___f_3697_);
lean_closure_set(v___f_3698_, 10, v___f_3696_);
v___x_3699_ = lean_apply_4(v_toBind_3690_, lean_box(0), lean_box(0), v___x_3694_, v___f_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3700_, lean_object* v_inst_3701_, lean_object* v_inst_3702_, lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_inst_3705_, lean_object* v_inst_3706_, lean_object* v_inst_3707_, lean_object* v_inst_3708_, lean_object* v_f_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3700_, v_inst_3701_, v_inst_3702_, v_inst_3703_, v_inst_3704_, v_inst_3705_, v_inst_3706_, v_inst_3707_, v_inst_3708_, v_f_3709_);
lean_dec_ref(v_inst_3708_);
lean_dec_ref(v_inst_3704_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3711_, lean_object* v_snd_3712_, lean_object* v___x_3713_, lean_object* v_toPure_3714_, lean_object* v_inst_3715_, lean_object* v_toBind_3716_, lean_object* v_inst_3717_, lean_object* v_inst_3718_, lean_object* v_toMonadRef_3719_, lean_object* v_inst_3720_, lean_object* v_inst_3721_, lean_object* v___f_3722_, lean_object* v_newHyp_3723_){
_start:
{
lean_object* v_type_3724_; lean_object* v_value_3725_; uint8_t v___x_3726_; 
v_type_3724_ = lean_ctor_get(v_newHyp_3723_, 1);
v_value_3725_ = lean_ctor_get(v_newHyp_3723_, 2);
lean_inc_ref(v_type_3724_);
v___x_3726_ = l_Lean_Expr_isFalse(v_type_3724_);
if (v___x_3726_ == 0)
{
lean_object* v_type_3727_; lean_object* v___f_3728_; lean_object* v___f_3729_; lean_object* v___f_3730_; lean_object* v___f_3731_; uint8_t v___x_3739_; 
lean_dec(v___f_3722_);
v_type_3727_ = lean_ctor_get(v___x_3711_, 1);
lean_inc(v_toPure_3714_);
lean_inc(v___x_3713_);
lean_inc_ref(v_newHyp_3723_);
lean_inc(v_snd_3712_);
v___f_3728_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3728_, 0, v_snd_3712_);
lean_closure_set(v___f_3728_, 1, v_newHyp_3723_);
lean_closure_set(v___f_3728_, 2, v___x_3713_);
lean_closure_set(v___f_3728_, 3, v_toPure_3714_);
v___f_3729_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3729_, 0, v___f_3728_);
lean_inc(v_toBind_3716_);
v___f_3730_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3730_, 0, v_inst_3715_);
lean_closure_set(v___f_3730_, 1, v_toBind_3716_);
lean_closure_set(v___f_3730_, 2, v___f_3729_);
lean_inc_ref(v___f_3730_);
v___f_3731_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3731_, 0, v___f_3730_);
v___x_3739_ = lean_expr_eqv(v_type_3727_, v_type_3724_);
if (v___x_3739_ == 0)
{
lean_inc_ref(v_type_3724_);
lean_dec_ref(v_newHyp_3723_);
lean_dec(v___x_3713_);
lean_dec(v_snd_3712_);
goto v___jp_3732_;
}
else
{
if (v___x_3726_ == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec_ref(v___f_3731_);
lean_dec_ref(v___f_3730_);
lean_dec_ref(v_inst_3721_);
lean_dec(v_inst_3720_);
lean_dec_ref(v_toMonadRef_3719_);
lean_dec_ref(v_inst_3718_);
lean_dec_ref(v_inst_3717_);
lean_dec(v_toBind_3716_);
lean_dec_ref(v___x_3711_);
v___x_3740_ = lean_box(0);
v___x_3741_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3712_, v_newHyp_3723_, v___x_3713_, v_toPure_3714_, v___x_3740_);
return v___x_3741_;
}
else
{
lean_inc_ref(v_type_3724_);
lean_dec_ref(v_newHyp_3723_);
lean_dec(v___x_3713_);
lean_dec(v_snd_3712_);
goto v___jp_3732_;
}
}
v___jp_3732_:
{
lean_object* v_getInheritedTraceOptions_3733_; lean_object* v___x_3734_; lean_object* v___f_3735_; lean_object* v___f_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v_getInheritedTraceOptions_3733_ = lean_ctor_get(v_inst_3717_, 2);
lean_inc(v_getInheritedTraceOptions_3733_);
v___x_3734_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3716_, 3);
v___f_3735_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3735_, 0, v___f_3730_);
lean_closure_set(v___f_3735_, 1, v___x_3711_);
lean_closure_set(v___f_3735_, 2, v_type_3724_);
lean_closure_set(v___f_3735_, 3, v_inst_3718_);
lean_closure_set(v___f_3735_, 4, v_inst_3717_);
lean_closure_set(v___f_3735_, 5, v_toMonadRef_3719_);
lean_closure_set(v___f_3735_, 6, v_inst_3720_);
lean_closure_set(v___f_3735_, 7, v___x_3734_);
lean_closure_set(v___f_3735_, 8, v_toBind_3716_);
lean_closure_set(v___f_3735_, 9, v___f_3731_);
v___f_3736_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3736_, 0, v_inst_3721_);
lean_closure_set(v___f_3736_, 1, v_toPure_3714_);
lean_closure_set(v___f_3736_, 2, v___x_3734_);
lean_closure_set(v___f_3736_, 3, v_toBind_3716_);
v___x_3737_ = lean_apply_4(v_toBind_3716_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3733_, v___f_3736_);
v___x_3738_ = lean_apply_4(v_toBind_3716_, lean_box(0), lean_box(0), v___x_3737_, v___f_3735_);
return v___x_3738_;
}
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_inc_ref(v_value_3725_);
lean_dec_ref(v_newHyp_3723_);
lean_dec_ref(v_inst_3721_);
lean_dec(v_inst_3720_);
lean_dec_ref(v_toMonadRef_3719_);
lean_dec_ref(v_inst_3718_);
lean_dec_ref(v_inst_3717_);
lean_dec(v_toPure_3714_);
lean_dec(v___x_3713_);
lean_dec(v_snd_3712_);
lean_dec_ref(v___x_3711_);
v___x_3742_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3742_, 0, v_value_3725_);
v___x_3743_ = lean_apply_2(v_inst_3715_, lean_box(0), v___x_3742_);
v___x_3744_ = lean_apply_4(v_toBind_3716_, lean_box(0), lean_box(0), v___x_3743_, v___f_3722_);
return v___x_3744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3745_, lean_object* v_toPure_3746_, lean_object* v_hyps_3747_, lean_object* v___x_3748_, lean_object* v_inst_3749_, lean_object* v_toBind_3750_, lean_object* v_inst_3751_, lean_object* v_inst_3752_, lean_object* v_toMonadRef_3753_, lean_object* v_inst_3754_, lean_object* v_inst_3755_, lean_object* v_f_3756_, lean_object* v___f_3757_, lean_object* v_next_3758_, lean_object* v_acc_3759_, lean_object* v_h_3760_, lean_object* v_G_3761_){
_start:
{
uint8_t v___x_3762_; 
v___x_3762_ = lean_nat_dec_lt(v_next_3758_, v___x_3745_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
lean_dec(v_G_3761_);
lean_dec(v_next_3758_);
lean_dec(v___f_3757_);
lean_dec(v_f_3756_);
lean_dec_ref(v_inst_3755_);
lean_dec(v_inst_3754_);
lean_dec_ref(v_toMonadRef_3753_);
lean_dec_ref(v_inst_3752_);
lean_dec_ref(v_inst_3751_);
lean_dec(v_toBind_3750_);
lean_dec(v_inst_3749_);
lean_dec(v___x_3748_);
v___x_3763_ = lean_apply_2(v_toPure_3746_, lean_box(0), v_acc_3759_);
return v___x_3763_;
}
else
{
lean_object* v_snd_3764_; lean_object* v___f_3765_; lean_object* v___x_3766_; lean_object* v___f_3767_; lean_object* v___x_3768_; lean_object* v___f_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v_snd_3764_ = lean_ctor_get(v_acc_3759_, 1);
lean_inc_n(v_snd_3764_, 2);
lean_dec_ref(v_acc_3759_);
lean_inc(v_next_3758_);
lean_inc_n(v_toPure_3746_, 2);
v___f_3765_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3765_, 0, v_toPure_3746_);
lean_closure_set(v___f_3765_, 1, v_next_3758_);
lean_closure_set(v___f_3765_, 2, v_G_3761_);
v___x_3766_ = lean_box(v___x_3762_);
v___f_3767_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3767_, 0, v___x_3766_);
lean_closure_set(v___f_3767_, 1, v_snd_3764_);
lean_closure_set(v___f_3767_, 2, v_toPure_3746_);
v___x_3768_ = lean_array_fget_borrowed(v_hyps_3747_, v_next_3758_);
lean_dec(v_next_3758_);
lean_inc_n(v_toBind_3750_, 3);
lean_inc_n(v___x_3768_, 2);
v___f_3769_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3769_, 0, v___x_3768_);
lean_closure_set(v___f_3769_, 1, v_snd_3764_);
lean_closure_set(v___f_3769_, 2, v___x_3748_);
lean_closure_set(v___f_3769_, 3, v_toPure_3746_);
lean_closure_set(v___f_3769_, 4, v_inst_3749_);
lean_closure_set(v___f_3769_, 5, v_toBind_3750_);
lean_closure_set(v___f_3769_, 6, v_inst_3751_);
lean_closure_set(v___f_3769_, 7, v_inst_3752_);
lean_closure_set(v___f_3769_, 8, v_toMonadRef_3753_);
lean_closure_set(v___f_3769_, 9, v_inst_3754_);
lean_closure_set(v___f_3769_, 10, v_inst_3755_);
lean_closure_set(v___f_3769_, 11, v___f_3767_);
v___x_3770_ = lean_apply_1(v_f_3756_, v___x_3768_);
v___x_3771_ = lean_apply_4(v_toBind_3750_, lean_box(0), lean_box(0), v___x_3770_, v___f_3769_);
v___x_3772_ = lean_apply_4(v_toBind_3750_, lean_box(0), lean_box(0), v___x_3771_, v___f_3757_);
v___x_3773_ = lean_apply_4(v_toBind_3750_, lean_box(0), lean_box(0), v___x_3772_, v___f_3765_);
return v___x_3773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3774_ = _args[0];
lean_object* v_toPure_3775_ = _args[1];
lean_object* v_hyps_3776_ = _args[2];
lean_object* v___x_3777_ = _args[3];
lean_object* v_inst_3778_ = _args[4];
lean_object* v_toBind_3779_ = _args[5];
lean_object* v_inst_3780_ = _args[6];
lean_object* v_inst_3781_ = _args[7];
lean_object* v_toMonadRef_3782_ = _args[8];
lean_object* v_inst_3783_ = _args[9];
lean_object* v_inst_3784_ = _args[10];
lean_object* v_f_3785_ = _args[11];
lean_object* v___f_3786_ = _args[12];
lean_object* v_next_3787_ = _args[13];
lean_object* v_acc_3788_ = _args[14];
lean_object* v_h_3789_ = _args[15];
lean_object* v_G_3790_ = _args[16];
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3774_, v_toPure_3775_, v_hyps_3776_, v___x_3777_, v_inst_3778_, v_toBind_3779_, v_inst_3780_, v_inst_3781_, v_toMonadRef_3782_, v_inst_3783_, v_inst_3784_, v_f_3785_, v___f_3786_, v_next_3787_, v_acc_3788_, v_h_3789_, v_G_3790_);
lean_dec_ref(v_hyps_3776_);
lean_dec(v___x_3774_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3792_, lean_object* v_inst_3793_, lean_object* v_toBind_3794_, lean_object* v_inst_3795_, lean_object* v_inst_3796_, lean_object* v_toMonadRef_3797_, lean_object* v_inst_3798_, lean_object* v_inst_3799_, lean_object* v_f_3800_, lean_object* v___f_3801_, lean_object* v___f_3802_, lean_object* v_hyps_3803_){
_start:
{
lean_object* v___x_3804_; lean_object* v_newHyps_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___f_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3804_ = lean_array_get_size(v_hyps_3803_);
v_newHyps_3805_ = lean_mk_empty_array_with_capacity(v___x_3804_);
v___x_3806_ = lean_unsigned_to_nat(0u);
v___x_3807_ = lean_box(0);
lean_inc(v_toBind_3794_);
v___f_3808_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3808_, 0, v___x_3804_);
lean_closure_set(v___f_3808_, 1, v_toPure_3792_);
lean_closure_set(v___f_3808_, 2, v_hyps_3803_);
lean_closure_set(v___f_3808_, 3, v___x_3807_);
lean_closure_set(v___f_3808_, 4, v_inst_3793_);
lean_closure_set(v___f_3808_, 5, v_toBind_3794_);
lean_closure_set(v___f_3808_, 6, v_inst_3795_);
lean_closure_set(v___f_3808_, 7, v_inst_3796_);
lean_closure_set(v___f_3808_, 8, v_toMonadRef_3797_);
lean_closure_set(v___f_3808_, 9, v_inst_3798_);
lean_closure_set(v___f_3808_, 10, v_inst_3799_);
lean_closure_set(v___f_3808_, 11, v_f_3800_);
lean_closure_set(v___f_3808_, 12, v___f_3801_);
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v_newHyps_3805_);
v___x_3810_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3808_, v___x_3806_, v___x_3809_, lean_box(0));
v___x_3811_ = lean_apply_4(v_toBind_3794_, lean_box(0), lean_box(0), v___x_3810_, v___f_3802_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3812_, lean_object* v_inst_3813_, lean_object* v_inst_3814_, lean_object* v_inst_3815_, lean_object* v_inst_3816_, lean_object* v_inst_3817_, lean_object* v_f_3818_){
_start:
{
lean_object* v_toApplicative_3819_; lean_object* v_toBind_3820_; lean_object* v_toPure_3821_; lean_object* v_toMonadRef_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___f_3825_; lean_object* v___f_3826_; lean_object* v___f_3827_; lean_object* v___f_3828_; lean_object* v___x_3829_; 
v_toApplicative_3819_ = lean_ctor_get(v_inst_3812_, 0);
v_toBind_3820_ = lean_ctor_get(v_inst_3812_, 1);
lean_inc_n(v_toBind_3820_, 3);
v_toPure_3821_ = lean_ctor_get(v_toApplicative_3819_, 1);
lean_inc_n(v_toPure_3821_, 4);
v_toMonadRef_3822_ = lean_ctor_get(v_inst_3814_, 1);
lean_inc_ref(v_toMonadRef_3822_);
lean_dec_ref(v_inst_3814_);
v___x_3823_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3813_, 2);
v___x_3824_ = lean_apply_2(v_inst_3813_, lean_box(0), v___x_3823_);
v___f_3825_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3825_, 0, v_toPure_3821_);
v___f_3826_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3826_, 0, v_inst_3813_);
lean_closure_set(v___f_3826_, 1, v_toBind_3820_);
lean_closure_set(v___f_3826_, 2, v___f_3825_);
lean_closure_set(v___f_3826_, 3, v_toPure_3821_);
v___f_3827_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3827_, 0, v_toPure_3821_);
v___f_3828_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3828_, 0, v_toPure_3821_);
lean_closure_set(v___f_3828_, 1, v_inst_3813_);
lean_closure_set(v___f_3828_, 2, v_toBind_3820_);
lean_closure_set(v___f_3828_, 3, v_inst_3815_);
lean_closure_set(v___f_3828_, 4, v_inst_3812_);
lean_closure_set(v___f_3828_, 5, v_toMonadRef_3822_);
lean_closure_set(v___f_3828_, 6, v_inst_3817_);
lean_closure_set(v___f_3828_, 7, v_inst_3816_);
lean_closure_set(v___f_3828_, 8, v_f_3818_);
lean_closure_set(v___f_3828_, 9, v___f_3827_);
lean_closure_set(v___f_3828_, 10, v___f_3826_);
v___x_3829_ = lean_apply_4(v_toBind_3820_, lean_box(0), lean_box(0), v___x_3824_, v___f_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3830_, lean_object* v_inst_3831_, lean_object* v_inst_3832_, lean_object* v_inst_3833_, lean_object* v_inst_3834_, lean_object* v_inst_3835_, lean_object* v_inst_3836_, lean_object* v_inst_3837_, lean_object* v_inst_3838_, lean_object* v_f_3839_){
_start:
{
lean_object* v_toApplicative_3840_; lean_object* v_toBind_3841_; lean_object* v_toPure_3842_; lean_object* v_toMonadRef_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___f_3848_; lean_object* v___f_3849_; lean_object* v___x_3850_; 
v_toApplicative_3840_ = lean_ctor_get(v_inst_3831_, 0);
v_toBind_3841_ = lean_ctor_get(v_inst_3831_, 1);
lean_inc_n(v_toBind_3841_, 3);
v_toPure_3842_ = lean_ctor_get(v_toApplicative_3840_, 1);
lean_inc_n(v_toPure_3842_, 4);
v_toMonadRef_3843_ = lean_ctor_get(v_inst_3833_, 1);
lean_inc_ref(v_toMonadRef_3843_);
lean_dec_ref(v_inst_3833_);
v___x_3844_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3832_, 2);
v___x_3845_ = lean_apply_2(v_inst_3832_, lean_box(0), v___x_3844_);
v___f_3846_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3846_, 0, v_toPure_3842_);
v___f_3847_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3847_, 0, v_inst_3832_);
lean_closure_set(v___f_3847_, 1, v_toBind_3841_);
lean_closure_set(v___f_3847_, 2, v___f_3846_);
lean_closure_set(v___f_3847_, 3, v_toPure_3842_);
v___f_3848_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3848_, 0, v_toPure_3842_);
v___f_3849_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3849_, 0, v_toPure_3842_);
lean_closure_set(v___f_3849_, 1, v_inst_3832_);
lean_closure_set(v___f_3849_, 2, v_toBind_3841_);
lean_closure_set(v___f_3849_, 3, v_inst_3835_);
lean_closure_set(v___f_3849_, 4, v_inst_3831_);
lean_closure_set(v___f_3849_, 5, v_toMonadRef_3843_);
lean_closure_set(v___f_3849_, 6, v_inst_3837_);
lean_closure_set(v___f_3849_, 7, v_inst_3836_);
lean_closure_set(v___f_3849_, 8, v_f_3839_);
lean_closure_set(v___f_3849_, 9, v___f_3848_);
lean_closure_set(v___f_3849_, 10, v___f_3847_);
v___x_3850_ = lean_apply_4(v_toBind_3841_, lean_box(0), lean_box(0), v___x_3845_, v___f_3849_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3851_, lean_object* v_inst_3852_, lean_object* v_inst_3853_, lean_object* v_inst_3854_, lean_object* v_inst_3855_, lean_object* v_inst_3856_, lean_object* v_inst_3857_, lean_object* v_inst_3858_, lean_object* v_inst_3859_, lean_object* v_f_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3851_, v_inst_3852_, v_inst_3853_, v_inst_3854_, v_inst_3855_, v_inst_3856_, v_inst_3857_, v_inst_3858_, v_inst_3859_, v_f_3860_);
lean_dec_ref(v_inst_3859_);
lean_dec_ref(v_inst_3855_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3862_, lean_object* v_x_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_apply_1(v_f_3862_, v___y_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3866_, lean_object* v_inst_3867_, lean_object* v___f_3868_, lean_object* v_hyps_3869_){
_start:
{
lean_object* v_toPure_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v_toPure_3870_ = lean_ctor_get(v_toApplicative_3866_, 1);
lean_inc(v_toPure_3870_);
lean_dec_ref(v_toApplicative_3866_);
v___x_3871_ = lean_unsigned_to_nat(0u);
v___x_3872_ = lean_array_get_size(v_hyps_3869_);
v___x_3873_ = lean_box(0);
v___x_3874_ = lean_nat_dec_lt(v___x_3871_, v___x_3872_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_dec_ref(v_hyps_3869_);
lean_dec(v___f_3868_);
lean_dec_ref(v_inst_3867_);
v___x_3875_ = lean_apply_2(v_toPure_3870_, lean_box(0), v___x_3873_);
return v___x_3875_;
}
else
{
uint8_t v___x_3876_; 
v___x_3876_ = lean_nat_dec_le(v___x_3872_, v___x_3872_);
if (v___x_3876_ == 0)
{
if (v___x_3874_ == 0)
{
lean_object* v___x_3877_; 
lean_dec_ref(v_hyps_3869_);
lean_dec(v___f_3868_);
lean_dec_ref(v_inst_3867_);
v___x_3877_ = lean_apply_2(v_toPure_3870_, lean_box(0), v___x_3873_);
return v___x_3877_;
}
else
{
size_t v___x_3878_; size_t v___x_3879_; lean_object* v___x_3880_; 
lean_dec(v_toPure_3870_);
v___x_3878_ = ((size_t)0ULL);
v___x_3879_ = lean_usize_of_nat(v___x_3872_);
v___x_3880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3867_, v___f_3868_, v_hyps_3869_, v___x_3878_, v___x_3879_, v___x_3873_);
return v___x_3880_;
}
}
else
{
size_t v___x_3881_; size_t v___x_3882_; lean_object* v___x_3883_; 
lean_dec(v_toPure_3870_);
v___x_3881_ = ((size_t)0ULL);
v___x_3882_ = lean_usize_of_nat(v___x_3872_);
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3867_, v___f_3868_, v_hyps_3869_, v___x_3881_, v___x_3882_, v___x_3873_);
return v___x_3883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3884_, lean_object* v_inst_3885_, lean_object* v_f_3886_){
_start:
{
lean_object* v_toApplicative_3887_; lean_object* v_toBind_3888_; lean_object* v___f_3889_; lean_object* v___f_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v_toApplicative_3887_ = lean_ctor_get(v_inst_3884_, 0);
lean_inc_ref(v_toApplicative_3887_);
v_toBind_3888_ = lean_ctor_get(v_inst_3884_, 1);
lean_inc(v_toBind_3888_);
v___f_3889_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3889_, 0, v_f_3886_);
v___f_3890_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3890_, 0, v_toApplicative_3887_);
lean_closure_set(v___f_3890_, 1, v_inst_3884_);
lean_closure_set(v___f_3890_, 2, v___f_3889_);
v___x_3891_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3892_ = lean_apply_2(v_inst_3885_, lean_box(0), v___x_3891_);
v___x_3893_ = lean_apply_4(v_toBind_3888_, lean_box(0), lean_box(0), v___x_3892_, v___f_3890_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3894_, lean_object* v_inst_3895_, lean_object* v_inst_3896_, lean_object* v_inst_3897_, lean_object* v_f_3898_){
_start:
{
lean_object* v_toApplicative_3899_; lean_object* v_toBind_3900_; lean_object* v___f_3901_; lean_object* v___f_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_toApplicative_3899_ = lean_ctor_get(v_inst_3895_, 0);
lean_inc_ref(v_toApplicative_3899_);
v_toBind_3900_ = lean_ctor_get(v_inst_3895_, 1);
lean_inc(v_toBind_3900_);
v___f_3901_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3901_, 0, v_f_3898_);
v___f_3902_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3902_, 0, v_toApplicative_3899_);
lean_closure_set(v___f_3902_, 1, v_inst_3895_);
lean_closure_set(v___f_3902_, 2, v___f_3901_);
v___x_3903_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3904_ = lean_apply_2(v_inst_3896_, lean_box(0), v___x_3903_);
v___x_3905_ = lean_apply_4(v_toBind_3900_, lean_box(0), lean_box(0), v___x_3904_, v___f_3902_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3906_, lean_object* v_inst_3907_, lean_object* v_inst_3908_, lean_object* v_inst_3909_, lean_object* v_f_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3906_, v_inst_3907_, v_inst_3908_, v_inst_3909_, v_f_3910_);
lean_dec_ref(v_inst_3909_);
return v_res_3911_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_3914_, lean_object* v_methods_3915_, lean_object* v_config_3916_, lean_object* v_hyp_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v___x_3926_; lean_object* v_caches_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v_typeAnalysis_3934_; lean_object* v_target_3935_; lean_object* v_hypotheses_3936_; uint8_t v_didChange_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3978_; 
v___x_3926_ = lean_st_ref_get(v_a_3918_);
v_caches_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc_ref(v_caches_3927_);
lean_dec(v___x_3926_);
v___x_3928_ = lean_unsigned_to_nat(0u);
v___x_3929_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_3914_, v_caches_3927_);
v___x_3930_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_3931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3928_);
lean_ctor_set(v___x_3931_, 1, v___x_3929_);
lean_ctor_set(v___x_3931_, 2, v___x_3930_);
lean_ctor_set(v___x_3931_, 3, v___x_3930_);
v___x_3932_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3914_, v___x_3930_, v_caches_3927_);
v___x_3933_ = lean_st_ref_take(v_a_3918_);
v_typeAnalysis_3934_ = lean_ctor_get(v___x_3933_, 1);
v_target_3935_ = lean_ctor_get(v___x_3933_, 2);
v_hypotheses_3936_ = lean_ctor_get(v___x_3933_, 3);
v_didChange_3937_ = lean_ctor_get_uint8(v___x_3933_, sizeof(void*)*4);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; 
v_unused_3979_ = lean_ctor_get(v___x_3933_, 0);
lean_dec(v_unused_3979_);
v___x_3939_ = v___x_3933_;
v_isShared_3940_ = v_isSharedCheck_3978_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_hypotheses_3936_);
lean_inc(v_target_3935_);
lean_inc(v_typeAnalysis_3934_);
lean_dec(v___x_3933_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3978_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v___x_3932_);
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_typeAnalysis_3934_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_target_3935_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v_hypotheses_3936_);
lean_ctor_set_uint8(v_reuseFailAlloc_3977_, sizeof(void*)*4, v_didChange_3937_);
v___x_3942_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; lean_object* v_type_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3943_ = lean_st_ref_put(v_a_3918_, v___x_3942_);
v_type_3944_ = lean_ctor_get(v_hyp_3917_, 1);
lean_inc_ref(v_type_3944_);
v___x_3945_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3945_, 0, v_type_3944_);
v___x_3946_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3945_, v_methods_3915_, v_config_3916_, v___x_3931_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v_fst_3948_; lean_object* v_snd_3949_; lean_object* v___x_3950_; lean_object* v_caches_3951_; lean_object* v_persistentCache_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v_typeAnalysis_3955_; lean_object* v_target_3956_; lean_object* v_hypotheses_3957_; uint8_t v_didChange_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3967_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___x_3946_, 1);
v_fst_3948_ = lean_ctor_get(v_a_3947_, 0);
lean_inc(v_fst_3948_);
v_snd_3949_ = lean_ctor_get(v_a_3947_, 1);
lean_inc(v_snd_3949_);
lean_dec(v_a_3947_);
v___x_3950_ = lean_st_ref_get(v_a_3918_);
v_caches_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc_ref(v_caches_3951_);
lean_dec(v___x_3950_);
v_persistentCache_3952_ = lean_ctor_get(v_snd_3949_, 1);
lean_inc_ref(v_persistentCache_3952_);
lean_dec(v_snd_3949_);
v___x_3953_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3914_, v_persistentCache_3952_, v_caches_3951_);
v___x_3954_ = lean_st_ref_take(v_a_3918_);
v_typeAnalysis_3955_ = lean_ctor_get(v___x_3954_, 1);
v_target_3956_ = lean_ctor_get(v___x_3954_, 2);
v_hypotheses_3957_ = lean_ctor_get(v___x_3954_, 3);
v_didChange_3958_ = lean_ctor_get_uint8(v___x_3954_, sizeof(void*)*4);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3967_ == 0)
{
lean_object* v_unused_3968_; 
v_unused_3968_ = lean_ctor_get(v___x_3954_, 0);
lean_dec(v_unused_3968_);
v___x_3960_ = v___x_3954_;
v_isShared_3961_ = v_isSharedCheck_3967_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_hypotheses_3957_);
lean_inc(v_target_3956_);
lean_inc(v_typeAnalysis_3955_);
lean_dec(v___x_3954_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3967_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3953_);
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3953_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_typeAnalysis_3955_);
lean_ctor_set(v_reuseFailAlloc_3966_, 2, v_target_3956_);
lean_ctor_set(v_reuseFailAlloc_3966_, 3, v_hypotheses_3957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3966_, sizeof(void*)*4, v_didChange_3958_);
v___x_3963_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = lean_st_ref_put(v_a_3918_, v___x_3963_);
v___x_3965_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_3917_, v_fst_3948_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
return v___x_3965_;
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec_ref(v_hyp_3917_);
v_a_3969_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3946_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3946_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_3980_, lean_object* v_methods_3981_, lean_object* v_config_3982_, lean_object* v_hyp_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
uint8_t v_cacheId_boxed_3992_; lean_object* v_res_3993_; 
v_cacheId_boxed_3992_ = lean_unbox(v_cacheId_3980_);
v_res_3993_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_3992_, v_methods_3981_, v_config_3982_, v_hyp_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_3994_, lean_object* v_methods_3995_, lean_object* v_config_3996_, lean_object* v_hyp_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_3994_, v_methods_3995_, v_config_3996_, v_hyp_3997_, v_a_3999_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4011_, lean_object* v_methods_4012_, lean_object* v_config_4013_, lean_object* v_hyp_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
uint8_t v_cacheId_boxed_4027_; lean_object* v_res_4028_; 
v_cacheId_boxed_4027_ = lean_unbox(v_cacheId_4011_);
v_res_4028_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4027_, v_methods_4012_, v_config_4013_, v_hyp_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4029_, lean_object* v_methods_4030_, lean_object* v_config_4031_, lean_object* v_hyp_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_){
_start:
{
lean_object* v___x_4041_; lean_object* v_caches_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v_typeAnalysis_4049_; lean_object* v_target_4050_; lean_object* v_hypotheses_4051_; uint8_t v_didChange_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4093_; 
v___x_4041_ = lean_st_ref_get(v_a_4033_);
v_caches_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc_ref(v_caches_4042_);
lean_dec(v___x_4041_);
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4029_, v_caches_4042_);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4047_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4029_, v___x_4046_, v_caches_4042_);
v___x_4048_ = lean_st_ref_take(v_a_4033_);
v_typeAnalysis_4049_ = lean_ctor_get(v___x_4048_, 1);
v_target_4050_ = lean_ctor_get(v___x_4048_, 2);
v_hypotheses_4051_ = lean_ctor_get(v___x_4048_, 3);
v_didChange_4052_ = lean_ctor_get_uint8(v___x_4048_, sizeof(void*)*4);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v___x_4048_, 0);
lean_dec(v_unused_4094_);
v___x_4054_ = v___x_4048_;
v_isShared_4055_ = v_isSharedCheck_4093_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_hypotheses_4051_);
lean_inc(v_target_4050_);
lean_inc(v_typeAnalysis_4049_);
lean_dec(v___x_4048_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4093_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 0, v___x_4047_);
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_typeAnalysis_4049_);
lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_target_4050_);
lean_ctor_set(v_reuseFailAlloc_4092_, 3, v_hypotheses_4051_);
lean_ctor_set_uint8(v_reuseFailAlloc_4092_, sizeof(void*)*4, v_didChange_4052_);
v___x_4057_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4058_; lean_object* v_type_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4058_ = lean_st_ref_put(v_a_4033_, v___x_4057_);
v_type_4059_ = lean_ctor_get(v_hyp_4032_, 1);
lean_inc_ref(v_type_4059_);
v___x_4060_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4060_, 0, v_type_4059_);
v___x_4061_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4060_, v_methods_4030_, v_config_4031_, v___x_4045_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v_fst_4063_; lean_object* v_snd_4064_; lean_object* v___x_4065_; lean_object* v_caches_4066_; lean_object* v_cache_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v_typeAnalysis_4070_; lean_object* v_target_4071_; lean_object* v_hypotheses_4072_; uint8_t v_didChange_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4082_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v_fst_4063_ = lean_ctor_get(v_a_4062_, 0);
lean_inc(v_fst_4063_);
v_snd_4064_ = lean_ctor_get(v_a_4062_, 1);
lean_inc(v_snd_4064_);
lean_dec(v_a_4062_);
v___x_4065_ = lean_st_ref_get(v_a_4033_);
v_caches_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc_ref(v_caches_4066_);
lean_dec(v___x_4065_);
v_cache_4067_ = lean_ctor_get(v_snd_4064_, 1);
lean_inc_ref(v_cache_4067_);
lean_dec(v_snd_4064_);
v___x_4068_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4029_, v_cache_4067_, v_caches_4066_);
v___x_4069_ = lean_st_ref_take(v_a_4033_);
v_typeAnalysis_4070_ = lean_ctor_get(v___x_4069_, 1);
v_target_4071_ = lean_ctor_get(v___x_4069_, 2);
v_hypotheses_4072_ = lean_ctor_get(v___x_4069_, 3);
v_didChange_4073_ = lean_ctor_get_uint8(v___x_4069_, sizeof(void*)*4);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4082_ == 0)
{
lean_object* v_unused_4083_; 
v_unused_4083_ = lean_ctor_get(v___x_4069_, 0);
lean_dec(v_unused_4083_);
v___x_4075_ = v___x_4069_;
v_isShared_4076_ = v_isSharedCheck_4082_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_hypotheses_4072_);
lean_inc(v_target_4071_);
lean_inc(v_typeAnalysis_4070_);
lean_dec(v___x_4069_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4082_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v___x_4068_);
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v_typeAnalysis_4070_);
lean_ctor_set(v_reuseFailAlloc_4081_, 2, v_target_4071_);
lean_ctor_set(v_reuseFailAlloc_4081_, 3, v_hypotheses_4072_);
lean_ctor_set_uint8(v_reuseFailAlloc_4081_, sizeof(void*)*4, v_didChange_4073_);
v___x_4078_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = lean_st_ref_put(v_a_4033_, v___x_4078_);
v___x_4080_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4032_, v_fst_4063_);
lean_dec(v_fst_4063_);
return v___x_4080_;
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec_ref(v_hyp_4032_);
v_a_4084_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4061_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4061_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4095_, lean_object* v_methods_4096_, lean_object* v_config_4097_, lean_object* v_hyp_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
uint8_t v_cacheId_boxed_4107_; lean_object* v_res_4108_; 
v_cacheId_boxed_4107_ = lean_unbox(v_cacheId_4095_);
v_res_4108_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4107_, v_methods_4096_, v_config_4097_, v_hyp_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4109_, lean_object* v_methods_4110_, lean_object* v_config_4111_, lean_object* v_hyp_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4109_, v_methods_4110_, v_config_4111_, v_hyp_4112_, v_a_4114_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4126_, lean_object* v_methods_4127_, lean_object* v_config_4128_, lean_object* v_hyp_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
uint8_t v_cacheId_boxed_4142_; lean_object* v_res_4143_; 
v_cacheId_boxed_4142_ = lean_unbox(v_cacheId_4126_);
v_res_4143_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4142_, v_methods_4127_, v_config_4128_, v_hyp_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4144_, lean_object* v_a_4145_, lean_object* v___x_4146_, lean_object* v_____r_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4160_ = lean_array_push(v_snd_4144_, v_a_4145_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4146_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4164_, lean_object* v_a_4165_, lean_object* v___x_4166_, lean_object* v_____r_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4164_, v_a_4165_, v___x_4166_, v_____r_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4181_, lean_object* v___f_4182_, lean_object* v_____r_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; lean_object* v_caches_4197_; lean_object* v_typeAnalysis_4198_; lean_object* v_target_4199_; lean_object* v_hypotheses_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4210_; 
v___x_4196_ = lean_st_ref_take(v___y_4185_);
v_caches_4197_ = lean_ctor_get(v___x_4196_, 0);
v_typeAnalysis_4198_ = lean_ctor_get(v___x_4196_, 1);
v_target_4199_ = lean_ctor_get(v___x_4196_, 2);
v_hypotheses_4200_ = lean_ctor_get(v___x_4196_, 3);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4202_ = v___x_4196_;
v_isShared_4203_ = v_isSharedCheck_4210_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_hypotheses_4200_);
lean_inc(v_target_4199_);
lean_inc(v_typeAnalysis_4198_);
lean_inc(v_caches_4197_);
lean_dec(v___x_4196_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4210_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4204_; lean_object* v___x_4206_; 
v___x_4204_ = lean_box(0);
if (v_isShared_4203_ == 0)
{
v___x_4206_ = v___x_4202_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_caches_4197_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_typeAnalysis_4198_);
lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_target_4199_);
lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_hypotheses_4200_);
v___x_4206_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*4, v___x_4181_);
v___x_4207_ = lean_st_ref_put(v___y_4185_, v___x_4206_);
lean_inc(v___y_4194_);
lean_inc_ref(v___y_4193_);
lean_inc(v___y_4192_);
lean_inc_ref(v___y_4191_);
lean_inc(v___y_4190_);
lean_inc_ref(v___y_4189_);
lean_inc(v___y_4188_);
lean_inc_ref(v___y_4187_);
lean_inc(v___y_4186_);
lean_inc(v___y_4185_);
lean_inc_ref(v___y_4184_);
v___x_4208_ = lean_apply_13(v___f_4182_, v___x_4204_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, lean_box(0));
return v___x_4208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4211_, lean_object* v___f_4212_, lean_object* v_____r_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v___x_22285__boxed_4226_; lean_object* v_res_4227_; 
v___x_22285__boxed_4226_ = lean_unbox(v___x_4211_);
v_res_4227_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22285__boxed_4226_, v___f_4212_, v_____r_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4228_, lean_object* v_hypotheses_4229_, uint8_t v_cacheId_4230_, lean_object* v_methods_4231_, lean_object* v_config_4232_, lean_object* v___x_4233_, lean_object* v___x_4234_, lean_object* v___x_4235_, lean_object* v_toMonadRef_4236_, lean_object* v___f_4237_, lean_object* v_next_4238_, lean_object* v_acc_4239_, lean_object* v_h_4240_, lean_object* v_G_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___y_4255_; uint8_t v___x_4277_; 
v___x_4277_ = lean_nat_dec_lt(v_next_4238_, v___x_4228_);
if (v___x_4277_ == 0)
{
lean_object* v___x_4278_; 
lean_dec_ref(v_G_4241_);
lean_dec(v___f_4237_);
lean_dec_ref(v_toMonadRef_4236_);
lean_dec_ref(v___x_4235_);
lean_dec_ref(v___x_4234_);
lean_dec(v___x_4233_);
lean_dec_ref(v_config_4232_);
lean_dec_ref(v_methods_4231_);
v___x_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4278_, 0, v_acc_4239_);
return v___x_4278_;
}
else
{
lean_object* v_snd_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4353_; 
v_snd_4279_ = lean_ctor_get(v_acc_4239_, 1);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_acc_4239_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v_acc_4239_, 0);
lean_dec(v_unused_4354_);
v___x_4281_ = v_acc_4239_;
v_isShared_4282_ = v_isSharedCheck_4353_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_snd_4279_);
lean_dec(v_acc_4239_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4353_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = lean_array_fget_borrowed(v_hypotheses_4229_, v_next_4238_);
lean_inc(v___x_4283_);
v___x_4284_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4230_, v_methods_4231_, v_config_4232_, v___x_4283_, v___y_4243_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; lean_object* v_type_4286_; lean_object* v_value_4287_; uint8_t v___x_4288_; 
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___x_4284_, 1);
v_type_4286_ = lean_ctor_get(v_a_4285_, 1);
v_value_4287_ = lean_ctor_get(v_a_4285_, 2);
lean_inc_ref(v_type_4286_);
v___x_4288_ = l_Lean_Expr_isFalse(v_type_4286_);
if (v___x_4288_ == 0)
{
lean_object* v_type_4289_; lean_object* v___f_4290_; uint8_t v___x_4320_; 
lean_del_object(v___x_4281_);
v_type_4289_ = lean_ctor_get(v___x_4283_, 1);
lean_inc(v___x_4233_);
lean_inc(v_a_4285_);
lean_inc(v_snd_4279_);
v___f_4290_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4290_, 0, v_snd_4279_);
lean_closure_set(v___f_4290_, 1, v_a_4285_);
lean_closure_set(v___f_4290_, 2, v___x_4233_);
v___x_4320_ = lean_expr_eqv(v_type_4289_, v_type_4286_);
if (v___x_4320_ == 0)
{
lean_inc_ref(v_type_4286_);
lean_dec(v_a_4285_);
lean_dec(v_snd_4279_);
lean_dec(v___x_4233_);
goto v___jp_4294_;
}
else
{
if (v___x_4288_ == 0)
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
lean_dec_ref(v___f_4290_);
lean_dec(v___f_4237_);
lean_dec_ref(v_toMonadRef_4236_);
lean_dec_ref(v___x_4235_);
lean_dec_ref(v___x_4234_);
v___x_4321_ = lean_box(0);
v___x_4322_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4279_, v_a_4285_, v___x_4233_, v___x_4321_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
v___y_4255_ = v___x_4322_;
goto v___jp_4254_;
}
else
{
lean_inc_ref(v_type_4286_);
lean_dec(v_a_4285_);
lean_dec(v_snd_4279_);
lean_dec(v___x_4233_);
goto v___jp_4294_;
}
}
v___jp_4291_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4292_ = lean_box(0);
v___x_4293_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4277_, v___f_4290_, v___x_4292_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
v___y_4255_ = v___x_4293_;
goto v___jp_4254_;
}
v___jp_4294_:
{
lean_object* v_toCold_4295_; lean_object* v_options_4296_; uint8_t v_hasTrace_4297_; 
v_toCold_4295_ = lean_ctor_get(v___y_4251_, 0);
v_options_4296_ = lean_ctor_get(v_toCold_4295_, 2);
v_hasTrace_4297_ = lean_ctor_get_uint8(v_options_4296_, sizeof(void*)*1);
if (v_hasTrace_4297_ == 0)
{
lean_dec_ref(v_type_4286_);
lean_dec(v___f_4237_);
lean_dec_ref(v_toMonadRef_4236_);
lean_dec_ref(v___x_4235_);
lean_dec_ref(v___x_4234_);
goto v___jp_4291_;
}
else
{
lean_object* v_inheritedTraceOptions_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v_inheritedTraceOptions_4298_ = lean_ctor_get(v_toCold_4295_, 11);
v___x_4299_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4300_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4301_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4298_, v_options_4296_, v___x_4300_);
if (v___x_4301_ == 0)
{
lean_dec_ref(v_type_4286_);
lean_dec(v___f_4237_);
lean_dec_ref(v_toMonadRef_4236_);
lean_dec_ref(v___x_4235_);
lean_dec_ref(v___x_4234_);
goto v___jp_4291_;
}
else
{
lean_object* v_type_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_22210__overap_4308_; lean_object* v___x_4309_; 
v_type_4302_ = lean_ctor_get(v___x_4283_, 1);
lean_inc_ref(v_type_4302_);
v___x_4303_ = l_Lean_MessageData_ofExpr(v_type_4302_);
v___x_4304_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = l_Lean_MessageData_ofExpr(v_type_4286_);
v___x_4307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4305_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_22210__overap_4308_ = l_Lean_addTrace___redArg(v___x_4234_, v___x_4235_, v_toMonadRef_4236_, v___f_4237_, v___x_4299_, v___x_4307_);
lean_inc(v___y_4252_);
lean_inc_ref(v___y_4251_);
lean_inc(v___y_4250_);
lean_inc_ref(v___y_4249_);
lean_inc(v___y_4248_);
lean_inc_ref(v___y_4247_);
lean_inc(v___y_4246_);
lean_inc_ref(v___y_4245_);
lean_inc(v___y_4244_);
lean_inc(v___y_4243_);
lean_inc_ref(v___y_4242_);
v___x_4309_ = lean_apply_12(v___x_22210__overap_4308_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, lean_box(0));
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
v___x_4311_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4277_, v___f_4290_, v_a_4310_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
v___y_4255_ = v___x_4311_;
goto v___jp_4254_;
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec_ref(v___f_4290_);
lean_dec_ref(v_G_4241_);
v_a_4312_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4309_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4309_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4323_; 
lean_inc_ref(v_value_4287_);
lean_dec(v_a_4285_);
lean_dec_ref(v_G_4241_);
lean_dec(v___f_4237_);
lean_dec_ref(v_toMonadRef_4236_);
lean_dec_ref(v___x_4235_);
lean_dec_ref(v___x_4234_);
lean_dec(v___x_4233_);
v___x_4323_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4287_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4335_; 
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4335_ == 0)
{
lean_object* v_unused_4336_; 
v_unused_4336_ = lean_ctor_get(v___x_4323_, 0);
lean_dec(v_unused_4336_);
v___x_4325_ = v___x_4323_;
v_isShared_4326_ = v_isSharedCheck_4335_;
goto v_resetjp_4324_;
}
else
{
lean_dec(v___x_4323_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4335_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4330_; 
v___x_4327_ = lean_box(v___x_4277_);
v___x_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4327_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4328_);
v___x_4330_ = v___x_4281_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4328_);
lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_snd_4279_);
v___x_4330_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
lean_object* v___x_4332_; 
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 0, v___x_4330_);
v___x_4332_ = v___x_4325_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4330_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_del_object(v___x_4281_);
lean_dec(v_snd_4279_);
v_a_4337_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4323_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4323_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
else
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
lean_del_object(v___x_4281_);
lean_dec(v_snd_4279_);
lean_dec_ref(v_G_4241_);
lean_dec(v___f_4237_);
lean_dec_ref(v_toMonadRef_4236_);
lean_dec_ref(v___x_4235_);
lean_dec_ref(v___x_4234_);
lean_dec(v___x_4233_);
v_a_4345_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4347_ = v___x_4284_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v___x_4284_);
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
v___jp_4254_:
{
if (lean_obj_tag(v___y_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4268_; 
v_a_4256_ = lean_ctor_get(v___y_4255_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___y_4255_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4258_ = v___y_4255_;
v_isShared_4259_ = v_isSharedCheck_4268_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___y_4255_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4268_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
if (lean_obj_tag(v_a_4256_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; 
lean_dec_ref(v_G_4241_);
v_a_4260_ = lean_ctor_get(v_a_4256_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v_a_4256_, 1);
if (v_isShared_4259_ == 0)
{
lean_ctor_set(v___x_4258_, 0, v_a_4260_);
v___x_4262_ = v___x_4258_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_del_object(v___x_4258_);
v_a_4264_ = lean_ctor_get(v_a_4256_, 0);
lean_inc(v_a_4264_);
lean_dec_ref_known(v_a_4256_, 1);
v___x_4265_ = lean_unsigned_to_nat(1u);
v___x_4266_ = lean_nat_add(v_next_4238_, v___x_4265_);
lean_inc(v___y_4252_);
lean_inc_ref(v___y_4251_);
lean_inc(v___y_4250_);
lean_inc_ref(v___y_4249_);
lean_inc(v___y_4248_);
lean_inc_ref(v___y_4247_);
lean_inc(v___y_4246_);
lean_inc_ref(v___y_4245_);
lean_inc(v___y_4244_);
lean_inc(v___y_4243_);
lean_inc_ref(v___y_4242_);
v___x_4267_ = lean_apply_16(v_G_4241_, v___x_4266_, v_a_4264_, lean_box(0), lean_box(0), v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, lean_box(0));
return v___x_4267_;
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v_G_4241_);
v_a_4269_ = lean_ctor_get(v___y_4255_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___y_4255_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___y_4255_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___y_4255_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4355_ = _args[0];
lean_object* v_hypotheses_4356_ = _args[1];
lean_object* v_cacheId_4357_ = _args[2];
lean_object* v_methods_4358_ = _args[3];
lean_object* v_config_4359_ = _args[4];
lean_object* v___x_4360_ = _args[5];
lean_object* v___x_4361_ = _args[6];
lean_object* v___x_4362_ = _args[7];
lean_object* v_toMonadRef_4363_ = _args[8];
lean_object* v___f_4364_ = _args[9];
lean_object* v_next_4365_ = _args[10];
lean_object* v_acc_4366_ = _args[11];
lean_object* v_h_4367_ = _args[12];
lean_object* v_G_4368_ = _args[13];
lean_object* v___y_4369_ = _args[14];
lean_object* v___y_4370_ = _args[15];
lean_object* v___y_4371_ = _args[16];
lean_object* v___y_4372_ = _args[17];
lean_object* v___y_4373_ = _args[18];
lean_object* v___y_4374_ = _args[19];
lean_object* v___y_4375_ = _args[20];
lean_object* v___y_4376_ = _args[21];
lean_object* v___y_4377_ = _args[22];
lean_object* v___y_4378_ = _args[23];
lean_object* v___y_4379_ = _args[24];
lean_object* v___y_4380_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4381_; lean_object* v_res_4382_; 
v_cacheId_boxed_4381_ = lean_unbox(v_cacheId_4357_);
v_res_4382_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4355_, v_hypotheses_4356_, v_cacheId_boxed_4381_, v_methods_4358_, v_config_4359_, v___x_4360_, v___x_4361_, v___x_4362_, v_toMonadRef_4363_, v___f_4364_, v_next_4365_, v_acc_4366_, v_h_4367_, v_G_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v_next_4365_);
lean_dec_ref(v_hypotheses_4356_);
lean_dec(v___x_4355_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4383_, lean_object* v_methods_4384_, lean_object* v_config_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v___x_4398_; lean_object* v_toApplicative_4399_; lean_object* v_toFunctor_4400_; lean_object* v_toSeq_4401_; lean_object* v_toSeqLeft_4402_; lean_object* v_toSeqRight_4403_; lean_object* v___f_4404_; lean_object* v___f_4405_; lean_object* v___f_4406_; lean_object* v___f_4407_; lean_object* v___x_4408_; lean_object* v___f_4409_; lean_object* v___f_4410_; lean_object* v___f_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v_toApplicative_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4502_; 
v___x_4398_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4399_ = lean_ctor_get(v___x_4398_, 0);
v_toFunctor_4400_ = lean_ctor_get(v_toApplicative_4399_, 0);
v_toSeq_4401_ = lean_ctor_get(v_toApplicative_4399_, 2);
v_toSeqLeft_4402_ = lean_ctor_get(v_toApplicative_4399_, 3);
v_toSeqRight_4403_ = lean_ctor_get(v_toApplicative_4399_, 4);
v___f_4404_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4405_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4400_, 2);
v___f_4406_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4406_, 0, v_toFunctor_4400_);
v___f_4407_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4407_, 0, v_toFunctor_4400_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___f_4406_);
lean_ctor_set(v___x_4408_, 1, v___f_4407_);
lean_inc(v_toSeqRight_4403_);
v___f_4409_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4409_, 0, v_toSeqRight_4403_);
lean_inc(v_toSeqLeft_4402_);
v___f_4410_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4410_, 0, v_toSeqLeft_4402_);
lean_inc(v_toSeq_4401_);
v___f_4411_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4411_, 0, v_toSeq_4401_);
v___x_4412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4408_);
lean_ctor_set(v___x_4412_, 1, v___f_4404_);
lean_ctor_set(v___x_4412_, 2, v___f_4411_);
lean_ctor_set(v___x_4412_, 3, v___f_4410_);
lean_ctor_set(v___x_4412_, 4, v___f_4409_);
v___x_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
lean_ctor_set(v___x_4413_, 1, v___f_4405_);
v___x_4414_ = l_StateRefT_x27_instMonad___redArg(v___x_4413_);
v_toApplicative_4415_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; 
v_unused_4503_ = lean_ctor_get(v___x_4414_, 1);
lean_dec(v_unused_4503_);
v___x_4417_ = v___x_4414_;
v_isShared_4418_ = v_isSharedCheck_4502_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_toApplicative_4415_);
lean_dec(v___x_4414_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4502_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v_toFunctor_4419_; lean_object* v_toSeq_4420_; lean_object* v_toSeqLeft_4421_; lean_object* v_toSeqRight_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4500_; 
v_toFunctor_4419_ = lean_ctor_get(v_toApplicative_4415_, 0);
v_toSeq_4420_ = lean_ctor_get(v_toApplicative_4415_, 2);
v_toSeqLeft_4421_ = lean_ctor_get(v_toApplicative_4415_, 3);
v_toSeqRight_4422_ = lean_ctor_get(v_toApplicative_4415_, 4);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_toApplicative_4415_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v_toApplicative_4415_, 1);
lean_dec(v_unused_4501_);
v___x_4424_ = v_toApplicative_4415_;
v_isShared_4425_ = v_isSharedCheck_4500_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_toSeqRight_4422_);
lean_inc(v_toSeqLeft_4421_);
lean_inc(v_toSeq_4420_);
lean_inc(v_toFunctor_4419_);
lean_dec(v_toApplicative_4415_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4500_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___f_4426_; lean_object* v___f_4427_; lean_object* v___f_4428_; lean_object* v___f_4429_; lean_object* v___x_4430_; lean_object* v___f_4431_; lean_object* v___f_4432_; lean_object* v___f_4433_; lean_object* v___x_4435_; 
v___f_4426_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4427_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4419_);
v___f_4428_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4428_, 0, v_toFunctor_4419_);
v___f_4429_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4429_, 0, v_toFunctor_4419_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___f_4428_);
lean_ctor_set(v___x_4430_, 1, v___f_4429_);
v___f_4431_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4431_, 0, v_toSeqRight_4422_);
v___f_4432_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4432_, 0, v_toSeqLeft_4421_);
v___f_4433_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4433_, 0, v_toSeq_4420_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 4, v___f_4431_);
lean_ctor_set(v___x_4424_, 3, v___f_4432_);
lean_ctor_set(v___x_4424_, 2, v___f_4433_);
lean_ctor_set(v___x_4424_, 1, v___f_4426_);
lean_ctor_set(v___x_4424_, 0, v___x_4430_);
v___x_4435_ = v___x_4424_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4430_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___f_4426_);
lean_ctor_set(v_reuseFailAlloc_4499_, 2, v___f_4433_);
lean_ctor_set(v_reuseFailAlloc_4499_, 3, v___f_4432_);
lean_ctor_set(v_reuseFailAlloc_4499_, 4, v___f_4431_);
v___x_4435_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4437_; 
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 1, v___f_4427_);
lean_ctor_set(v___x_4417_, 0, v___x_4435_);
v___x_4437_ = v___x_4417_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4435_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v___f_4427_);
v___x_4437_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v_toMonadRef_4446_; lean_object* v___f_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v_hypotheses_4450_; lean_object* v___x_4451_; lean_object* v_newHyps_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___f_4456_; lean_object* v___x_4457_; lean_object* v___x_22108__overap_4458_; lean_object* v___x_4459_; 
v___x_4438_ = l_StateRefT_x27_instMonad___redArg(v___x_4437_);
v___x_4439_ = l_ReaderT_instMonad___redArg(v___x_4438_);
v___x_4440_ = l_StateRefT_x27_instMonad___redArg(v___x_4439_);
v___x_4441_ = l_ReaderT_instMonad___redArg(v___x_4440_);
v___x_4442_ = l_ReaderT_instMonad___redArg(v___x_4441_);
v___x_4443_ = l_StateRefT_x27_instMonad___redArg(v___x_4442_);
v___x_4444_ = l_ReaderT_instMonad___redArg(v___x_4443_);
v___x_4445_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4446_ = lean_ctor_get(v___x_4445_, 0);
v___f_4447_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4448_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4449_ = lean_st_ref_get(v_a_4387_);
v_hypotheses_4450_ = lean_ctor_get(v___x_4449_, 3);
lean_inc_ref(v_hypotheses_4450_);
lean_dec(v___x_4449_);
v___x_4451_ = lean_array_get_size(v_hypotheses_4450_);
v_newHyps_4452_ = lean_mk_empty_array_with_capacity(v___x_4451_);
v___x_4453_ = lean_unsigned_to_nat(0u);
v___x_4454_ = lean_box(0);
v___x_4455_ = lean_box(v_cacheId_4383_);
lean_inc_ref(v_toMonadRef_4446_);
v___f_4456_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4456_, 0, v___x_4451_);
lean_closure_set(v___f_4456_, 1, v_hypotheses_4450_);
lean_closure_set(v___f_4456_, 2, v___x_4455_);
lean_closure_set(v___f_4456_, 3, v_methods_4384_);
lean_closure_set(v___f_4456_, 4, v_config_4385_);
lean_closure_set(v___f_4456_, 5, v___x_4454_);
lean_closure_set(v___f_4456_, 6, v___x_4444_);
lean_closure_set(v___f_4456_, 7, v___x_4448_);
lean_closure_set(v___f_4456_, 8, v_toMonadRef_4446_);
lean_closure_set(v___f_4456_, 9, v___f_4447_);
v___x_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4454_);
lean_ctor_set(v___x_4457_, 1, v_newHyps_4452_);
v___x_22108__overap_4458_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4456_, v___x_4453_, v___x_4457_, lean_box(0));
lean_inc(v_a_4396_);
lean_inc_ref(v_a_4395_);
lean_inc(v_a_4394_);
lean_inc_ref(v_a_4393_);
lean_inc(v_a_4392_);
lean_inc_ref(v_a_4391_);
lean_inc(v_a_4390_);
lean_inc_ref(v_a_4389_);
lean_inc(v_a_4388_);
lean_inc(v_a_4387_);
lean_inc_ref(v_a_4386_);
v___x_4459_ = lean_apply_12(v___x_22108__overap_4458_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, lean_box(0));
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4489_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4462_ = v___x_4459_;
v_isShared_4463_ = v_isSharedCheck_4489_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4489_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v_fst_4464_; 
v_fst_4464_ = lean_ctor_get(v_a_4460_, 0);
if (lean_obj_tag(v_fst_4464_) == 0)
{
lean_object* v_snd_4465_; lean_object* v___x_4466_; lean_object* v_caches_4467_; lean_object* v_typeAnalysis_4468_; lean_object* v_target_4469_; uint8_t v_didChange_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4483_; 
v_snd_4465_ = lean_ctor_get(v_a_4460_, 1);
lean_inc(v_snd_4465_);
lean_dec(v_a_4460_);
v___x_4466_ = lean_st_ref_take(v_a_4387_);
v_caches_4467_ = lean_ctor_get(v___x_4466_, 0);
v_typeAnalysis_4468_ = lean_ctor_get(v___x_4466_, 1);
v_target_4469_ = lean_ctor_get(v___x_4466_, 2);
v_didChange_4470_ = lean_ctor_get_uint8(v___x_4466_, sizeof(void*)*4);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4483_ == 0)
{
lean_object* v_unused_4484_; 
v_unused_4484_ = lean_ctor_get(v___x_4466_, 3);
lean_dec(v_unused_4484_);
v___x_4472_ = v___x_4466_;
v_isShared_4473_ = v_isSharedCheck_4483_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_target_4469_);
lean_inc(v_typeAnalysis_4468_);
lean_inc(v_caches_4467_);
lean_dec(v___x_4466_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4483_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 3, v_snd_4465_);
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_caches_4467_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_typeAnalysis_4468_);
lean_ctor_set(v_reuseFailAlloc_4482_, 2, v_target_4469_);
lean_ctor_set(v_reuseFailAlloc_4482_, 3, v_snd_4465_);
lean_ctor_set_uint8(v_reuseFailAlloc_4482_, sizeof(void*)*4, v_didChange_4470_);
v___x_4475_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4476_; uint8_t v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4480_; 
v___x_4476_ = lean_st_ref_put(v_a_4387_, v___x_4475_);
v___x_4477_ = 0;
v___x_4478_ = lean_box(v___x_4477_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4478_);
v___x_4480_ = v___x_4462_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
else
{
lean_object* v_val_4485_; lean_object* v___x_4487_; 
lean_inc_ref(v_fst_4464_);
lean_dec(v_a_4460_);
v_val_4485_ = lean_ctor_get(v_fst_4464_, 0);
lean_inc(v_val_4485_);
lean_dec_ref_known(v_fst_4464_, 1);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v_val_4485_);
v___x_4487_ = v___x_4462_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_val_4485_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
v_a_4490_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4459_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4459_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_4504_, lean_object* v_methods_4505_, lean_object* v_config_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
uint8_t v_cacheId_boxed_4519_; lean_object* v_res_4520_; 
v_cacheId_boxed_4519_ = lean_unbox(v_cacheId_4504_);
v_res_4520_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_4519_, v_methods_4505_, v_config_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_4521_, lean_object* v_hypotheses_4522_, uint8_t v_cacheId_4523_, lean_object* v_methods_4524_, lean_object* v_config_4525_, lean_object* v___x_4526_, lean_object* v___x_4527_, lean_object* v___x_4528_, lean_object* v_toMonadRef_4529_, lean_object* v___f_4530_, lean_object* v_next_4531_, lean_object* v_acc_4532_, lean_object* v_h_4533_, lean_object* v_G_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v___y_4548_; uint8_t v___x_4570_; 
v___x_4570_ = lean_nat_dec_lt(v_next_4531_, v___x_4521_);
if (v___x_4570_ == 0)
{
lean_object* v___x_4571_; 
lean_dec_ref(v_G_4534_);
lean_dec(v___f_4530_);
lean_dec_ref(v_toMonadRef_4529_);
lean_dec_ref(v___x_4528_);
lean_dec_ref(v___x_4527_);
lean_dec(v___x_4526_);
lean_dec_ref(v_config_4525_);
lean_dec_ref(v_methods_4524_);
v___x_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4571_, 0, v_acc_4532_);
return v___x_4571_;
}
else
{
lean_object* v_snd_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4646_; 
v_snd_4572_ = lean_ctor_get(v_acc_4532_, 1);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_acc_4532_);
if (v_isSharedCheck_4646_ == 0)
{
lean_object* v_unused_4647_; 
v_unused_4647_ = lean_ctor_get(v_acc_4532_, 0);
lean_dec(v_unused_4647_);
v___x_4574_ = v_acc_4532_;
v_isShared_4575_ = v_isSharedCheck_4646_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_snd_4572_);
lean_dec(v_acc_4532_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4646_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4576_ = lean_array_fget_borrowed(v_hypotheses_4522_, v_next_4531_);
lean_inc(v___x_4576_);
v___x_4577_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4523_, v_methods_4524_, v_config_4525_, v___x_4576_, v___y_4536_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v_a_4578_; lean_object* v_type_4579_; lean_object* v_value_4580_; uint8_t v___x_4581_; 
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
lean_inc(v_a_4578_);
lean_dec_ref_known(v___x_4577_, 1);
v_type_4579_ = lean_ctor_get(v_a_4578_, 1);
v_value_4580_ = lean_ctor_get(v_a_4578_, 2);
lean_inc_ref(v_type_4579_);
v___x_4581_ = l_Lean_Expr_isFalse(v_type_4579_);
if (v___x_4581_ == 0)
{
lean_object* v_type_4582_; lean_object* v___f_4583_; uint8_t v___x_4613_; 
lean_del_object(v___x_4574_);
v_type_4582_ = lean_ctor_get(v___x_4576_, 1);
lean_inc(v___x_4526_);
lean_inc(v_a_4578_);
lean_inc(v_snd_4572_);
v___f_4583_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4583_, 0, v_snd_4572_);
lean_closure_set(v___f_4583_, 1, v_a_4578_);
lean_closure_set(v___f_4583_, 2, v___x_4526_);
v___x_4613_ = lean_expr_eqv(v_type_4582_, v_type_4579_);
if (v___x_4613_ == 0)
{
lean_inc_ref(v_type_4579_);
lean_dec(v_a_4578_);
lean_dec(v_snd_4572_);
lean_dec(v___x_4526_);
goto v___jp_4587_;
}
else
{
if (v___x_4581_ == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
lean_dec_ref(v___f_4583_);
lean_dec(v___f_4530_);
lean_dec_ref(v_toMonadRef_4529_);
lean_dec_ref(v___x_4528_);
lean_dec_ref(v___x_4527_);
v___x_4614_ = lean_box(0);
v___x_4615_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4572_, v_a_4578_, v___x_4526_, v___x_4614_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
v___y_4548_ = v___x_4615_;
goto v___jp_4547_;
}
else
{
lean_inc_ref(v_type_4579_);
lean_dec(v_a_4578_);
lean_dec(v_snd_4572_);
lean_dec(v___x_4526_);
goto v___jp_4587_;
}
}
v___jp_4584_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = lean_box(0);
v___x_4586_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4570_, v___f_4583_, v___x_4585_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
v___y_4548_ = v___x_4586_;
goto v___jp_4547_;
}
v___jp_4587_:
{
lean_object* v_toCold_4588_; lean_object* v_options_4589_; uint8_t v_hasTrace_4590_; 
v_toCold_4588_ = lean_ctor_get(v___y_4544_, 0);
v_options_4589_ = lean_ctor_get(v_toCold_4588_, 2);
v_hasTrace_4590_ = lean_ctor_get_uint8(v_options_4589_, sizeof(void*)*1);
if (v_hasTrace_4590_ == 0)
{
lean_dec_ref(v_type_4579_);
lean_dec(v___f_4530_);
lean_dec_ref(v_toMonadRef_4529_);
lean_dec_ref(v___x_4528_);
lean_dec_ref(v___x_4527_);
goto v___jp_4584_;
}
else
{
lean_object* v_inheritedTraceOptions_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v_inheritedTraceOptions_4591_ = lean_ctor_get(v_toCold_4588_, 11);
v___x_4592_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4593_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4591_, v_options_4589_, v___x_4593_);
if (v___x_4594_ == 0)
{
lean_dec_ref(v_type_4579_);
lean_dec(v___f_4530_);
lean_dec_ref(v_toMonadRef_4529_);
lean_dec_ref(v___x_4528_);
lean_dec_ref(v___x_4527_);
goto v___jp_4584_;
}
else
{
lean_object* v_type_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_22210__overap_4601_; lean_object* v___x_4602_; 
v_type_4595_ = lean_ctor_get(v___x_4576_, 1);
lean_inc_ref(v_type_4595_);
v___x_4596_ = l_Lean_MessageData_ofExpr(v_type_4595_);
v___x_4597_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4596_);
lean_ctor_set(v___x_4598_, 1, v___x_4597_);
v___x_4599_ = l_Lean_MessageData_ofExpr(v_type_4579_);
v___x_4600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4598_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
v___x_22210__overap_4601_ = l_Lean_addTrace___redArg(v___x_4527_, v___x_4528_, v_toMonadRef_4529_, v___f_4530_, v___x_4592_, v___x_4600_);
lean_inc(v___y_4545_);
lean_inc_ref(v___y_4544_);
lean_inc(v___y_4543_);
lean_inc_ref(v___y_4542_);
lean_inc(v___y_4541_);
lean_inc_ref(v___y_4540_);
lean_inc(v___y_4539_);
lean_inc_ref(v___y_4538_);
lean_inc(v___y_4537_);
lean_inc(v___y_4536_);
lean_inc_ref(v___y_4535_);
v___x_4602_ = lean_apply_12(v___x_22210__overap_4601_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, lean_box(0));
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4604_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4603_);
lean_dec_ref_known(v___x_4602_, 1);
v___x_4604_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4570_, v___f_4583_, v_a_4603_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
v___y_4548_ = v___x_4604_;
goto v___jp_4547_;
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec_ref(v___f_4583_);
lean_dec_ref(v_G_4534_);
v_a_4605_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4602_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4602_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4616_; 
lean_inc_ref(v_value_4580_);
lean_dec(v_a_4578_);
lean_dec_ref(v_G_4534_);
lean_dec(v___f_4530_);
lean_dec_ref(v_toMonadRef_4529_);
lean_dec_ref(v___x_4528_);
lean_dec_ref(v___x_4527_);
lean_dec(v___x_4526_);
v___x_4616_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4580_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4628_; 
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4628_ == 0)
{
lean_object* v_unused_4629_; 
v_unused_4629_ = lean_ctor_get(v___x_4616_, 0);
lean_dec(v_unused_4629_);
v___x_4618_ = v___x_4616_;
v_isShared_4619_ = v_isSharedCheck_4628_;
goto v_resetjp_4617_;
}
else
{
lean_dec(v___x_4616_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4628_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4620_ = lean_box(v___x_4570_);
v___x_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v___x_4621_);
v___x_4623_ = v___x_4574_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4627_, 1, v_snd_4572_);
v___x_4623_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4625_; 
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4623_);
v___x_4625_ = v___x_4618_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
lean_del_object(v___x_4574_);
lean_dec(v_snd_4572_);
v_a_4630_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4616_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4616_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
}
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
lean_del_object(v___x_4574_);
lean_dec(v_snd_4572_);
lean_dec_ref(v_G_4534_);
lean_dec(v___f_4530_);
lean_dec_ref(v_toMonadRef_4529_);
lean_dec_ref(v___x_4528_);
lean_dec_ref(v___x_4527_);
lean_dec(v___x_4526_);
v_a_4638_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4577_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4577_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
}
v___jp_4547_:
{
if (lean_obj_tag(v___y_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4561_; 
v_a_4549_ = lean_ctor_get(v___y_4548_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___y_4548_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4551_ = v___y_4548_;
v_isShared_4552_ = v_isSharedCheck_4561_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___y_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4561_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
if (lean_obj_tag(v_a_4549_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4555_; 
lean_dec_ref(v_G_4534_);
v_a_4553_ = lean_ctor_get(v_a_4549_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v_a_4549_, 1);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v_a_4553_);
v___x_4555_ = v___x_4551_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_a_4553_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_del_object(v___x_4551_);
v_a_4557_ = lean_ctor_get(v_a_4549_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v_a_4549_, 1);
v___x_4558_ = lean_unsigned_to_nat(1u);
v___x_4559_ = lean_nat_add(v_next_4531_, v___x_4558_);
lean_inc(v___y_4545_);
lean_inc_ref(v___y_4544_);
lean_inc(v___y_4543_);
lean_inc_ref(v___y_4542_);
lean_inc(v___y_4541_);
lean_inc_ref(v___y_4540_);
lean_inc(v___y_4539_);
lean_inc_ref(v___y_4538_);
lean_inc(v___y_4537_);
lean_inc(v___y_4536_);
lean_inc_ref(v___y_4535_);
v___x_4560_ = lean_apply_16(v_G_4534_, v___x_4559_, v_a_4557_, lean_box(0), lean_box(0), v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, lean_box(0));
return v___x_4560_;
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v_G_4534_);
v_a_4562_ = lean_ctor_get(v___y_4548_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___y_4548_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___y_4548_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___y_4548_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4648_ = _args[0];
lean_object* v_hypotheses_4649_ = _args[1];
lean_object* v_cacheId_4650_ = _args[2];
lean_object* v_methods_4651_ = _args[3];
lean_object* v_config_4652_ = _args[4];
lean_object* v___x_4653_ = _args[5];
lean_object* v___x_4654_ = _args[6];
lean_object* v___x_4655_ = _args[7];
lean_object* v_toMonadRef_4656_ = _args[8];
lean_object* v___f_4657_ = _args[9];
lean_object* v_next_4658_ = _args[10];
lean_object* v_acc_4659_ = _args[11];
lean_object* v_h_4660_ = _args[12];
lean_object* v_G_4661_ = _args[13];
lean_object* v___y_4662_ = _args[14];
lean_object* v___y_4663_ = _args[15];
lean_object* v___y_4664_ = _args[16];
lean_object* v___y_4665_ = _args[17];
lean_object* v___y_4666_ = _args[18];
lean_object* v___y_4667_ = _args[19];
lean_object* v___y_4668_ = _args[20];
lean_object* v___y_4669_ = _args[21];
lean_object* v___y_4670_ = _args[22];
lean_object* v___y_4671_ = _args[23];
lean_object* v___y_4672_ = _args[24];
lean_object* v___y_4673_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4674_; lean_object* v_res_4675_; 
v_cacheId_boxed_4674_ = lean_unbox(v_cacheId_4650_);
v_res_4675_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4648_, v_hypotheses_4649_, v_cacheId_boxed_4674_, v_methods_4651_, v_config_4652_, v___x_4653_, v___x_4654_, v___x_4655_, v_toMonadRef_4656_, v___f_4657_, v_next_4658_, v_acc_4659_, v_h_4660_, v_G_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v_next_4658_);
lean_dec_ref(v_hypotheses_4649_);
lean_dec(v___x_4648_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4676_, lean_object* v_methods_4677_, lean_object* v_config_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v___x_4691_; lean_object* v_toApplicative_4692_; lean_object* v_toFunctor_4693_; lean_object* v_toSeq_4694_; lean_object* v_toSeqLeft_4695_; lean_object* v_toSeqRight_4696_; lean_object* v___f_4697_; lean_object* v___f_4698_; lean_object* v___f_4699_; lean_object* v___f_4700_; lean_object* v___x_4701_; lean_object* v___f_4702_; lean_object* v___f_4703_; lean_object* v___f_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v_toApplicative_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4795_; 
v___x_4691_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4692_ = lean_ctor_get(v___x_4691_, 0);
v_toFunctor_4693_ = lean_ctor_get(v_toApplicative_4692_, 0);
v_toSeq_4694_ = lean_ctor_get(v_toApplicative_4692_, 2);
v_toSeqLeft_4695_ = lean_ctor_get(v_toApplicative_4692_, 3);
v_toSeqRight_4696_ = lean_ctor_get(v_toApplicative_4692_, 4);
v___f_4697_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4698_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4693_, 2);
v___f_4699_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4699_, 0, v_toFunctor_4693_);
v___f_4700_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4700_, 0, v_toFunctor_4693_);
v___x_4701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4701_, 0, v___f_4699_);
lean_ctor_set(v___x_4701_, 1, v___f_4700_);
lean_inc(v_toSeqRight_4696_);
v___f_4702_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4702_, 0, v_toSeqRight_4696_);
lean_inc(v_toSeqLeft_4695_);
v___f_4703_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4703_, 0, v_toSeqLeft_4695_);
lean_inc(v_toSeq_4694_);
v___f_4704_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4704_, 0, v_toSeq_4694_);
v___x_4705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4701_);
lean_ctor_set(v___x_4705_, 1, v___f_4697_);
lean_ctor_set(v___x_4705_, 2, v___f_4704_);
lean_ctor_set(v___x_4705_, 3, v___f_4703_);
lean_ctor_set(v___x_4705_, 4, v___f_4702_);
v___x_4706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
lean_ctor_set(v___x_4706_, 1, v___f_4698_);
v___x_4707_ = l_StateRefT_x27_instMonad___redArg(v___x_4706_);
v_toApplicative_4708_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4795_ == 0)
{
lean_object* v_unused_4796_; 
v_unused_4796_ = lean_ctor_get(v___x_4707_, 1);
lean_dec(v_unused_4796_);
v___x_4710_ = v___x_4707_;
v_isShared_4711_ = v_isSharedCheck_4795_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_toApplicative_4708_);
lean_dec(v___x_4707_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4795_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v_toFunctor_4712_; lean_object* v_toSeq_4713_; lean_object* v_toSeqLeft_4714_; lean_object* v_toSeqRight_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4793_; 
v_toFunctor_4712_ = lean_ctor_get(v_toApplicative_4708_, 0);
v_toSeq_4713_ = lean_ctor_get(v_toApplicative_4708_, 2);
v_toSeqLeft_4714_ = lean_ctor_get(v_toApplicative_4708_, 3);
v_toSeqRight_4715_ = lean_ctor_get(v_toApplicative_4708_, 4);
v_isSharedCheck_4793_ = !lean_is_exclusive(v_toApplicative_4708_);
if (v_isSharedCheck_4793_ == 0)
{
lean_object* v_unused_4794_; 
v_unused_4794_ = lean_ctor_get(v_toApplicative_4708_, 1);
lean_dec(v_unused_4794_);
v___x_4717_ = v_toApplicative_4708_;
v_isShared_4718_ = v_isSharedCheck_4793_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_toSeqRight_4715_);
lean_inc(v_toSeqLeft_4714_);
lean_inc(v_toSeq_4713_);
lean_inc(v_toFunctor_4712_);
lean_dec(v_toApplicative_4708_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4793_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___f_4719_; lean_object* v___f_4720_; lean_object* v___f_4721_; lean_object* v___f_4722_; lean_object* v___x_4723_; lean_object* v___f_4724_; lean_object* v___f_4725_; lean_object* v___f_4726_; lean_object* v___x_4728_; 
v___f_4719_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4720_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4712_);
v___f_4721_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4721_, 0, v_toFunctor_4712_);
v___f_4722_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4722_, 0, v_toFunctor_4712_);
v___x_4723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4723_, 0, v___f_4721_);
lean_ctor_set(v___x_4723_, 1, v___f_4722_);
v___f_4724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4724_, 0, v_toSeqRight_4715_);
v___f_4725_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4725_, 0, v_toSeqLeft_4714_);
v___f_4726_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4726_, 0, v_toSeq_4713_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 4, v___f_4724_);
lean_ctor_set(v___x_4717_, 3, v___f_4725_);
lean_ctor_set(v___x_4717_, 2, v___f_4726_);
lean_ctor_set(v___x_4717_, 1, v___f_4719_);
lean_ctor_set(v___x_4717_, 0, v___x_4723_);
v___x_4728_ = v___x_4717_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4792_, 1, v___f_4719_);
lean_ctor_set(v_reuseFailAlloc_4792_, 2, v___f_4726_);
lean_ctor_set(v_reuseFailAlloc_4792_, 3, v___f_4725_);
lean_ctor_set(v_reuseFailAlloc_4792_, 4, v___f_4724_);
v___x_4728_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
lean_object* v___x_4730_; 
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 1, v___f_4720_);
lean_ctor_set(v___x_4710_, 0, v___x_4728_);
v___x_4730_ = v___x_4710_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4728_);
lean_ctor_set(v_reuseFailAlloc_4791_, 1, v___f_4720_);
v___x_4730_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v_toMonadRef_4739_; lean_object* v___f_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v_hypotheses_4743_; lean_object* v___x_4744_; lean_object* v_newHyps_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___f_4749_; lean_object* v___x_4750_; lean_object* v___x_22108__overap_4751_; lean_object* v___x_4752_; 
v___x_4731_ = l_StateRefT_x27_instMonad___redArg(v___x_4730_);
v___x_4732_ = l_ReaderT_instMonad___redArg(v___x_4731_);
v___x_4733_ = l_StateRefT_x27_instMonad___redArg(v___x_4732_);
v___x_4734_ = l_ReaderT_instMonad___redArg(v___x_4733_);
v___x_4735_ = l_ReaderT_instMonad___redArg(v___x_4734_);
v___x_4736_ = l_StateRefT_x27_instMonad___redArg(v___x_4735_);
v___x_4737_ = l_ReaderT_instMonad___redArg(v___x_4736_);
v___x_4738_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4739_ = lean_ctor_get(v___x_4738_, 0);
v___f_4740_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4741_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4742_ = lean_st_ref_get(v_a_4680_);
v_hypotheses_4743_ = lean_ctor_get(v___x_4742_, 3);
lean_inc_ref(v_hypotheses_4743_);
lean_dec(v___x_4742_);
v___x_4744_ = lean_array_get_size(v_hypotheses_4743_);
v_newHyps_4745_ = lean_mk_empty_array_with_capacity(v___x_4744_);
v___x_4746_ = lean_unsigned_to_nat(0u);
v___x_4747_ = lean_box(0);
v___x_4748_ = lean_box(v_cacheId_4676_);
lean_inc_ref(v_toMonadRef_4739_);
v___f_4749_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4749_, 0, v___x_4744_);
lean_closure_set(v___f_4749_, 1, v_hypotheses_4743_);
lean_closure_set(v___f_4749_, 2, v___x_4748_);
lean_closure_set(v___f_4749_, 3, v_methods_4677_);
lean_closure_set(v___f_4749_, 4, v_config_4678_);
lean_closure_set(v___f_4749_, 5, v___x_4747_);
lean_closure_set(v___f_4749_, 6, v___x_4737_);
lean_closure_set(v___f_4749_, 7, v___x_4741_);
lean_closure_set(v___f_4749_, 8, v_toMonadRef_4739_);
lean_closure_set(v___f_4749_, 9, v___f_4740_);
v___x_4750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4747_);
lean_ctor_set(v___x_4750_, 1, v_newHyps_4745_);
v___x_22108__overap_4751_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4749_, v___x_4746_, v___x_4750_, lean_box(0));
lean_inc(v_a_4689_);
lean_inc_ref(v_a_4688_);
lean_inc(v_a_4687_);
lean_inc_ref(v_a_4686_);
lean_inc(v_a_4685_);
lean_inc_ref(v_a_4684_);
lean_inc(v_a_4683_);
lean_inc_ref(v_a_4682_);
lean_inc(v_a_4681_);
lean_inc(v_a_4680_);
lean_inc_ref(v_a_4679_);
v___x_4752_ = lean_apply_12(v___x_22108__overap_4751_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, lean_box(0));
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4782_; 
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4755_ = v___x_4752_;
v_isShared_4756_ = v_isSharedCheck_4782_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4752_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4782_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v_fst_4757_; 
v_fst_4757_ = lean_ctor_get(v_a_4753_, 0);
if (lean_obj_tag(v_fst_4757_) == 0)
{
lean_object* v_snd_4758_; lean_object* v___x_4759_; lean_object* v_caches_4760_; lean_object* v_typeAnalysis_4761_; lean_object* v_target_4762_; uint8_t v_didChange_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4776_; 
v_snd_4758_ = lean_ctor_get(v_a_4753_, 1);
lean_inc(v_snd_4758_);
lean_dec(v_a_4753_);
v___x_4759_ = lean_st_ref_take(v_a_4680_);
v_caches_4760_ = lean_ctor_get(v___x_4759_, 0);
v_typeAnalysis_4761_ = lean_ctor_get(v___x_4759_, 1);
v_target_4762_ = lean_ctor_get(v___x_4759_, 2);
v_didChange_4763_ = lean_ctor_get_uint8(v___x_4759_, sizeof(void*)*4);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4776_ == 0)
{
lean_object* v_unused_4777_; 
v_unused_4777_ = lean_ctor_get(v___x_4759_, 3);
lean_dec(v_unused_4777_);
v___x_4765_ = v___x_4759_;
v_isShared_4766_ = v_isSharedCheck_4776_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_target_4762_);
lean_inc(v_typeAnalysis_4761_);
lean_inc(v_caches_4760_);
lean_dec(v___x_4759_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4776_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
lean_ctor_set(v___x_4765_, 3, v_snd_4758_);
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_caches_4760_);
lean_ctor_set(v_reuseFailAlloc_4775_, 1, v_typeAnalysis_4761_);
lean_ctor_set(v_reuseFailAlloc_4775_, 2, v_target_4762_);
lean_ctor_set(v_reuseFailAlloc_4775_, 3, v_snd_4758_);
lean_ctor_set_uint8(v_reuseFailAlloc_4775_, sizeof(void*)*4, v_didChange_4763_);
v___x_4768_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4769_; uint8_t v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4773_; 
v___x_4769_ = lean_st_ref_put(v_a_4680_, v___x_4768_);
v___x_4770_ = 0;
v___x_4771_ = lean_box(v___x_4770_);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 0, v___x_4771_);
v___x_4773_ = v___x_4755_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4771_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
else
{
lean_object* v_val_4778_; lean_object* v___x_4780_; 
lean_inc_ref(v_fst_4757_);
lean_dec(v_a_4753_);
v_val_4778_ = lean_ctor_get(v_fst_4757_, 0);
lean_inc(v_val_4778_);
lean_dec_ref_known(v_fst_4757_, 1);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 0, v_val_4778_);
v___x_4780_ = v___x_4755_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_val_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
v_a_4783_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4752_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4752_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4797_, lean_object* v_methods_4798_, lean_object* v_config_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
uint8_t v_cacheId_boxed_4812_; lean_object* v_res_4813_; 
v_cacheId_boxed_4812_ = lean_unbox(v_cacheId_4797_);
v_res_4813_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4812_, v_methods_4798_, v_config_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v___x_4820_; lean_object* v_env_4821_; lean_object* v___x_4822_; lean_object* v_toCold_4823_; lean_object* v_mctx_4824_; lean_object* v_lctx_4825_; lean_object* v_options_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4820_ = lean_st_ref_get(v___y_4818_);
v_env_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc_ref(v_env_4821_);
lean_dec(v___x_4820_);
v___x_4822_ = lean_st_ref_get(v___y_4816_);
v_toCold_4823_ = lean_ctor_get(v___y_4817_, 0);
v_mctx_4824_ = lean_ctor_get(v___x_4822_, 0);
lean_inc_ref(v_mctx_4824_);
lean_dec(v___x_4822_);
v_lctx_4825_ = lean_ctor_get(v___y_4815_, 2);
v_options_4826_ = lean_ctor_get(v_toCold_4823_, 2);
lean_inc_ref(v_options_4826_);
lean_inc_ref(v_lctx_4825_);
v___x_4827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4827_, 0, v_env_4821_);
lean_ctor_set(v___x_4827_, 1, v_mctx_4824_);
lean_ctor_set(v___x_4827_, 2, v_lctx_4825_);
lean_ctor_set(v___x_4827_, 3, v_options_4826_);
v___x_4828_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4827_);
lean_ctor_set(v___x_4828_, 1, v_msgData_4814_);
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
return v_res_4836_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4837_; double v___x_4838_; 
v___x_4837_ = lean_unsigned_to_nat(0u);
v___x_4838_ = lean_float_of_nat(v___x_4837_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4842_, lean_object* v_msg_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v_ref_4849_; lean_object* v___x_4850_; lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4896_; 
v_ref_4849_ = lean_ctor_get(v___y_4846_, 2);
v___x_4850_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4853_ = v___x_4850_;
v_isShared_4854_ = v_isSharedCheck_4896_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4850_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4896_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4855_; lean_object* v_traceState_4856_; lean_object* v_env_4857_; lean_object* v_nextMacroScope_4858_; lean_object* v_ngen_4859_; lean_object* v_auxDeclNGen_4860_; lean_object* v_cache_4861_; lean_object* v_recordedDeps_4862_; lean_object* v_messages_4863_; lean_object* v_infoState_4864_; lean_object* v_snapshotTasks_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4895_; 
v___x_4855_ = lean_st_ref_take(v___y_4847_);
v_traceState_4856_ = lean_ctor_get(v___x_4855_, 4);
v_env_4857_ = lean_ctor_get(v___x_4855_, 0);
v_nextMacroScope_4858_ = lean_ctor_get(v___x_4855_, 1);
v_ngen_4859_ = lean_ctor_get(v___x_4855_, 2);
v_auxDeclNGen_4860_ = lean_ctor_get(v___x_4855_, 3);
v_cache_4861_ = lean_ctor_get(v___x_4855_, 5);
v_recordedDeps_4862_ = lean_ctor_get(v___x_4855_, 6);
v_messages_4863_ = lean_ctor_get(v___x_4855_, 7);
v_infoState_4864_ = lean_ctor_get(v___x_4855_, 8);
v_snapshotTasks_4865_ = lean_ctor_get(v___x_4855_, 9);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4867_ = v___x_4855_;
v_isShared_4868_ = v_isSharedCheck_4895_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_snapshotTasks_4865_);
lean_inc(v_infoState_4864_);
lean_inc(v_messages_4863_);
lean_inc(v_recordedDeps_4862_);
lean_inc(v_cache_4861_);
lean_inc(v_traceState_4856_);
lean_inc(v_auxDeclNGen_4860_);
lean_inc(v_ngen_4859_);
lean_inc(v_nextMacroScope_4858_);
lean_inc(v_env_4857_);
lean_dec(v___x_4855_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4895_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
uint64_t v_tid_4869_; lean_object* v_traces_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4894_; 
v_tid_4869_ = lean_ctor_get_uint64(v_traceState_4856_, sizeof(void*)*1);
v_traces_4870_ = lean_ctor_get(v_traceState_4856_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v_traceState_4856_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4872_ = v_traceState_4856_;
v_isShared_4873_ = v_isSharedCheck_4894_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_traces_4870_);
lean_dec(v_traceState_4856_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4894_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; double v___x_4876_; uint8_t v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4885_; 
v___x_4874_ = lean_box(0);
v___x_4875_ = lean_box(0);
v___x_4876_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4877_ = 0;
v___x_4878_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4879_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4879_, 0, v_cls_4842_);
lean_ctor_set(v___x_4879_, 1, v___x_4875_);
lean_ctor_set(v___x_4879_, 2, v___x_4878_);
lean_ctor_set_float(v___x_4879_, sizeof(void*)*3, v___x_4876_);
lean_ctor_set_float(v___x_4879_, sizeof(void*)*3 + 8, v___x_4876_);
lean_ctor_set_uint8(v___x_4879_, sizeof(void*)*3 + 16, v___x_4877_);
v___x_4880_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4881_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4879_);
lean_ctor_set(v___x_4881_, 1, v_a_4851_);
lean_ctor_set(v___x_4881_, 2, v___x_4880_);
lean_inc(v_ref_4849_);
v___x_4882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4882_, 0, v_ref_4849_);
lean_ctor_set(v___x_4882_, 1, v___x_4881_);
v___x_4883_ = l_Lean_PersistentArray_push___redArg(v_traces_4870_, v___x_4882_);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 0, v___x_4883_);
v___x_4885_ = v___x_4872_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4883_);
lean_ctor_set_uint64(v_reuseFailAlloc_4893_, sizeof(void*)*1, v_tid_4869_);
v___x_4885_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
lean_object* v___x_4887_; 
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 4, v___x_4885_);
v___x_4887_ = v___x_4867_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_env_4857_);
lean_ctor_set(v_reuseFailAlloc_4892_, 1, v_nextMacroScope_4858_);
lean_ctor_set(v_reuseFailAlloc_4892_, 2, v_ngen_4859_);
lean_ctor_set(v_reuseFailAlloc_4892_, 3, v_auxDeclNGen_4860_);
lean_ctor_set(v_reuseFailAlloc_4892_, 4, v___x_4885_);
lean_ctor_set(v_reuseFailAlloc_4892_, 5, v_cache_4861_);
lean_ctor_set(v_reuseFailAlloc_4892_, 6, v_recordedDeps_4862_);
lean_ctor_set(v_reuseFailAlloc_4892_, 7, v_messages_4863_);
lean_ctor_set(v_reuseFailAlloc_4892_, 8, v_infoState_4864_);
lean_ctor_set(v_reuseFailAlloc_4892_, 9, v_snapshotTasks_4865_);
v___x_4887_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4888_; lean_object* v___x_4890_; 
v___x_4888_ = lean_st_ref_put(v___y_4847_, v___x_4887_);
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 0, v___x_4874_);
v___x_4890_ = v___x_4853_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4874_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4897_, lean_object* v_msg_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4897_, v_msg_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_);
lean_dec(v___y_4902_);
lean_dec_ref(v___y_4901_);
lean_dec(v___y_4900_);
lean_dec_ref(v___y_4899_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_4905_, lean_object* v___f_4906_, lean_object* v_____r_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_){
_start:
{
lean_object* v___x_4921_; lean_object* v_caches_4922_; lean_object* v_typeAnalysis_4923_; lean_object* v_target_4924_; lean_object* v_hypotheses_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4935_; 
v___x_4921_ = lean_st_ref_take(v___y_4910_);
v_caches_4922_ = lean_ctor_get(v___x_4921_, 0);
v_typeAnalysis_4923_ = lean_ctor_get(v___x_4921_, 1);
v_target_4924_ = lean_ctor_get(v___x_4921_, 2);
v_hypotheses_4925_ = lean_ctor_get(v___x_4921_, 3);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4927_ = v___x_4921_;
v_isShared_4928_ = v_isSharedCheck_4935_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_hypotheses_4925_);
lean_inc(v_target_4924_);
lean_inc(v_typeAnalysis_4923_);
lean_inc(v_caches_4922_);
lean_dec(v___x_4921_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4935_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4929_; lean_object* v___x_4931_; 
v___x_4929_ = lean_box(0);
if (v_isShared_4928_ == 0)
{
v___x_4931_ = v___x_4927_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_caches_4922_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v_typeAnalysis_4923_);
lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_target_4924_);
lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_hypotheses_4925_);
v___x_4931_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_ctor_set_uint8(v___x_4931_, sizeof(void*)*4, v___x_4905_);
v___x_4932_ = lean_st_ref_put(v___y_4910_, v___x_4931_);
lean_inc(v___y_4919_);
lean_inc_ref(v___y_4918_);
lean_inc(v___y_4917_);
lean_inc_ref(v___y_4916_);
lean_inc(v___y_4915_);
lean_inc_ref(v___y_4914_);
lean_inc(v___y_4913_);
lean_inc_ref(v___y_4912_);
lean_inc(v___y_4911_);
lean_inc(v___y_4910_);
lean_inc_ref(v___y_4909_);
lean_inc(v___y_4908_);
v___x_4933_ = lean_apply_14(v___f_4906_, v___x_4929_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, lean_box(0));
return v___x_4933_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_4936_, lean_object* v___f_4937_, lean_object* v_____r_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
uint8_t v___x_35925__boxed_4952_; lean_object* v_res_4953_; 
v___x_35925__boxed_4952_ = lean_unbox(v___x_4936_);
v_res_4953_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35925__boxed_4952_, v___f_4937_, v_____r_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v___y_4939_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_4954_, lean_object* v_a_4955_, lean_object* v___x_4956_, lean_object* v_____r_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4971_ = lean_array_push(v_snd_4954_, v_a_4955_);
v___x_4972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4956_);
lean_ctor_set(v___x_4972_, 1, v___x_4971_);
v___x_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4972_);
v___x_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4973_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_4975_ = _args[0];
lean_object* v_a_4976_ = _args[1];
lean_object* v___x_4977_ = _args[2];
lean_object* v_____r_4978_ = _args[3];
lean_object* v___y_4979_ = _args[4];
lean_object* v___y_4980_ = _args[5];
lean_object* v___y_4981_ = _args[6];
lean_object* v___y_4982_ = _args[7];
lean_object* v___y_4983_ = _args[8];
lean_object* v___y_4984_ = _args[9];
lean_object* v___y_4985_ = _args[10];
lean_object* v___y_4986_ = _args[11];
lean_object* v___y_4987_ = _args[12];
lean_object* v___y_4988_ = _args[13];
lean_object* v___y_4989_ = _args[14];
lean_object* v___y_4990_ = _args[15];
lean_object* v___y_4991_ = _args[16];
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_4975_, v_a_4976_, v___x_4977_, v_____r_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
lean_dec(v___y_4986_);
lean_dec_ref(v___y_4985_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
lean_dec(v___y_4982_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_4993_, lean_object* v___x_4994_, lean_object* v_methods_4995_, lean_object* v_config_4996_, lean_object* v_a_4997_, lean_object* v_b_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_){
_start:
{
lean_object* v___y_5013_; uint8_t v___x_5035_; 
v___x_5035_ = lean_nat_dec_lt(v_a_4997_, v_upperBound_4993_);
if (v___x_5035_ == 0)
{
lean_object* v___x_5036_; 
lean_dec(v_a_4997_);
lean_dec_ref(v_config_4996_);
lean_dec_ref(v_methods_4995_);
v___x_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5036_, 0, v_b_4998_);
return v___x_5036_;
}
else
{
lean_object* v_snd_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5136_; 
v_snd_5037_ = lean_ctor_get(v_b_4998_, 1);
v_isSharedCheck_5136_ = !lean_is_exclusive(v_b_4998_);
if (v_isSharedCheck_5136_ == 0)
{
lean_object* v_unused_5137_; 
v_unused_5137_ = lean_ctor_get(v_b_4998_, 0);
lean_dec(v_unused_5137_);
v___x_5039_ = v_b_4998_;
v_isShared_5040_ = v_isSharedCheck_5136_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_snd_5037_);
lean_dec(v_b_4998_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5136_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v_type_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
v___x_5041_ = lean_box(0);
v___x_5042_ = lean_array_fget_borrowed(v___x_4994_, v_a_4997_);
v___x_5043_ = lean_st_ref_take(v___y_4999_);
v___x_5044_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5045_ = lean_st_ref_put(v___y_4999_, v___x_5044_);
v_type_5046_ = lean_ctor_get(v___x_5042_, 1);
v___x_5047_ = lean_unsigned_to_nat(0u);
v___x_5048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5048_, 0, v___x_5047_);
lean_ctor_set(v___x_5048_, 1, v___x_5043_);
lean_ctor_set(v___x_5048_, 2, v___x_5044_);
lean_ctor_set(v___x_5048_, 3, v___x_5044_);
lean_inc_ref(v_type_5046_);
v___x_5049_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5049_, 0, v_type_5046_);
lean_inc_ref(v_config_4996_);
lean_inc_ref(v_methods_4995_);
v___x_5050_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5049_, v_methods_4995_, v_config_4996_, v___x_5048_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v_a_5051_; lean_object* v_snd_5052_; lean_object* v_fst_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5127_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5051_);
lean_dec_ref_known(v___x_5050_, 1);
v_snd_5052_ = lean_ctor_get(v_a_5051_, 1);
v_fst_5053_ = lean_ctor_get(v_a_5051_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v_a_5051_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5055_ = v_a_5051_;
v_isShared_5056_ = v_isSharedCheck_5127_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_snd_5052_);
lean_inc(v_fst_5053_);
lean_dec(v_a_5051_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5127_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v_persistentCache_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v_persistentCache_5057_ = lean_ctor_get(v_snd_5052_, 1);
lean_inc_ref(v_persistentCache_5057_);
lean_dec(v_snd_5052_);
v___x_5058_ = lean_st_ref_swap(v___y_4999_, v_persistentCache_5057_);
lean_dec(v___x_5058_);
lean_inc(v___x_5042_);
v___x_5059_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5042_, v_fst_5053_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5060_; lean_object* v_type_5061_; lean_object* v_value_5062_; uint8_t v___x_5063_; 
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
lean_inc(v_a_5060_);
lean_dec_ref_known(v___x_5059_, 1);
v_type_5061_ = lean_ctor_get(v_a_5060_, 1);
v_value_5062_ = lean_ctor_get(v_a_5060_, 2);
lean_inc_ref(v_type_5061_);
v___x_5063_ = l_Lean_Expr_isFalse(v_type_5061_);
if (v___x_5063_ == 0)
{
lean_object* v___f_5064_; uint8_t v___x_5094_; 
lean_del_object(v___x_5055_);
lean_inc(v_a_5060_);
lean_inc(v_snd_5037_);
v___f_5064_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5064_, 0, v_snd_5037_);
lean_closure_set(v___f_5064_, 1, v_a_5060_);
lean_closure_set(v___f_5064_, 2, v___x_5041_);
v___x_5094_ = lean_expr_eqv(v_type_5046_, v_type_5061_);
if (v___x_5094_ == 0)
{
lean_inc_ref(v_type_5061_);
lean_dec(v_a_5060_);
lean_dec(v_snd_5037_);
goto v___jp_5068_;
}
else
{
if (v___x_5063_ == 0)
{
lean_object* v___x_5095_; lean_object* v___x_5096_; 
lean_dec_ref(v___f_5064_);
lean_del_object(v___x_5039_);
v___x_5095_ = lean_box(0);
v___x_5096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5037_, v_a_5060_, v___x_5041_, v___x_5095_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
v___y_5013_ = v___x_5096_;
goto v___jp_5012_;
}
else
{
lean_inc_ref(v_type_5061_);
lean_dec(v_a_5060_);
lean_dec(v_snd_5037_);
goto v___jp_5068_;
}
}
v___jp_5065_:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5066_ = lean_box(0);
v___x_5067_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5035_, v___f_5064_, v___x_5066_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
v___y_5013_ = v___x_5067_;
goto v___jp_5012_;
}
v___jp_5068_:
{
lean_object* v_toCold_5069_; lean_object* v_options_5070_; uint8_t v_hasTrace_5071_; 
v_toCold_5069_ = lean_ctor_get(v___y_5009_, 0);
v_options_5070_ = lean_ctor_get(v_toCold_5069_, 2);
v_hasTrace_5071_ = lean_ctor_get_uint8(v_options_5070_, sizeof(void*)*1);
if (v_hasTrace_5071_ == 0)
{
lean_dec_ref(v_type_5061_);
lean_del_object(v___x_5039_);
goto v___jp_5065_;
}
else
{
lean_object* v_inheritedTraceOptions_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; 
v_inheritedTraceOptions_5072_ = lean_ctor_get(v_toCold_5069_, 11);
v___x_5073_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5074_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5072_, v_options_5070_, v___x_5074_);
if (v___x_5075_ == 0)
{
lean_dec_ref(v_type_5061_);
lean_del_object(v___x_5039_);
goto v___jp_5065_;
}
else
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5079_; 
lean_inc_ref(v_type_5046_);
v___x_5076_ = l_Lean_MessageData_ofExpr(v_type_5046_);
v___x_5077_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5040_ == 0)
{
lean_ctor_set_tag(v___x_5039_, 7);
lean_ctor_set(v___x_5039_, 1, v___x_5077_);
lean_ctor_set(v___x_5039_, 0, v___x_5076_);
v___x_5079_ = v___x_5039_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v___x_5076_);
lean_ctor_set(v_reuseFailAlloc_5093_, 1, v___x_5077_);
v___x_5079_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5080_ = l_Lean_MessageData_ofExpr(v_type_5061_);
v___x_5081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5079_);
lean_ctor_set(v___x_5081_, 1, v___x_5080_);
v___x_5082_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5073_, v___x_5081_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___x_5084_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5083_);
lean_dec_ref_known(v___x_5082_, 1);
v___x_5084_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5035_, v___f_5064_, v_a_5083_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
v___y_5013_ = v___x_5084_;
goto v___jp_5012_;
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec_ref(v___f_5064_);
lean_dec(v_a_4997_);
lean_dec_ref(v_config_4996_);
lean_dec_ref(v_methods_4995_);
v_a_5085_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5082_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5082_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
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
lean_object* v___x_5097_; 
lean_inc_ref(v_value_5062_);
lean_dec(v_a_5060_);
lean_del_object(v___x_5039_);
lean_dec(v_a_4997_);
lean_dec_ref(v_config_4996_);
lean_dec_ref(v_methods_4995_);
v___x_5097_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5062_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5109_; 
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5109_ == 0)
{
lean_object* v_unused_5110_; 
v_unused_5110_ = lean_ctor_get(v___x_5097_, 0);
lean_dec(v_unused_5110_);
v___x_5099_ = v___x_5097_;
v_isShared_5100_ = v_isSharedCheck_5109_;
goto v_resetjp_5098_;
}
else
{
lean_dec(v___x_5097_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5109_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5104_; 
v___x_5101_ = lean_box(v___x_5035_);
v___x_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5101_);
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 1, v_snd_5037_);
lean_ctor_set(v___x_5055_, 0, v___x_5102_);
v___x_5104_ = v___x_5055_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5102_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v_snd_5037_);
v___x_5104_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
lean_object* v___x_5106_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v___x_5104_);
v___x_5106_ = v___x_5099_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5104_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_del_object(v___x_5055_);
lean_dec(v_snd_5037_);
v_a_5111_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_5097_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5097_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_del_object(v___x_5055_);
lean_del_object(v___x_5039_);
lean_dec(v_snd_5037_);
lean_dec(v_a_4997_);
lean_dec_ref(v_config_4996_);
lean_dec_ref(v_methods_4995_);
v_a_5119_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5059_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5059_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5135_; 
lean_del_object(v___x_5039_);
lean_dec(v_snd_5037_);
lean_dec(v_a_4997_);
lean_dec_ref(v_config_4996_);
lean_dec_ref(v_methods_4995_);
v_a_5128_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5135_ == 0)
{
v___x_5130_ = v___x_5050_;
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5050_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5133_; 
if (v_isShared_5131_ == 0)
{
v___x_5133_ = v___x_5130_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5128_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
}
}
}
v___jp_5012_:
{
if (lean_obj_tag(v___y_5013_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5026_; 
v_a_5014_ = lean_ctor_get(v___y_5013_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___y_5013_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5016_ = v___y_5013_;
v_isShared_5017_ = v_isSharedCheck_5026_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___y_5013_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5026_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
if (lean_obj_tag(v_a_5014_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5020_; 
lean_dec(v_a_4997_);
lean_dec_ref(v_config_4996_);
lean_dec_ref(v_methods_4995_);
v_a_5018_ = lean_ctor_get(v_a_5014_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v_a_5014_, 1);
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 0, v_a_5018_);
v___x_5020_ = v___x_5016_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5018_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
lean_del_object(v___x_5016_);
v_a_5022_ = lean_ctor_get(v_a_5014_, 0);
lean_inc(v_a_5022_);
lean_dec_ref_known(v_a_5014_, 1);
v___x_5023_ = lean_unsigned_to_nat(1u);
v___x_5024_ = lean_nat_add(v_a_4997_, v___x_5023_);
lean_dec(v_a_4997_);
v_a_4997_ = v___x_5024_;
v_b_4998_ = v_a_5022_;
goto _start;
}
}
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5034_; 
lean_dec(v_a_4997_);
lean_dec_ref(v_config_4996_);
lean_dec_ref(v_methods_4995_);
v_a_5027_ = lean_ctor_get(v___y_5013_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___y_5013_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5029_ = v___y_5013_;
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___y_5013_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5032_; 
if (v_isShared_5030_ == 0)
{
v___x_5032_ = v___x_5029_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_a_5027_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
return v___x_5032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5138_ = _args[0];
lean_object* v___x_5139_ = _args[1];
lean_object* v_methods_5140_ = _args[2];
lean_object* v_config_5141_ = _args[3];
lean_object* v_a_5142_ = _args[4];
lean_object* v_b_5143_ = _args[5];
lean_object* v___y_5144_ = _args[6];
lean_object* v___y_5145_ = _args[7];
lean_object* v___y_5146_ = _args[8];
lean_object* v___y_5147_ = _args[9];
lean_object* v___y_5148_ = _args[10];
lean_object* v___y_5149_ = _args[11];
lean_object* v___y_5150_ = _args[12];
lean_object* v___y_5151_ = _args[13];
lean_object* v___y_5152_ = _args[14];
lean_object* v___y_5153_ = _args[15];
lean_object* v___y_5154_ = _args[16];
lean_object* v___y_5155_ = _args[17];
lean_object* v___y_5156_ = _args[18];
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5138_, v___x_5139_, v_methods_5140_, v_config_5141_, v_a_5142_, v_b_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
lean_dec(v___y_5151_);
lean_dec_ref(v___y_5150_);
lean_dec(v___y_5149_);
lean_dec_ref(v___y_5148_);
lean_dec(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___x_5139_);
lean_dec(v_upperBound_5138_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_5158_, lean_object* v_config_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_){
_start:
{
lean_object* v___x_5173_; lean_object* v_hypotheses_5174_; lean_object* v___x_5175_; lean_object* v_newHyps_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5173_ = lean_st_ref_get(v_a_5162_);
v_hypotheses_5174_ = lean_ctor_get(v___x_5173_, 3);
lean_inc_ref(v_hypotheses_5174_);
lean_dec(v___x_5173_);
v___x_5175_ = lean_array_get_size(v_hypotheses_5174_);
v_newHyps_5176_ = lean_mk_empty_array_with_capacity(v___x_5175_);
v___x_5177_ = lean_unsigned_to_nat(0u);
v___x_5178_ = lean_box(0);
v___x_5179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5178_);
lean_ctor_set(v___x_5179_, 1, v_newHyps_5176_);
v___x_5180_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_5175_, v_hypotheses_5174_, v_methods_5158_, v_config_5159_, v___x_5177_, v___x_5179_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_);
lean_dec_ref(v_hypotheses_5174_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v_a_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5210_; 
v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5183_ = v___x_5180_;
v_isShared_5184_ = v_isSharedCheck_5210_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_a_5181_);
lean_dec(v___x_5180_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5210_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v_fst_5185_; 
v_fst_5185_ = lean_ctor_get(v_a_5181_, 0);
if (lean_obj_tag(v_fst_5185_) == 0)
{
lean_object* v_snd_5186_; lean_object* v___x_5187_; lean_object* v_caches_5188_; lean_object* v_typeAnalysis_5189_; lean_object* v_target_5190_; uint8_t v_didChange_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5204_; 
v_snd_5186_ = lean_ctor_get(v_a_5181_, 1);
lean_inc(v_snd_5186_);
lean_dec(v_a_5181_);
v___x_5187_ = lean_st_ref_take(v_a_5162_);
v_caches_5188_ = lean_ctor_get(v___x_5187_, 0);
v_typeAnalysis_5189_ = lean_ctor_get(v___x_5187_, 1);
v_target_5190_ = lean_ctor_get(v___x_5187_, 2);
v_didChange_5191_ = lean_ctor_get_uint8(v___x_5187_, sizeof(void*)*4);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5204_ == 0)
{
lean_object* v_unused_5205_; 
v_unused_5205_ = lean_ctor_get(v___x_5187_, 3);
lean_dec(v_unused_5205_);
v___x_5193_ = v___x_5187_;
v_isShared_5194_ = v_isSharedCheck_5204_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_target_5190_);
lean_inc(v_typeAnalysis_5189_);
lean_inc(v_caches_5188_);
lean_dec(v___x_5187_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5204_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 3, v_snd_5186_);
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_caches_5188_);
lean_ctor_set(v_reuseFailAlloc_5203_, 1, v_typeAnalysis_5189_);
lean_ctor_set(v_reuseFailAlloc_5203_, 2, v_target_5190_);
lean_ctor_set(v_reuseFailAlloc_5203_, 3, v_snd_5186_);
lean_ctor_set_uint8(v_reuseFailAlloc_5203_, sizeof(void*)*4, v_didChange_5191_);
v___x_5196_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
lean_object* v___x_5197_; uint8_t v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5201_; 
v___x_5197_ = lean_st_ref_put(v_a_5162_, v___x_5196_);
v___x_5198_ = 0;
v___x_5199_ = lean_box(v___x_5198_);
if (v_isShared_5184_ == 0)
{
lean_ctor_set(v___x_5183_, 0, v___x_5199_);
v___x_5201_ = v___x_5183_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5199_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
else
{
lean_object* v_val_5206_; lean_object* v___x_5208_; 
lean_inc_ref(v_fst_5185_);
lean_dec(v_a_5181_);
v_val_5206_ = lean_ctor_get(v_fst_5185_, 0);
lean_inc(v_val_5206_);
lean_dec_ref_known(v_fst_5185_, 1);
if (v_isShared_5184_ == 0)
{
lean_ctor_set(v___x_5183_, 0, v_val_5206_);
v___x_5208_ = v___x_5183_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_val_5206_);
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
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
v_a_5211_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5180_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5180_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_5219_, lean_object* v_config_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5219_, v_config_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
lean_dec(v_a_5232_);
lean_dec_ref(v_a_5231_);
lean_dec(v_a_5230_);
lean_dec_ref(v_a_5229_);
lean_dec(v_a_5228_);
lean_dec_ref(v_a_5227_);
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
lean_dec(v_a_5224_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
lean_dec(v_a_5221_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_5235_, lean_object* v_msg_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5235_, v_msg_5236_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_5251_, lean_object* v_msg_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5251_, v_msg_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_);
lean_dec(v___y_5264_);
lean_dec_ref(v___y_5263_);
lean_dec(v___y_5262_);
lean_dec_ref(v___y_5261_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_upperBound_5267_, lean_object* v___x_5268_, lean_object* v_methods_5269_, lean_object* v_config_5270_, lean_object* v_inst_5271_, lean_object* v_R_5272_, lean_object* v_a_5273_, lean_object* v_b_5274_, lean_object* v_c_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_){
_start:
{
lean_object* v___x_5289_; 
v___x_5289_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5267_, v___x_5268_, v_methods_5269_, v_config_5270_, v_a_5273_, v_b_5274_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_);
return v___x_5289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5290_ = _args[0];
lean_object* v___x_5291_ = _args[1];
lean_object* v_methods_5292_ = _args[2];
lean_object* v_config_5293_ = _args[3];
lean_object* v_inst_5294_ = _args[4];
lean_object* v_R_5295_ = _args[5];
lean_object* v_a_5296_ = _args[6];
lean_object* v_b_5297_ = _args[7];
lean_object* v_c_5298_ = _args[8];
lean_object* v___y_5299_ = _args[9];
lean_object* v___y_5300_ = _args[10];
lean_object* v___y_5301_ = _args[11];
lean_object* v___y_5302_ = _args[12];
lean_object* v___y_5303_ = _args[13];
lean_object* v___y_5304_ = _args[14];
lean_object* v___y_5305_ = _args[15];
lean_object* v___y_5306_ = _args[16];
lean_object* v___y_5307_ = _args[17];
lean_object* v___y_5308_ = _args[18];
lean_object* v___y_5309_ = _args[19];
lean_object* v___y_5310_ = _args[20];
lean_object* v___y_5311_ = _args[21];
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5290_, v___x_5291_, v_methods_5292_, v_config_5293_, v_inst_5294_, v_R_5295_, v_a_5296_, v_b_5297_, v_c_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___x_5291_);
lean_dec(v_upperBound_5290_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_5313_, lean_object* v_config_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_){
_start:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; 
v___x_5327_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5328_ = lean_st_mk_ref(v___x_5327_);
v___x_5329_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5313_, v_config_5314_, v___x_5328_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5338_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5332_ = v___x_5329_;
v_isShared_5333_ = v_isSharedCheck_5338_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5329_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5338_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5334_; lean_object* v___x_5336_; 
v___x_5334_ = lean_st_ref_get(v___x_5328_);
lean_dec(v___x_5328_);
lean_dec(v___x_5334_);
if (v_isShared_5333_ == 0)
{
v___x_5336_ = v___x_5332_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_a_5330_);
v___x_5336_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
return v___x_5336_;
}
}
}
else
{
lean_dec(v___x_5328_);
return v___x_5329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_5339_, lean_object* v_config_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_){
_start:
{
lean_object* v_res_5353_; 
v_res_5353_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5339_, v_config_5340_, v_a_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_);
lean_dec(v_a_5351_);
lean_dec_ref(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec_ref(v_a_5348_);
lean_dec(v_a_5347_);
lean_dec_ref(v_a_5346_);
lean_dec(v_a_5345_);
lean_dec_ref(v_a_5344_);
lean_dec(v_a_5343_);
lean_dec(v_a_5342_);
lean_dec_ref(v_a_5341_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_5354_, lean_object* v_msg_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v_ref_5361_; lean_object* v___x_5362_; lean_object* v_a_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5408_; 
v_ref_5361_ = lean_ctor_get(v___y_5358_, 2);
v___x_5362_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
v_a_5363_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5365_ = v___x_5362_;
v_isShared_5366_ = v_isSharedCheck_5408_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_a_5363_);
lean_dec(v___x_5362_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5408_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5367_; lean_object* v_traceState_5368_; lean_object* v_env_5369_; lean_object* v_nextMacroScope_5370_; lean_object* v_ngen_5371_; lean_object* v_auxDeclNGen_5372_; lean_object* v_cache_5373_; lean_object* v_recordedDeps_5374_; lean_object* v_messages_5375_; lean_object* v_infoState_5376_; lean_object* v_snapshotTasks_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5407_; 
v___x_5367_ = lean_st_ref_take(v___y_5359_);
v_traceState_5368_ = lean_ctor_get(v___x_5367_, 4);
v_env_5369_ = lean_ctor_get(v___x_5367_, 0);
v_nextMacroScope_5370_ = lean_ctor_get(v___x_5367_, 1);
v_ngen_5371_ = lean_ctor_get(v___x_5367_, 2);
v_auxDeclNGen_5372_ = lean_ctor_get(v___x_5367_, 3);
v_cache_5373_ = lean_ctor_get(v___x_5367_, 5);
v_recordedDeps_5374_ = lean_ctor_get(v___x_5367_, 6);
v_messages_5375_ = lean_ctor_get(v___x_5367_, 7);
v_infoState_5376_ = lean_ctor_get(v___x_5367_, 8);
v_snapshotTasks_5377_ = lean_ctor_get(v___x_5367_, 9);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5367_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5379_ = v___x_5367_;
v_isShared_5380_ = v_isSharedCheck_5407_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_snapshotTasks_5377_);
lean_inc(v_infoState_5376_);
lean_inc(v_messages_5375_);
lean_inc(v_recordedDeps_5374_);
lean_inc(v_cache_5373_);
lean_inc(v_traceState_5368_);
lean_inc(v_auxDeclNGen_5372_);
lean_inc(v_ngen_5371_);
lean_inc(v_nextMacroScope_5370_);
lean_inc(v_env_5369_);
lean_dec(v___x_5367_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5407_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
uint64_t v_tid_5381_; lean_object* v_traces_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5406_; 
v_tid_5381_ = lean_ctor_get_uint64(v_traceState_5368_, sizeof(void*)*1);
v_traces_5382_ = lean_ctor_get(v_traceState_5368_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v_traceState_5368_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5384_ = v_traceState_5368_;
v_isShared_5385_ = v_isSharedCheck_5406_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_traces_5382_);
lean_dec(v_traceState_5368_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5406_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; double v___x_5388_; uint8_t v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5397_; 
v___x_5386_ = lean_box(0);
v___x_5387_ = lean_box(0);
v___x_5388_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5389_ = 0;
v___x_5390_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5391_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5391_, 0, v_cls_5354_);
lean_ctor_set(v___x_5391_, 1, v___x_5387_);
lean_ctor_set(v___x_5391_, 2, v___x_5390_);
lean_ctor_set_float(v___x_5391_, sizeof(void*)*3, v___x_5388_);
lean_ctor_set_float(v___x_5391_, sizeof(void*)*3 + 8, v___x_5388_);
lean_ctor_set_uint8(v___x_5391_, sizeof(void*)*3 + 16, v___x_5389_);
v___x_5392_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5393_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5391_);
lean_ctor_set(v___x_5393_, 1, v_a_5363_);
lean_ctor_set(v___x_5393_, 2, v___x_5392_);
lean_inc(v_ref_5361_);
v___x_5394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5394_, 0, v_ref_5361_);
lean_ctor_set(v___x_5394_, 1, v___x_5393_);
v___x_5395_ = l_Lean_PersistentArray_push___redArg(v_traces_5382_, v___x_5394_);
if (v_isShared_5385_ == 0)
{
lean_ctor_set(v___x_5384_, 0, v___x_5395_);
v___x_5397_ = v___x_5384_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5395_);
lean_ctor_set_uint64(v_reuseFailAlloc_5405_, sizeof(void*)*1, v_tid_5381_);
v___x_5397_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
lean_object* v___x_5399_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 4, v___x_5397_);
v___x_5399_ = v___x_5379_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_env_5369_);
lean_ctor_set(v_reuseFailAlloc_5404_, 1, v_nextMacroScope_5370_);
lean_ctor_set(v_reuseFailAlloc_5404_, 2, v_ngen_5371_);
lean_ctor_set(v_reuseFailAlloc_5404_, 3, v_auxDeclNGen_5372_);
lean_ctor_set(v_reuseFailAlloc_5404_, 4, v___x_5397_);
lean_ctor_set(v_reuseFailAlloc_5404_, 5, v_cache_5373_);
lean_ctor_set(v_reuseFailAlloc_5404_, 6, v_recordedDeps_5374_);
lean_ctor_set(v_reuseFailAlloc_5404_, 7, v_messages_5375_);
lean_ctor_set(v_reuseFailAlloc_5404_, 8, v_infoState_5376_);
lean_ctor_set(v_reuseFailAlloc_5404_, 9, v_snapshotTasks_5377_);
v___x_5399_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
lean_object* v___x_5400_; lean_object* v___x_5402_; 
v___x_5400_ = lean_st_ref_put(v___y_5359_, v___x_5399_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 0, v___x_5386_);
v___x_5402_ = v___x_5365_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v___x_5386_);
v___x_5402_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
return v___x_5402_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5409_, lean_object* v_msg_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v_res_5416_; 
v_res_5416_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5409_, v_msg_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
lean_dec(v___y_5412_);
lean_dec_ref(v___y_5411_);
return v_res_5416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5417_, lean_object* v___x_5418_, lean_object* v_methods_5419_, lean_object* v_config_5420_, lean_object* v_a_5421_, lean_object* v_b_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_){
_start:
{
lean_object* v___y_5437_; uint8_t v___x_5459_; 
v___x_5459_ = lean_nat_dec_lt(v_a_5421_, v_upperBound_5417_);
if (v___x_5459_ == 0)
{
lean_object* v___x_5460_; 
lean_dec(v_a_5421_);
lean_dec_ref(v_config_5420_);
lean_dec_ref(v_methods_5419_);
v___x_5460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5460_, 0, v_b_5422_);
return v___x_5460_;
}
else
{
lean_object* v_snd_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5567_; 
v_snd_5461_ = lean_ctor_get(v_b_5422_, 1);
v_isSharedCheck_5567_ = !lean_is_exclusive(v_b_5422_);
if (v_isSharedCheck_5567_ == 0)
{
lean_object* v_unused_5568_; 
v_unused_5568_ = lean_ctor_get(v_b_5422_, 0);
lean_dec(v_unused_5568_);
v___x_5463_ = v_b_5422_;
v_isShared_5464_ = v_isSharedCheck_5567_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_snd_5461_);
lean_dec(v_b_5422_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5567_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v_type_5470_; lean_object* v___x_5471_; lean_object* v___x_5473_; 
v___x_5465_ = lean_box(0);
v___x_5466_ = lean_array_fget_borrowed(v___x_5418_, v_a_5421_);
v___x_5467_ = lean_st_ref_take(v___y_5423_);
v___x_5468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5469_ = lean_st_ref_put(v___y_5423_, v___x_5468_);
v_type_5470_ = lean_ctor_get(v___x_5466_, 1);
v___x_5471_ = lean_unsigned_to_nat(0u);
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 1, v___x_5467_);
lean_ctor_set(v___x_5463_, 0, v___x_5471_);
v___x_5473_ = v___x_5463_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5467_);
v___x_5473_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
lean_object* v___x_5474_; lean_object* v___x_5475_; 
lean_inc_ref(v_type_5470_);
v___x_5474_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5474_, 0, v_type_5470_);
lean_inc_ref(v_config_5420_);
lean_inc_ref(v_methods_5419_);
v___x_5475_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5474_, v_methods_5419_, v_config_5420_, v___x_5473_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
if (lean_obj_tag(v___x_5475_) == 0)
{
lean_object* v_a_5476_; lean_object* v_snd_5477_; lean_object* v_fst_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5557_; 
v_a_5476_ = lean_ctor_get(v___x_5475_, 0);
lean_inc(v_a_5476_);
lean_dec_ref_known(v___x_5475_, 1);
v_snd_5477_ = lean_ctor_get(v_a_5476_, 1);
v_fst_5478_ = lean_ctor_get(v_a_5476_, 0);
v_isSharedCheck_5557_ = !lean_is_exclusive(v_a_5476_);
if (v_isSharedCheck_5557_ == 0)
{
v___x_5480_ = v_a_5476_;
v_isShared_5481_ = v_isSharedCheck_5557_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_snd_5477_);
lean_inc(v_fst_5478_);
lean_dec(v_a_5476_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5557_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v_cache_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5555_; 
v_cache_5482_ = lean_ctor_get(v_snd_5477_, 1);
v_isSharedCheck_5555_ = !lean_is_exclusive(v_snd_5477_);
if (v_isSharedCheck_5555_ == 0)
{
lean_object* v_unused_5556_; 
v_unused_5556_ = lean_ctor_get(v_snd_5477_, 0);
lean_dec(v_unused_5556_);
v___x_5484_ = v_snd_5477_;
v_isShared_5485_ = v_isSharedCheck_5555_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_cache_5482_);
lean_dec(v_snd_5477_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5555_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5486_ = lean_st_ref_swap(v___y_5423_, v_cache_5482_);
lean_dec(v___x_5486_);
lean_inc(v___x_5466_);
v___x_5487_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5466_, v_fst_5478_);
lean_dec(v_fst_5478_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_a_5488_; lean_object* v_type_5489_; lean_object* v_value_5490_; uint8_t v___x_5491_; 
v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_a_5488_);
lean_dec_ref_known(v___x_5487_, 1);
v_type_5489_ = lean_ctor_get(v_a_5488_, 1);
v_value_5490_ = lean_ctor_get(v_a_5488_, 2);
lean_inc_ref(v_type_5489_);
v___x_5491_ = l_Lean_Expr_isFalse(v_type_5489_);
if (v___x_5491_ == 0)
{
lean_object* v___f_5492_; uint8_t v___x_5522_; 
lean_del_object(v___x_5480_);
lean_inc(v_a_5488_);
lean_inc(v_snd_5461_);
v___f_5492_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5492_, 0, v_snd_5461_);
lean_closure_set(v___f_5492_, 1, v_a_5488_);
lean_closure_set(v___f_5492_, 2, v___x_5465_);
v___x_5522_ = lean_expr_eqv(v_type_5470_, v_type_5489_);
if (v___x_5522_ == 0)
{
lean_inc_ref(v_type_5489_);
lean_dec(v_a_5488_);
lean_dec(v_snd_5461_);
goto v___jp_5496_;
}
else
{
if (v___x_5491_ == 0)
{
lean_object* v___x_5523_; lean_object* v___x_5524_; 
lean_dec_ref(v___f_5492_);
lean_del_object(v___x_5484_);
v___x_5523_ = lean_box(0);
v___x_5524_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5461_, v_a_5488_, v___x_5465_, v___x_5523_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
v___y_5437_ = v___x_5524_;
goto v___jp_5436_;
}
else
{
lean_inc_ref(v_type_5489_);
lean_dec(v_a_5488_);
lean_dec(v_snd_5461_);
goto v___jp_5496_;
}
}
v___jp_5493_:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = lean_box(0);
v___x_5495_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5459_, v___f_5492_, v___x_5494_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
v___y_5437_ = v___x_5495_;
goto v___jp_5436_;
}
v___jp_5496_:
{
lean_object* v_toCold_5497_; lean_object* v_options_5498_; uint8_t v_hasTrace_5499_; 
v_toCold_5497_ = lean_ctor_get(v___y_5433_, 0);
v_options_5498_ = lean_ctor_get(v_toCold_5497_, 2);
v_hasTrace_5499_ = lean_ctor_get_uint8(v_options_5498_, sizeof(void*)*1);
if (v_hasTrace_5499_ == 0)
{
lean_dec_ref(v_type_5489_);
lean_del_object(v___x_5484_);
goto v___jp_5493_;
}
else
{
lean_object* v_inheritedTraceOptions_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; uint8_t v___x_5503_; 
v_inheritedTraceOptions_5500_ = lean_ctor_get(v_toCold_5497_, 11);
v___x_5501_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5502_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5500_, v_options_5498_, v___x_5502_);
if (v___x_5503_ == 0)
{
lean_dec_ref(v_type_5489_);
lean_del_object(v___x_5484_);
goto v___jp_5493_;
}
else
{
lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5507_; 
lean_inc_ref(v_type_5470_);
v___x_5504_ = l_Lean_MessageData_ofExpr(v_type_5470_);
v___x_5505_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5485_ == 0)
{
lean_ctor_set_tag(v___x_5484_, 7);
lean_ctor_set(v___x_5484_, 1, v___x_5505_);
lean_ctor_set(v___x_5484_, 0, v___x_5504_);
v___x_5507_ = v___x_5484_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5504_);
lean_ctor_set(v_reuseFailAlloc_5521_, 1, v___x_5505_);
v___x_5507_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; 
v___x_5508_ = l_Lean_MessageData_ofExpr(v_type_5489_);
v___x_5509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5509_, 0, v___x_5507_);
lean_ctor_set(v___x_5509_, 1, v___x_5508_);
v___x_5510_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5501_, v___x_5509_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
if (lean_obj_tag(v___x_5510_) == 0)
{
lean_object* v_a_5511_; lean_object* v___x_5512_; 
v_a_5511_ = lean_ctor_get(v___x_5510_, 0);
lean_inc(v_a_5511_);
lean_dec_ref_known(v___x_5510_, 1);
v___x_5512_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5459_, v___f_5492_, v_a_5511_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
v___y_5437_ = v___x_5512_;
goto v___jp_5436_;
}
else
{
lean_object* v_a_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5520_; 
lean_dec_ref(v___f_5492_);
lean_dec(v_a_5421_);
lean_dec_ref(v_config_5420_);
lean_dec_ref(v_methods_5419_);
v_a_5513_ = lean_ctor_get(v___x_5510_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5515_ = v___x_5510_;
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_a_5513_);
lean_dec(v___x_5510_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5518_; 
if (v_isShared_5516_ == 0)
{
v___x_5518_ = v___x_5515_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
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
else
{
lean_object* v___x_5525_; 
lean_inc_ref(v_value_5490_);
lean_dec(v_a_5488_);
lean_del_object(v___x_5484_);
lean_dec(v_a_5421_);
lean_dec_ref(v_config_5420_);
lean_dec_ref(v_methods_5419_);
v___x_5525_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5490_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
if (lean_obj_tag(v___x_5525_) == 0)
{
lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5537_; 
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5537_ == 0)
{
lean_object* v_unused_5538_; 
v_unused_5538_ = lean_ctor_get(v___x_5525_, 0);
lean_dec(v_unused_5538_);
v___x_5527_ = v___x_5525_;
v_isShared_5528_ = v_isSharedCheck_5537_;
goto v_resetjp_5526_;
}
else
{
lean_dec(v___x_5525_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5537_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5532_; 
v___x_5529_ = lean_box(v___x_5459_);
v___x_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5530_, 0, v___x_5529_);
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 1, v_snd_5461_);
lean_ctor_set(v___x_5480_, 0, v___x_5530_);
v___x_5532_ = v___x_5480_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v___x_5530_);
lean_ctor_set(v_reuseFailAlloc_5536_, 1, v_snd_5461_);
v___x_5532_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
lean_object* v___x_5534_; 
if (v_isShared_5528_ == 0)
{
lean_ctor_set(v___x_5527_, 0, v___x_5532_);
v___x_5534_ = v___x_5527_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v___x_5532_);
v___x_5534_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
return v___x_5534_;
}
}
}
}
else
{
lean_object* v_a_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
lean_del_object(v___x_5480_);
lean_dec(v_snd_5461_);
v_a_5539_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5525_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_a_5539_);
lean_dec(v___x_5525_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5544_; 
if (v_isShared_5542_ == 0)
{
v___x_5544_ = v___x_5541_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_a_5539_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
}
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
lean_del_object(v___x_5484_);
lean_del_object(v___x_5480_);
lean_dec(v_snd_5461_);
lean_dec(v_a_5421_);
lean_dec_ref(v_config_5420_);
lean_dec_ref(v_methods_5419_);
v_a_5547_ = lean_ctor_get(v___x_5487_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5487_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5549_ = v___x_5487_;
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5487_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
}
}
else
{
lean_object* v_a_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5565_; 
lean_dec(v_snd_5461_);
lean_dec(v_a_5421_);
lean_dec_ref(v_config_5420_);
lean_dec_ref(v_methods_5419_);
v_a_5558_ = lean_ctor_get(v___x_5475_, 0);
v_isSharedCheck_5565_ = !lean_is_exclusive(v___x_5475_);
if (v_isSharedCheck_5565_ == 0)
{
v___x_5560_ = v___x_5475_;
v_isShared_5561_ = v_isSharedCheck_5565_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_a_5558_);
lean_dec(v___x_5475_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5565_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v___x_5563_; 
if (v_isShared_5561_ == 0)
{
v___x_5563_ = v___x_5560_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_a_5558_);
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
}
}
v___jp_5436_:
{
if (lean_obj_tag(v___y_5437_) == 0)
{
lean_object* v_a_5438_; lean_object* v___x_5440_; uint8_t v_isShared_5441_; uint8_t v_isSharedCheck_5450_; 
v_a_5438_ = lean_ctor_get(v___y_5437_, 0);
v_isSharedCheck_5450_ = !lean_is_exclusive(v___y_5437_);
if (v_isSharedCheck_5450_ == 0)
{
v___x_5440_ = v___y_5437_;
v_isShared_5441_ = v_isSharedCheck_5450_;
goto v_resetjp_5439_;
}
else
{
lean_inc(v_a_5438_);
lean_dec(v___y_5437_);
v___x_5440_ = lean_box(0);
v_isShared_5441_ = v_isSharedCheck_5450_;
goto v_resetjp_5439_;
}
v_resetjp_5439_:
{
if (lean_obj_tag(v_a_5438_) == 0)
{
lean_object* v_a_5442_; lean_object* v___x_5444_; 
lean_dec(v_a_5421_);
lean_dec_ref(v_config_5420_);
lean_dec_ref(v_methods_5419_);
v_a_5442_ = lean_ctor_get(v_a_5438_, 0);
lean_inc(v_a_5442_);
lean_dec_ref_known(v_a_5438_, 1);
if (v_isShared_5441_ == 0)
{
lean_ctor_set(v___x_5440_, 0, v_a_5442_);
v___x_5444_ = v___x_5440_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5442_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
lean_del_object(v___x_5440_);
v_a_5446_ = lean_ctor_get(v_a_5438_, 0);
lean_inc(v_a_5446_);
lean_dec_ref_known(v_a_5438_, 1);
v___x_5447_ = lean_unsigned_to_nat(1u);
v___x_5448_ = lean_nat_add(v_a_5421_, v___x_5447_);
lean_dec(v_a_5421_);
v_a_5421_ = v___x_5448_;
v_b_5422_ = v_a_5446_;
goto _start;
}
}
}
else
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec(v_a_5421_);
lean_dec_ref(v_config_5420_);
lean_dec_ref(v_methods_5419_);
v_a_5451_ = lean_ctor_get(v___y_5437_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___y_5437_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___y_5437_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___y_5437_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5456_; 
if (v_isShared_5454_ == 0)
{
v___x_5456_ = v___x_5453_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5451_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5569_ = _args[0];
lean_object* v___x_5570_ = _args[1];
lean_object* v_methods_5571_ = _args[2];
lean_object* v_config_5572_ = _args[3];
lean_object* v_a_5573_ = _args[4];
lean_object* v_b_5574_ = _args[5];
lean_object* v___y_5575_ = _args[6];
lean_object* v___y_5576_ = _args[7];
lean_object* v___y_5577_ = _args[8];
lean_object* v___y_5578_ = _args[9];
lean_object* v___y_5579_ = _args[10];
lean_object* v___y_5580_ = _args[11];
lean_object* v___y_5581_ = _args[12];
lean_object* v___y_5582_ = _args[13];
lean_object* v___y_5583_ = _args[14];
lean_object* v___y_5584_ = _args[15];
lean_object* v___y_5585_ = _args[16];
lean_object* v___y_5586_ = _args[17];
lean_object* v___y_5587_ = _args[18];
_start:
{
lean_object* v_res_5588_; 
v_res_5588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5569_, v___x_5570_, v_methods_5571_, v_config_5572_, v_a_5573_, v_b_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
lean_dec(v___y_5582_);
lean_dec_ref(v___y_5581_);
lean_dec(v___y_5580_);
lean_dec_ref(v___y_5579_);
lean_dec(v___y_5578_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___x_5570_);
lean_dec(v_upperBound_5569_);
return v_res_5588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5589_, lean_object* v_config_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_){
_start:
{
lean_object* v___x_5604_; lean_object* v_hypotheses_5605_; lean_object* v___x_5606_; lean_object* v_newHyps_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
v___x_5604_ = lean_st_ref_get(v_a_5593_);
v_hypotheses_5605_ = lean_ctor_get(v___x_5604_, 3);
lean_inc_ref(v_hypotheses_5605_);
lean_dec(v___x_5604_);
v___x_5606_ = lean_array_get_size(v_hypotheses_5605_);
v_newHyps_5607_ = lean_mk_empty_array_with_capacity(v___x_5606_);
v___x_5608_ = lean_unsigned_to_nat(0u);
v___x_5609_ = lean_box(0);
v___x_5610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5609_);
lean_ctor_set(v___x_5610_, 1, v_newHyps_5607_);
v___x_5611_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5606_, v_hypotheses_5605_, v_methods_5589_, v_config_5590_, v___x_5608_, v___x_5610_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_, v_a_5600_, v_a_5601_, v_a_5602_);
lean_dec_ref(v_hypotheses_5605_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5641_; 
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5614_ = v___x_5611_;
v_isShared_5615_ = v_isSharedCheck_5641_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5611_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5641_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v_fst_5616_; 
v_fst_5616_ = lean_ctor_get(v_a_5612_, 0);
if (lean_obj_tag(v_fst_5616_) == 0)
{
lean_object* v_snd_5617_; lean_object* v___x_5618_; lean_object* v_caches_5619_; lean_object* v_typeAnalysis_5620_; lean_object* v_target_5621_; uint8_t v_didChange_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5635_; 
v_snd_5617_ = lean_ctor_get(v_a_5612_, 1);
lean_inc(v_snd_5617_);
lean_dec(v_a_5612_);
v___x_5618_ = lean_st_ref_take(v_a_5593_);
v_caches_5619_ = lean_ctor_get(v___x_5618_, 0);
v_typeAnalysis_5620_ = lean_ctor_get(v___x_5618_, 1);
v_target_5621_ = lean_ctor_get(v___x_5618_, 2);
v_didChange_5622_ = lean_ctor_get_uint8(v___x_5618_, sizeof(void*)*4);
v_isSharedCheck_5635_ = !lean_is_exclusive(v___x_5618_);
if (v_isSharedCheck_5635_ == 0)
{
lean_object* v_unused_5636_; 
v_unused_5636_ = lean_ctor_get(v___x_5618_, 3);
lean_dec(v_unused_5636_);
v___x_5624_ = v___x_5618_;
v_isShared_5625_ = v_isSharedCheck_5635_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_target_5621_);
lean_inc(v_typeAnalysis_5620_);
lean_inc(v_caches_5619_);
lean_dec(v___x_5618_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5635_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5627_; 
if (v_isShared_5625_ == 0)
{
lean_ctor_set(v___x_5624_, 3, v_snd_5617_);
v___x_5627_ = v___x_5624_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_caches_5619_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v_typeAnalysis_5620_);
lean_ctor_set(v_reuseFailAlloc_5634_, 2, v_target_5621_);
lean_ctor_set(v_reuseFailAlloc_5634_, 3, v_snd_5617_);
lean_ctor_set_uint8(v_reuseFailAlloc_5634_, sizeof(void*)*4, v_didChange_5622_);
v___x_5627_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
lean_object* v___x_5628_; uint8_t v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5632_; 
v___x_5628_ = lean_st_ref_put(v_a_5593_, v___x_5627_);
v___x_5629_ = 0;
v___x_5630_ = lean_box(v___x_5629_);
if (v_isShared_5615_ == 0)
{
lean_ctor_set(v___x_5614_, 0, v___x_5630_);
v___x_5632_ = v___x_5614_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v___x_5630_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
}
else
{
lean_object* v_val_5637_; lean_object* v___x_5639_; 
lean_inc_ref(v_fst_5616_);
lean_dec(v_a_5612_);
v_val_5637_ = lean_ctor_get(v_fst_5616_, 0);
lean_inc(v_val_5637_);
lean_dec_ref_known(v_fst_5616_, 1);
if (v_isShared_5615_ == 0)
{
lean_ctor_set(v___x_5614_, 0, v_val_5637_);
v___x_5639_ = v___x_5614_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_val_5637_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
}
else
{
lean_object* v_a_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5649_; 
v_a_5642_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5649_ == 0)
{
v___x_5644_ = v___x_5611_;
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_a_5642_);
lean_dec(v___x_5611_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5650_, lean_object* v_config_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_){
_start:
{
lean_object* v_res_5665_; 
v_res_5665_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5650_, v_config_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
lean_dec(v_a_5661_);
lean_dec_ref(v_a_5660_);
lean_dec(v_a_5659_);
lean_dec_ref(v_a_5658_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
lean_dec(v_a_5655_);
lean_dec(v_a_5654_);
lean_dec_ref(v_a_5653_);
lean_dec(v_a_5652_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5666_, lean_object* v_msg_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_){
_start:
{
lean_object* v___x_5681_; 
v___x_5681_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5666_, v_msg_5667_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
return v___x_5681_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5682_, lean_object* v_msg_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5682_, v_msg_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_);
lean_dec(v___y_5695_);
lean_dec_ref(v___y_5694_);
lean_dec(v___y_5693_);
lean_dec_ref(v___y_5692_);
lean_dec(v___y_5691_);
lean_dec_ref(v___y_5690_);
lean_dec(v___y_5689_);
lean_dec_ref(v___y_5688_);
lean_dec(v___y_5687_);
lean_dec(v___y_5686_);
lean_dec_ref(v___y_5685_);
lean_dec(v___y_5684_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5698_, lean_object* v___x_5699_, lean_object* v_methods_5700_, lean_object* v_config_5701_, lean_object* v_inst_5702_, lean_object* v_R_5703_, lean_object* v_a_5704_, lean_object* v_b_5705_, lean_object* v_c_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_){
_start:
{
lean_object* v___x_5720_; 
v___x_5720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5698_, v___x_5699_, v_methods_5700_, v_config_5701_, v_a_5704_, v_b_5705_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_);
return v___x_5720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5721_ = _args[0];
lean_object* v___x_5722_ = _args[1];
lean_object* v_methods_5723_ = _args[2];
lean_object* v_config_5724_ = _args[3];
lean_object* v_inst_5725_ = _args[4];
lean_object* v_R_5726_ = _args[5];
lean_object* v_a_5727_ = _args[6];
lean_object* v_b_5728_ = _args[7];
lean_object* v_c_5729_ = _args[8];
lean_object* v___y_5730_ = _args[9];
lean_object* v___y_5731_ = _args[10];
lean_object* v___y_5732_ = _args[11];
lean_object* v___y_5733_ = _args[12];
lean_object* v___y_5734_ = _args[13];
lean_object* v___y_5735_ = _args[14];
lean_object* v___y_5736_ = _args[15];
lean_object* v___y_5737_ = _args[16];
lean_object* v___y_5738_ = _args[17];
lean_object* v___y_5739_ = _args[18];
lean_object* v___y_5740_ = _args[19];
lean_object* v___y_5741_ = _args[20];
lean_object* v___y_5742_ = _args[21];
_start:
{
lean_object* v_res_5743_; 
v_res_5743_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5721_, v___x_5722_, v_methods_5723_, v_config_5724_, v_inst_5725_, v_R_5726_, v_a_5727_, v_b_5728_, v_c_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
lean_dec(v___y_5741_);
lean_dec_ref(v___y_5740_);
lean_dec(v___y_5739_);
lean_dec_ref(v___y_5738_);
lean_dec(v___y_5737_);
lean_dec_ref(v___y_5736_);
lean_dec(v___y_5735_);
lean_dec_ref(v___y_5734_);
lean_dec(v___y_5733_);
lean_dec(v___y_5732_);
lean_dec_ref(v___y_5731_);
lean_dec(v___y_5730_);
lean_dec_ref(v___x_5722_);
lean_dec(v_upperBound_5721_);
return v_res_5743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5744_, lean_object* v_config_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_){
_start:
{
lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; 
v___x_5758_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5759_ = lean_st_mk_ref(v___x_5758_);
v___x_5760_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5744_, v_config_5745_, v___x_5759_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_, v_a_5755_, v_a_5756_);
if (lean_obj_tag(v___x_5760_) == 0)
{
lean_object* v_a_5761_; lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5769_; 
v_a_5761_ = lean_ctor_get(v___x_5760_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v___x_5760_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5763_ = v___x_5760_;
v_isShared_5764_ = v_isSharedCheck_5769_;
goto v_resetjp_5762_;
}
else
{
lean_inc(v_a_5761_);
lean_dec(v___x_5760_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5769_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
lean_object* v___x_5765_; lean_object* v___x_5767_; 
v___x_5765_ = lean_st_ref_get(v___x_5759_);
lean_dec(v___x_5759_);
lean_dec(v___x_5765_);
if (v_isShared_5764_ == 0)
{
v___x_5767_ = v___x_5763_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5761_);
v___x_5767_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
return v___x_5767_;
}
}
}
else
{
lean_dec(v___x_5759_);
return v___x_5760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5770_, lean_object* v_config_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5770_, v_config_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_);
lean_dec(v_a_5782_);
lean_dec_ref(v_a_5781_);
lean_dec(v_a_5780_);
lean_dec_ref(v_a_5779_);
lean_dec(v_a_5778_);
lean_dec_ref(v_a_5777_);
lean_dec(v_a_5776_);
lean_dec_ref(v_a_5775_);
lean_dec(v_a_5774_);
lean_dec(v_a_5773_);
lean_dec_ref(v_a_5772_);
return v_res_5784_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5786_; lean_object* v___x_5787_; 
v___x_5786_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5787_ = l_Lean_stringToMessageData(v___x_5786_);
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5788_, lean_object* v_x_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_){
_start:
{
lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; 
v___x_5802_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5803_ = l_Lean_MessageData_ofName(v_name_5788_);
v___x_5804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5804_, 0, v___x_5802_);
lean_ctor_set(v___x_5804_, 1, v___x_5803_);
v___x_5805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5805_, 0, v___x_5804_);
return v___x_5805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5806_, lean_object* v_x_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_){
_start:
{
lean_object* v_res_5820_; 
v_res_5820_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5806_, v_x_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
lean_dec(v___y_5812_);
lean_dec_ref(v___y_5811_);
lean_dec(v___y_5810_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5808_);
lean_dec_ref(v_x_5807_);
return v_res_5820_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5821_; 
v___x_5821_ = l_instMonadExceptOfEIO___redArg();
return v___x_5821_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5823_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5822_);
return v___x_5823_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5824_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5825_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5824_);
return v___x_5825_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5826_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5827_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5826_);
return v___x_5827_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5828_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5829_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5828_);
return v___x_5829_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; 
v___x_5830_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5831_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5830_);
return v___x_5831_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5833_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5832_);
return v___x_5833_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; 
v___x_5834_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5835_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5834_);
return v___x_5835_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5836_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5837_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5836_);
return v___x_5837_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5839_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5838_);
return v___x_5839_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5840_; lean_object* v___x_5841_; 
v___x_5840_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5841_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5840_);
return v___x_5841_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; 
v___x_5842_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5843_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5842_);
return v___x_5843_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5845_; double v___x_5846_; 
v___x_5845_ = lean_unsigned_to_nat(1000000000u);
v___x_5846_ = lean_float_of_nat(v___x_5845_);
return v___x_5846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_){
_start:
{
lean_object* v___x_5860_; lean_object* v_toApplicative_5861_; lean_object* v_toFunctor_5862_; lean_object* v_toSeq_5863_; lean_object* v_toSeqLeft_5864_; lean_object* v_toSeqRight_5865_; lean_object* v___f_5866_; lean_object* v___f_5867_; lean_object* v___f_5868_; lean_object* v___f_5869_; lean_object* v___x_5870_; lean_object* v___f_5871_; lean_object* v___f_5872_; lean_object* v___f_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v_toApplicative_5877_; lean_object* v___x_5879_; uint8_t v_isShared_5880_; uint8_t v_isSharedCheck_6020_; 
v___x_5860_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5861_ = lean_ctor_get(v___x_5860_, 0);
v_toFunctor_5862_ = lean_ctor_get(v_toApplicative_5861_, 0);
v_toSeq_5863_ = lean_ctor_get(v_toApplicative_5861_, 2);
v_toSeqLeft_5864_ = lean_ctor_get(v_toApplicative_5861_, 3);
v_toSeqRight_5865_ = lean_ctor_get(v_toApplicative_5861_, 4);
v___f_5866_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5867_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5862_, 2);
v___f_5868_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5868_, 0, v_toFunctor_5862_);
v___f_5869_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5869_, 0, v_toFunctor_5862_);
v___x_5870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5870_, 0, v___f_5868_);
lean_ctor_set(v___x_5870_, 1, v___f_5869_);
lean_inc(v_toSeqRight_5865_);
v___f_5871_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5871_, 0, v_toSeqRight_5865_);
lean_inc(v_toSeqLeft_5864_);
v___f_5872_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5872_, 0, v_toSeqLeft_5864_);
lean_inc(v_toSeq_5863_);
v___f_5873_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5873_, 0, v_toSeq_5863_);
v___x_5874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5874_, 0, v___x_5870_);
lean_ctor_set(v___x_5874_, 1, v___f_5866_);
lean_ctor_set(v___x_5874_, 2, v___f_5873_);
lean_ctor_set(v___x_5874_, 3, v___f_5872_);
lean_ctor_set(v___x_5874_, 4, v___f_5871_);
v___x_5875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
lean_ctor_set(v___x_5875_, 1, v___f_5867_);
v___x_5876_ = l_StateRefT_x27_instMonad___redArg(v___x_5875_);
v_toApplicative_5877_ = lean_ctor_get(v___x_5876_, 0);
v_isSharedCheck_6020_ = !lean_is_exclusive(v___x_5876_);
if (v_isSharedCheck_6020_ == 0)
{
lean_object* v_unused_6021_; 
v_unused_6021_ = lean_ctor_get(v___x_5876_, 1);
lean_dec(v_unused_6021_);
v___x_5879_ = v___x_5876_;
v_isShared_5880_ = v_isSharedCheck_6020_;
goto v_resetjp_5878_;
}
else
{
lean_inc(v_toApplicative_5877_);
lean_dec(v___x_5876_);
v___x_5879_ = lean_box(0);
v_isShared_5880_ = v_isSharedCheck_6020_;
goto v_resetjp_5878_;
}
v_resetjp_5878_:
{
lean_object* v_toFunctor_5881_; lean_object* v_toSeq_5882_; lean_object* v_toSeqLeft_5883_; lean_object* v_toSeqRight_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_6018_; 
v_toFunctor_5881_ = lean_ctor_get(v_toApplicative_5877_, 0);
v_toSeq_5882_ = lean_ctor_get(v_toApplicative_5877_, 2);
v_toSeqLeft_5883_ = lean_ctor_get(v_toApplicative_5877_, 3);
v_toSeqRight_5884_ = lean_ctor_get(v_toApplicative_5877_, 4);
v_isSharedCheck_6018_ = !lean_is_exclusive(v_toApplicative_5877_);
if (v_isSharedCheck_6018_ == 0)
{
lean_object* v_unused_6019_; 
v_unused_6019_ = lean_ctor_get(v_toApplicative_5877_, 1);
lean_dec(v_unused_6019_);
v___x_5886_ = v_toApplicative_5877_;
v_isShared_5887_ = v_isSharedCheck_6018_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_toSeqRight_5884_);
lean_inc(v_toSeqLeft_5883_);
lean_inc(v_toSeq_5882_);
lean_inc(v_toFunctor_5881_);
lean_dec(v_toApplicative_5877_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_6018_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___f_5888_; lean_object* v___f_5889_; lean_object* v___f_5890_; lean_object* v___f_5891_; lean_object* v___x_5892_; lean_object* v___f_5893_; lean_object* v___f_5894_; lean_object* v___f_5895_; lean_object* v___x_5897_; 
v___f_5888_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5889_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5881_);
v___f_5890_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5890_, 0, v_toFunctor_5881_);
v___f_5891_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5891_, 0, v_toFunctor_5881_);
v___x_5892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___f_5890_);
lean_ctor_set(v___x_5892_, 1, v___f_5891_);
v___f_5893_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5893_, 0, v_toSeqRight_5884_);
v___f_5894_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5894_, 0, v_toSeqLeft_5883_);
v___f_5895_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5895_, 0, v_toSeq_5882_);
if (v_isShared_5887_ == 0)
{
lean_ctor_set(v___x_5886_, 4, v___f_5893_);
lean_ctor_set(v___x_5886_, 3, v___f_5894_);
lean_ctor_set(v___x_5886_, 2, v___f_5895_);
lean_ctor_set(v___x_5886_, 1, v___f_5888_);
lean_ctor_set(v___x_5886_, 0, v___x_5892_);
v___x_5897_ = v___x_5886_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_6017_; 
v_reuseFailAlloc_6017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6017_, 0, v___x_5892_);
lean_ctor_set(v_reuseFailAlloc_6017_, 1, v___f_5888_);
lean_ctor_set(v_reuseFailAlloc_6017_, 2, v___f_5895_);
lean_ctor_set(v_reuseFailAlloc_6017_, 3, v___f_5894_);
lean_ctor_set(v_reuseFailAlloc_6017_, 4, v___f_5893_);
v___x_5897_ = v_reuseFailAlloc_6017_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
lean_object* v___x_5899_; 
if (v_isShared_5880_ == 0)
{
lean_ctor_set(v___x_5879_, 1, v___f_5889_);
lean_ctor_set(v___x_5879_, 0, v___x_5897_);
v___x_5899_ = v___x_5879_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v___x_5897_);
lean_ctor_set(v_reuseFailAlloc_6016_, 1, v___f_5889_);
v___x_5899_ = v_reuseFailAlloc_6016_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v_toMonadRef_5909_; lean_object* v___x_5910_; lean_object* v_name_5911_; lean_object* v_run_x27_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_6015_; 
v___x_5900_ = l_StateRefT_x27_instMonad___redArg(v___x_5899_);
v___x_5901_ = l_ReaderT_instMonad___redArg(v___x_5900_);
v___x_5902_ = l_StateRefT_x27_instMonad___redArg(v___x_5901_);
v___x_5903_ = l_ReaderT_instMonad___redArg(v___x_5902_);
v___x_5904_ = l_ReaderT_instMonad___redArg(v___x_5903_);
v___x_5905_ = l_StateRefT_x27_instMonad___redArg(v___x_5904_);
v___x_5906_ = l_ReaderT_instMonad___redArg(v___x_5905_);
v___x_5907_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5908_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_5909_ = lean_ctor_get(v___x_5908_, 0);
v___x_5910_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_name_5911_ = lean_ctor_get(v_pass_5847_, 0);
v_run_x27_5912_ = lean_ctor_get(v_pass_5847_, 1);
v_isSharedCheck_6015_ = !lean_is_exclusive(v_pass_5847_);
if (v_isSharedCheck_6015_ == 0)
{
v___x_5914_ = v_pass_5847_;
v_isShared_5915_ = v_isSharedCheck_6015_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_run_x27_5912_);
lean_inc(v_name_5911_);
lean_dec(v_pass_5847_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_6015_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
lean_object* v___x_5916_; lean_object* v_toCold_5917_; lean_object* v_options_5918_; uint8_t v_hasTrace_5919_; 
v___x_5916_ = l_Lean_KVMap_instValueBool;
v_toCold_5917_ = lean_ctor_get(v_a_5857_, 0);
v_options_5918_ = lean_ctor_get(v_toCold_5917_, 2);
v_hasTrace_5919_ = lean_ctor_get_uint8(v_options_5918_, sizeof(void*)*1);
if (v_hasTrace_5919_ == 0)
{
lean_object* v___x_5920_; 
lean_del_object(v___x_5914_);
lean_dec(v_name_5911_);
lean_dec_ref(v___x_5906_);
lean_inc(v_a_5858_);
lean_inc_ref(v_a_5857_);
lean_inc(v_a_5856_);
lean_inc_ref(v_a_5855_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
v___x_5920_ = lean_apply_12(v_run_x27_5912_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, lean_box(0));
return v___x_5920_;
}
else
{
lean_object* v_inheritedTraceOptions_5921_; lean_object* v___f_5922_; lean_object* v___f_5923_; lean_object* v___f_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; uint8_t v___x_5928_; lean_object* v___y_5930_; lean_object* v___y_5931_; lean_object* v_a_5932_; lean_object* v___y_5948_; lean_object* v___y_5949_; lean_object* v_a_5950_; 
v_inheritedTraceOptions_5921_ = lean_ctor_get(v_toCold_5917_, 11);
v___f_5922_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5922_, 0, v_name_5911_);
v___f_5923_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_5924_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5925_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5926_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5927_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5928_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5921_, v_options_5918_, v___x_5927_);
if (v___x_5928_ == 0)
{
lean_object* v___x_6011_; lean_object* v___x_6012_; uint8_t v___x_6013_; 
v___x_6011_ = l_Lean_trace_profiler;
v___x_6012_ = l_Lean_Option_get___redArg(v___x_5916_, v_options_5918_, v___x_6011_);
v___x_6013_ = lean_unbox(v___x_6012_);
lean_dec(v___x_6012_);
if (v___x_6013_ == 0)
{
lean_object* v___x_6014_; 
lean_dec_ref(v___f_5922_);
lean_del_object(v___x_5914_);
lean_dec_ref(v___x_5906_);
lean_inc(v_a_5858_);
lean_inc_ref(v_a_5857_);
lean_inc(v_a_5856_);
lean_inc_ref(v_a_5855_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
v___x_6014_ = lean_apply_12(v_run_x27_5912_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, lean_box(0));
return v___x_6014_;
}
else
{
goto v___jp_5960_;
}
}
else
{
goto v___jp_5960_;
}
v___jp_5929_:
{
lean_object* v___x_5933_; double v___x_5934_; double v___x_5935_; double v___x_5936_; double v___x_5937_; double v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5942_; 
v___x_5933_ = lean_io_mono_nanos_now();
v___x_5934_ = lean_float_of_nat(v___y_5930_);
v___x_5935_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5936_ = lean_float_div(v___x_5934_, v___x_5935_);
v___x_5937_ = lean_float_of_nat(v___x_5933_);
v___x_5938_ = lean_float_div(v___x_5937_, v___x_5935_);
v___x_5939_ = lean_box_float(v___x_5936_);
v___x_5940_ = lean_box_float(v___x_5938_);
if (v_isShared_5915_ == 0)
{
lean_ctor_set(v___x_5914_, 1, v___x_5940_);
lean_ctor_set(v___x_5914_, 0, v___x_5939_);
v___x_5942_ = v___x_5914_;
goto v_reusejp_5941_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v___x_5939_);
lean_ctor_set(v_reuseFailAlloc_5946_, 1, v___x_5940_);
v___x_5942_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5941_;
}
v_reusejp_5941_:
{
lean_object* v___x_5943_; lean_object* v___x_28875__overap_5944_; lean_object* v___x_5945_; 
v___x_5943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5943_, 0, v_a_5932_);
lean_ctor_set(v___x_5943_, 1, v___x_5942_);
lean_inc_ref(v_toMonadRef_5909_);
v___x_28875__overap_5944_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5906_, v___x_5907_, v_toMonadRef_5909_, v___f_5923_, lean_box(0), v___x_5910_, v___f_5924_, v___x_5925_, v_hasTrace_5919_, v___x_5926_, v_options_5918_, v___x_5928_, v___y_5931_, v___f_5922_, v___x_5943_);
lean_inc(v_a_5858_);
lean_inc_ref(v_a_5857_);
lean_inc(v_a_5856_);
lean_inc_ref(v_a_5855_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
v___x_5945_ = lean_apply_12(v___x_28875__overap_5944_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, lean_box(0));
return v___x_5945_;
}
}
v___jp_5947_:
{
lean_object* v___x_5951_; double v___x_5952_; double v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_28896__overap_5958_; lean_object* v___x_5959_; 
v___x_5951_ = lean_io_get_num_heartbeats();
v___x_5952_ = lean_float_of_nat(v___y_5949_);
v___x_5953_ = lean_float_of_nat(v___x_5951_);
v___x_5954_ = lean_box_float(v___x_5952_);
v___x_5955_ = lean_box_float(v___x_5953_);
v___x_5956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5954_);
lean_ctor_set(v___x_5956_, 1, v___x_5955_);
v___x_5957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5957_, 0, v_a_5950_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
lean_inc_ref(v_toMonadRef_5909_);
v___x_28896__overap_5958_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5906_, v___x_5907_, v_toMonadRef_5909_, v___f_5923_, lean_box(0), v___x_5910_, v___f_5924_, v___x_5925_, v_hasTrace_5919_, v___x_5926_, v_options_5918_, v___x_5928_, v___y_5948_, v___f_5922_, v___x_5957_);
lean_inc(v_a_5858_);
lean_inc_ref(v_a_5857_);
lean_inc(v_a_5856_);
lean_inc_ref(v_a_5855_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
v___x_5959_ = lean_apply_12(v___x_28896__overap_5958_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, lean_box(0));
return v___x_5959_;
}
v___jp_5960_:
{
lean_object* v___x_28853__overap_5961_; lean_object* v___x_5962_; 
lean_inc_ref(v___x_5906_);
v___x_28853__overap_5961_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5906_, v___x_5907_);
lean_inc(v_a_5858_);
lean_inc_ref(v_a_5857_);
lean_inc(v_a_5856_);
lean_inc_ref(v_a_5855_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
v___x_5962_ = lean_apply_12(v___x_28853__overap_5961_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, lean_box(0));
if (lean_obj_tag(v___x_5962_) == 0)
{
lean_object* v_a_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; uint8_t v___x_5966_; 
v_a_5963_ = lean_ctor_get(v___x_5962_, 0);
lean_inc(v_a_5963_);
lean_dec_ref_known(v___x_5962_, 1);
v___x_5964_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5965_ = l_Lean_Option_get___redArg(v___x_5916_, v_options_5918_, v___x_5964_);
v___x_5966_ = lean_unbox(v___x_5965_);
lean_dec(v___x_5965_);
if (v___x_5966_ == 0)
{
lean_object* v___x_5967_; lean_object* v___x_5968_; 
v___x_5967_ = lean_io_mono_nanos_now();
lean_inc(v_a_5858_);
lean_inc_ref(v_a_5857_);
lean_inc(v_a_5856_);
lean_inc_ref(v_a_5855_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
v___x_5968_ = lean_apply_12(v_run_x27_5912_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, lean_box(0));
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_object* v_a_5969_; lean_object* v___x_5971_; uint8_t v_isShared_5972_; uint8_t v_isSharedCheck_5976_; 
v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
v_isSharedCheck_5976_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_5976_ == 0)
{
v___x_5971_ = v___x_5968_;
v_isShared_5972_ = v_isSharedCheck_5976_;
goto v_resetjp_5970_;
}
else
{
lean_inc(v_a_5969_);
lean_dec(v___x_5968_);
v___x_5971_ = lean_box(0);
v_isShared_5972_ = v_isSharedCheck_5976_;
goto v_resetjp_5970_;
}
v_resetjp_5970_:
{
lean_object* v___x_5974_; 
if (v_isShared_5972_ == 0)
{
lean_ctor_set_tag(v___x_5971_, 1);
v___x_5974_ = v___x_5971_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_a_5969_);
v___x_5974_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
v___y_5930_ = v___x_5967_;
v___y_5931_ = v_a_5963_;
v_a_5932_ = v___x_5974_;
goto v___jp_5929_;
}
}
}
else
{
lean_object* v_a_5977_; lean_object* v___x_5979_; uint8_t v_isShared_5980_; uint8_t v_isSharedCheck_5984_; 
v_a_5977_ = lean_ctor_get(v___x_5968_, 0);
v_isSharedCheck_5984_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_5984_ == 0)
{
v___x_5979_ = v___x_5968_;
v_isShared_5980_ = v_isSharedCheck_5984_;
goto v_resetjp_5978_;
}
else
{
lean_inc(v_a_5977_);
lean_dec(v___x_5968_);
v___x_5979_ = lean_box(0);
v_isShared_5980_ = v_isSharedCheck_5984_;
goto v_resetjp_5978_;
}
v_resetjp_5978_:
{
lean_object* v___x_5982_; 
if (v_isShared_5980_ == 0)
{
lean_ctor_set_tag(v___x_5979_, 0);
v___x_5982_ = v___x_5979_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v_a_5977_);
v___x_5982_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
v___y_5930_ = v___x_5967_;
v___y_5931_ = v_a_5963_;
v_a_5932_ = v___x_5982_;
goto v___jp_5929_;
}
}
}
}
else
{
lean_object* v___x_5985_; lean_object* v___x_5986_; 
lean_del_object(v___x_5914_);
v___x_5985_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5858_);
lean_inc_ref(v_a_5857_);
lean_inc(v_a_5856_);
lean_inc_ref(v_a_5855_);
lean_inc(v_a_5854_);
lean_inc_ref(v_a_5853_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc(v_a_5849_);
lean_inc_ref(v_a_5848_);
v___x_5986_ = lean_apply_12(v_run_x27_5912_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, lean_box(0));
if (lean_obj_tag(v___x_5986_) == 0)
{
lean_object* v_a_5987_; lean_object* v___x_5989_; uint8_t v_isShared_5990_; uint8_t v_isSharedCheck_5994_; 
v_a_5987_ = lean_ctor_get(v___x_5986_, 0);
v_isSharedCheck_5994_ = !lean_is_exclusive(v___x_5986_);
if (v_isSharedCheck_5994_ == 0)
{
v___x_5989_ = v___x_5986_;
v_isShared_5990_ = v_isSharedCheck_5994_;
goto v_resetjp_5988_;
}
else
{
lean_inc(v_a_5987_);
lean_dec(v___x_5986_);
v___x_5989_ = lean_box(0);
v_isShared_5990_ = v_isSharedCheck_5994_;
goto v_resetjp_5988_;
}
v_resetjp_5988_:
{
lean_object* v___x_5992_; 
if (v_isShared_5990_ == 0)
{
lean_ctor_set_tag(v___x_5989_, 1);
v___x_5992_ = v___x_5989_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v_a_5987_);
v___x_5992_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5991_;
}
v_reusejp_5991_:
{
v___y_5948_ = v_a_5963_;
v___y_5949_ = v___x_5985_;
v_a_5950_ = v___x_5992_;
goto v___jp_5947_;
}
}
}
else
{
lean_object* v_a_5995_; lean_object* v___x_5997_; uint8_t v_isShared_5998_; uint8_t v_isSharedCheck_6002_; 
v_a_5995_ = lean_ctor_get(v___x_5986_, 0);
v_isSharedCheck_6002_ = !lean_is_exclusive(v___x_5986_);
if (v_isSharedCheck_6002_ == 0)
{
v___x_5997_ = v___x_5986_;
v_isShared_5998_ = v_isSharedCheck_6002_;
goto v_resetjp_5996_;
}
else
{
lean_inc(v_a_5995_);
lean_dec(v___x_5986_);
v___x_5997_ = lean_box(0);
v_isShared_5998_ = v_isSharedCheck_6002_;
goto v_resetjp_5996_;
}
v_resetjp_5996_:
{
lean_object* v___x_6000_; 
if (v_isShared_5998_ == 0)
{
lean_ctor_set_tag(v___x_5997_, 0);
v___x_6000_ = v___x_5997_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v_a_5995_);
v___x_6000_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
v___y_5948_ = v_a_5963_;
v___y_5949_ = v___x_5985_;
v_a_5950_ = v___x_6000_;
goto v___jp_5947_;
}
}
}
}
}
else
{
lean_object* v_a_6003_; lean_object* v___x_6005_; uint8_t v_isShared_6006_; uint8_t v_isSharedCheck_6010_; 
lean_dec_ref(v___f_5922_);
lean_del_object(v___x_5914_);
lean_dec_ref(v_run_x27_5912_);
lean_dec_ref(v___x_5906_);
v_a_6003_ = lean_ctor_get(v___x_5962_, 0);
v_isSharedCheck_6010_ = !lean_is_exclusive(v___x_5962_);
if (v_isSharedCheck_6010_ == 0)
{
v___x_6005_ = v___x_5962_;
v_isShared_6006_ = v_isSharedCheck_6010_;
goto v_resetjp_6004_;
}
else
{
lean_inc(v_a_6003_);
lean_dec(v___x_5962_);
v___x_6005_ = lean_box(0);
v_isShared_6006_ = v_isSharedCheck_6010_;
goto v_resetjp_6004_;
}
v_resetjp_6004_:
{
lean_object* v___x_6008_; 
if (v_isShared_6006_ == 0)
{
v___x_6008_ = v___x_6005_;
goto v_reusejp_6007_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v_a_6003_);
v___x_6008_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6007_;
}
v_reusejp_6007_:
{
return v___x_6008_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_, lean_object* v_a_6034_){
_start:
{
lean_object* v_res_6035_; 
v_res_6035_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6022_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_, v_a_6031_, v_a_6032_, v_a_6033_);
lean_dec(v_a_6033_);
lean_dec_ref(v_a_6032_);
lean_dec(v_a_6031_);
lean_dec_ref(v_a_6030_);
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6028_);
lean_dec(v_a_6027_);
lean_dec_ref(v_a_6026_);
lean_dec(v_a_6025_);
lean_dec(v_a_6024_);
lean_dec_ref(v_a_6023_);
return v_res_6035_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; 
v___x_6036_ = lean_unsigned_to_nat(32u);
v___x_6037_ = lean_mk_empty_array_with_capacity(v___x_6036_);
v___x_6038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
return v___x_6038_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; 
v___x_6039_ = ((size_t)5ULL);
v___x_6040_ = lean_unsigned_to_nat(0u);
v___x_6041_ = lean_unsigned_to_nat(32u);
v___x_6042_ = lean_mk_empty_array_with_capacity(v___x_6041_);
v___x_6043_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6044_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6044_, 0, v___x_6043_);
lean_ctor_set(v___x_6044_, 1, v___x_6042_);
lean_ctor_set(v___x_6044_, 2, v___x_6040_);
lean_ctor_set(v___x_6044_, 3, v___x_6040_);
lean_ctor_set_usize(v___x_6044_, 4, v___x_6039_);
return v___x_6044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6045_){
_start:
{
lean_object* v___x_6047_; lean_object* v_traceState_6048_; lean_object* v_traces_6049_; lean_object* v___x_6050_; lean_object* v_traceState_6051_; lean_object* v_env_6052_; lean_object* v_nextMacroScope_6053_; lean_object* v_ngen_6054_; lean_object* v_auxDeclNGen_6055_; lean_object* v_cache_6056_; lean_object* v_recordedDeps_6057_; lean_object* v_messages_6058_; lean_object* v_infoState_6059_; lean_object* v_snapshotTasks_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6079_; 
v___x_6047_ = lean_st_ref_get(v___y_6045_);
v_traceState_6048_ = lean_ctor_get(v___x_6047_, 4);
lean_inc_ref(v_traceState_6048_);
lean_dec(v___x_6047_);
v_traces_6049_ = lean_ctor_get(v_traceState_6048_, 0);
lean_inc_ref(v_traces_6049_);
lean_dec_ref(v_traceState_6048_);
v___x_6050_ = lean_st_ref_take(v___y_6045_);
v_traceState_6051_ = lean_ctor_get(v___x_6050_, 4);
v_env_6052_ = lean_ctor_get(v___x_6050_, 0);
v_nextMacroScope_6053_ = lean_ctor_get(v___x_6050_, 1);
v_ngen_6054_ = lean_ctor_get(v___x_6050_, 2);
v_auxDeclNGen_6055_ = lean_ctor_get(v___x_6050_, 3);
v_cache_6056_ = lean_ctor_get(v___x_6050_, 5);
v_recordedDeps_6057_ = lean_ctor_get(v___x_6050_, 6);
v_messages_6058_ = lean_ctor_get(v___x_6050_, 7);
v_infoState_6059_ = lean_ctor_get(v___x_6050_, 8);
v_snapshotTasks_6060_ = lean_ctor_get(v___x_6050_, 9);
v_isSharedCheck_6079_ = !lean_is_exclusive(v___x_6050_);
if (v_isSharedCheck_6079_ == 0)
{
v___x_6062_ = v___x_6050_;
v_isShared_6063_ = v_isSharedCheck_6079_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_snapshotTasks_6060_);
lean_inc(v_infoState_6059_);
lean_inc(v_messages_6058_);
lean_inc(v_recordedDeps_6057_);
lean_inc(v_cache_6056_);
lean_inc(v_traceState_6051_);
lean_inc(v_auxDeclNGen_6055_);
lean_inc(v_ngen_6054_);
lean_inc(v_nextMacroScope_6053_);
lean_inc(v_env_6052_);
lean_dec(v___x_6050_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6079_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
uint64_t v_tid_6064_; lean_object* v___x_6066_; uint8_t v_isShared_6067_; uint8_t v_isSharedCheck_6077_; 
v_tid_6064_ = lean_ctor_get_uint64(v_traceState_6051_, sizeof(void*)*1);
v_isSharedCheck_6077_ = !lean_is_exclusive(v_traceState_6051_);
if (v_isSharedCheck_6077_ == 0)
{
lean_object* v_unused_6078_; 
v_unused_6078_ = lean_ctor_get(v_traceState_6051_, 0);
lean_dec(v_unused_6078_);
v___x_6066_ = v_traceState_6051_;
v_isShared_6067_ = v_isSharedCheck_6077_;
goto v_resetjp_6065_;
}
else
{
lean_dec(v_traceState_6051_);
v___x_6066_ = lean_box(0);
v_isShared_6067_ = v_isSharedCheck_6077_;
goto v_resetjp_6065_;
}
v_resetjp_6065_:
{
lean_object* v___x_6068_; lean_object* v___x_6070_; 
v___x_6068_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6067_ == 0)
{
lean_ctor_set(v___x_6066_, 0, v___x_6068_);
v___x_6070_ = v___x_6066_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6076_; 
v_reuseFailAlloc_6076_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6076_, 0, v___x_6068_);
lean_ctor_set_uint64(v_reuseFailAlloc_6076_, sizeof(void*)*1, v_tid_6064_);
v___x_6070_ = v_reuseFailAlloc_6076_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
lean_object* v___x_6072_; 
if (v_isShared_6063_ == 0)
{
lean_ctor_set(v___x_6062_, 4, v___x_6070_);
v___x_6072_ = v___x_6062_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6075_; 
v_reuseFailAlloc_6075_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_env_6052_);
lean_ctor_set(v_reuseFailAlloc_6075_, 1, v_nextMacroScope_6053_);
lean_ctor_set(v_reuseFailAlloc_6075_, 2, v_ngen_6054_);
lean_ctor_set(v_reuseFailAlloc_6075_, 3, v_auxDeclNGen_6055_);
lean_ctor_set(v_reuseFailAlloc_6075_, 4, v___x_6070_);
lean_ctor_set(v_reuseFailAlloc_6075_, 5, v_cache_6056_);
lean_ctor_set(v_reuseFailAlloc_6075_, 6, v_recordedDeps_6057_);
lean_ctor_set(v_reuseFailAlloc_6075_, 7, v_messages_6058_);
lean_ctor_set(v_reuseFailAlloc_6075_, 8, v_infoState_6059_);
lean_ctor_set(v_reuseFailAlloc_6075_, 9, v_snapshotTasks_6060_);
v___x_6072_ = v_reuseFailAlloc_6075_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6073_ = lean_st_ref_put(v___y_6045_, v___x_6072_);
v___x_6074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6074_, 0, v_traces_6049_);
return v___x_6074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6080_, lean_object* v___y_6081_){
_start:
{
lean_object* v_res_6082_; 
v_res_6082_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6080_);
lean_dec(v___y_6080_);
return v_res_6082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_){
_start:
{
lean_object* v___x_6095_; 
v___x_6095_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6093_);
return v___x_6095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_){
_start:
{
lean_object* v_res_6108_; 
v_res_6108_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_);
lean_dec(v___y_6106_);
lean_dec_ref(v___y_6105_);
lean_dec(v___y_6104_);
lean_dec_ref(v___y_6103_);
lean_dec(v___y_6102_);
lean_dec_ref(v___y_6101_);
lean_dec(v___y_6100_);
lean_dec_ref(v___y_6099_);
lean_dec(v___y_6098_);
lean_dec(v___y_6097_);
lean_dec_ref(v___y_6096_);
return v_res_6108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6109_, lean_object* v_opt_6110_){
_start:
{
lean_object* v_name_6111_; lean_object* v_defValue_6112_; lean_object* v_map_6113_; lean_object* v___x_6114_; 
v_name_6111_ = lean_ctor_get(v_opt_6110_, 0);
v_defValue_6112_ = lean_ctor_get(v_opt_6110_, 1);
v_map_6113_ = lean_ctor_get(v_opts_6109_, 0);
v___x_6114_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6113_, v_name_6111_);
if (lean_obj_tag(v___x_6114_) == 0)
{
uint8_t v___x_6115_; 
v___x_6115_ = lean_unbox(v_defValue_6112_);
return v___x_6115_;
}
else
{
lean_object* v_val_6116_; 
v_val_6116_ = lean_ctor_get(v___x_6114_, 0);
lean_inc(v_val_6116_);
lean_dec_ref_known(v___x_6114_, 1);
if (lean_obj_tag(v_val_6116_) == 1)
{
uint8_t v_v_6117_; 
v_v_6117_ = lean_ctor_get_uint8(v_val_6116_, 0);
lean_dec_ref_known(v_val_6116_, 0);
return v_v_6117_;
}
else
{
uint8_t v___x_6118_; 
lean_dec(v_val_6116_);
v___x_6118_ = lean_unbox(v_defValue_6112_);
return v___x_6118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6119_, lean_object* v_opt_6120_){
_start:
{
uint8_t v_res_6121_; lean_object* v_r_6122_; 
v_res_6121_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6119_, v_opt_6120_);
lean_dec_ref(v_opt_6120_);
lean_dec_ref(v_opts_6119_);
v_r_6122_ = lean_box(v_res_6121_);
return v_r_6122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6123_, lean_object* v_msg_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
lean_object* v_ref_6130_; lean_object* v___x_6131_; lean_object* v_a_6132_; lean_object* v___x_6134_; uint8_t v_isShared_6135_; uint8_t v_isSharedCheck_6177_; 
v_ref_6130_ = lean_ctor_get(v___y_6127_, 2);
v___x_6131_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
v_a_6132_ = lean_ctor_get(v___x_6131_, 0);
v_isSharedCheck_6177_ = !lean_is_exclusive(v___x_6131_);
if (v_isSharedCheck_6177_ == 0)
{
v___x_6134_ = v___x_6131_;
v_isShared_6135_ = v_isSharedCheck_6177_;
goto v_resetjp_6133_;
}
else
{
lean_inc(v_a_6132_);
lean_dec(v___x_6131_);
v___x_6134_ = lean_box(0);
v_isShared_6135_ = v_isSharedCheck_6177_;
goto v_resetjp_6133_;
}
v_resetjp_6133_:
{
lean_object* v___x_6136_; lean_object* v_traceState_6137_; lean_object* v_env_6138_; lean_object* v_nextMacroScope_6139_; lean_object* v_ngen_6140_; lean_object* v_auxDeclNGen_6141_; lean_object* v_cache_6142_; lean_object* v_recordedDeps_6143_; lean_object* v_messages_6144_; lean_object* v_infoState_6145_; lean_object* v_snapshotTasks_6146_; lean_object* v___x_6148_; uint8_t v_isShared_6149_; uint8_t v_isSharedCheck_6176_; 
v___x_6136_ = lean_st_ref_take(v___y_6128_);
v_traceState_6137_ = lean_ctor_get(v___x_6136_, 4);
v_env_6138_ = lean_ctor_get(v___x_6136_, 0);
v_nextMacroScope_6139_ = lean_ctor_get(v___x_6136_, 1);
v_ngen_6140_ = lean_ctor_get(v___x_6136_, 2);
v_auxDeclNGen_6141_ = lean_ctor_get(v___x_6136_, 3);
v_cache_6142_ = lean_ctor_get(v___x_6136_, 5);
v_recordedDeps_6143_ = lean_ctor_get(v___x_6136_, 6);
v_messages_6144_ = lean_ctor_get(v___x_6136_, 7);
v_infoState_6145_ = lean_ctor_get(v___x_6136_, 8);
v_snapshotTasks_6146_ = lean_ctor_get(v___x_6136_, 9);
v_isSharedCheck_6176_ = !lean_is_exclusive(v___x_6136_);
if (v_isSharedCheck_6176_ == 0)
{
v___x_6148_ = v___x_6136_;
v_isShared_6149_ = v_isSharedCheck_6176_;
goto v_resetjp_6147_;
}
else
{
lean_inc(v_snapshotTasks_6146_);
lean_inc(v_infoState_6145_);
lean_inc(v_messages_6144_);
lean_inc(v_recordedDeps_6143_);
lean_inc(v_cache_6142_);
lean_inc(v_traceState_6137_);
lean_inc(v_auxDeclNGen_6141_);
lean_inc(v_ngen_6140_);
lean_inc(v_nextMacroScope_6139_);
lean_inc(v_env_6138_);
lean_dec(v___x_6136_);
v___x_6148_ = lean_box(0);
v_isShared_6149_ = v_isSharedCheck_6176_;
goto v_resetjp_6147_;
}
v_resetjp_6147_:
{
uint64_t v_tid_6150_; lean_object* v_traces_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6175_; 
v_tid_6150_ = lean_ctor_get_uint64(v_traceState_6137_, sizeof(void*)*1);
v_traces_6151_ = lean_ctor_get(v_traceState_6137_, 0);
v_isSharedCheck_6175_ = !lean_is_exclusive(v_traceState_6137_);
if (v_isSharedCheck_6175_ == 0)
{
v___x_6153_ = v_traceState_6137_;
v_isShared_6154_ = v_isSharedCheck_6175_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_traces_6151_);
lean_dec(v_traceState_6137_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6175_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
lean_object* v___x_6155_; lean_object* v___x_6156_; double v___x_6157_; uint8_t v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6166_; 
v___x_6155_ = lean_box(0);
v___x_6156_ = lean_box(0);
v___x_6157_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6158_ = 0;
v___x_6159_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6160_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6160_, 0, v_cls_6123_);
lean_ctor_set(v___x_6160_, 1, v___x_6156_);
lean_ctor_set(v___x_6160_, 2, v___x_6159_);
lean_ctor_set_float(v___x_6160_, sizeof(void*)*3, v___x_6157_);
lean_ctor_set_float(v___x_6160_, sizeof(void*)*3 + 8, v___x_6157_);
lean_ctor_set_uint8(v___x_6160_, sizeof(void*)*3 + 16, v___x_6158_);
v___x_6161_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6162_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6160_);
lean_ctor_set(v___x_6162_, 1, v_a_6132_);
lean_ctor_set(v___x_6162_, 2, v___x_6161_);
lean_inc(v_ref_6130_);
v___x_6163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6163_, 0, v_ref_6130_);
lean_ctor_set(v___x_6163_, 1, v___x_6162_);
v___x_6164_ = l_Lean_PersistentArray_push___redArg(v_traces_6151_, v___x_6163_);
if (v_isShared_6154_ == 0)
{
lean_ctor_set(v___x_6153_, 0, v___x_6164_);
v___x_6166_ = v___x_6153_;
goto v_reusejp_6165_;
}
else
{
lean_object* v_reuseFailAlloc_6174_; 
v_reuseFailAlloc_6174_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6174_, 0, v___x_6164_);
lean_ctor_set_uint64(v_reuseFailAlloc_6174_, sizeof(void*)*1, v_tid_6150_);
v___x_6166_ = v_reuseFailAlloc_6174_;
goto v_reusejp_6165_;
}
v_reusejp_6165_:
{
lean_object* v___x_6168_; 
if (v_isShared_6149_ == 0)
{
lean_ctor_set(v___x_6148_, 4, v___x_6166_);
v___x_6168_ = v___x_6148_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6173_; 
v_reuseFailAlloc_6173_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6173_, 0, v_env_6138_);
lean_ctor_set(v_reuseFailAlloc_6173_, 1, v_nextMacroScope_6139_);
lean_ctor_set(v_reuseFailAlloc_6173_, 2, v_ngen_6140_);
lean_ctor_set(v_reuseFailAlloc_6173_, 3, v_auxDeclNGen_6141_);
lean_ctor_set(v_reuseFailAlloc_6173_, 4, v___x_6166_);
lean_ctor_set(v_reuseFailAlloc_6173_, 5, v_cache_6142_);
lean_ctor_set(v_reuseFailAlloc_6173_, 6, v_recordedDeps_6143_);
lean_ctor_set(v_reuseFailAlloc_6173_, 7, v_messages_6144_);
lean_ctor_set(v_reuseFailAlloc_6173_, 8, v_infoState_6145_);
lean_ctor_set(v_reuseFailAlloc_6173_, 9, v_snapshotTasks_6146_);
v___x_6168_ = v_reuseFailAlloc_6173_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
lean_object* v___x_6169_; lean_object* v___x_6171_; 
v___x_6169_ = lean_st_ref_put(v___y_6128_, v___x_6168_);
if (v_isShared_6135_ == 0)
{
lean_ctor_set(v___x_6134_, 0, v___x_6155_);
v___x_6171_ = v___x_6134_;
goto v_reusejp_6170_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v___x_6155_);
v___x_6171_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6170_;
}
v_reusejp_6170_:
{
return v___x_6171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6178_, lean_object* v_msg_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_){
_start:
{
lean_object* v_res_6185_; 
v_res_6185_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6178_, v_msg_6179_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_);
lean_dec(v___y_6183_);
lean_dec_ref(v___y_6182_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
return v_res_6185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6186_){
_start:
{
if (lean_obj_tag(v_e_6186_) == 0)
{
uint8_t v___x_6187_; 
v___x_6187_ = 2;
return v___x_6187_;
}
else
{
lean_object* v_a_6188_; uint8_t v___x_6189_; 
v_a_6188_ = lean_ctor_get(v_e_6186_, 0);
v___x_6189_ = lean_unbox(v_a_6188_);
if (v___x_6189_ == 0)
{
uint8_t v___x_6190_; 
v___x_6190_ = 1;
return v___x_6190_;
}
else
{
uint8_t v___x_6191_; 
v___x_6191_ = 0;
return v___x_6191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6192_){
_start:
{
uint8_t v_res_6193_; lean_object* v_r_6194_; 
v_res_6193_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6192_);
lean_dec_ref(v_e_6192_);
v_r_6194_ = lean_box(v_res_6193_);
return v_r_6194_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6195_){
_start:
{
if (lean_obj_tag(v_x_6195_) == 0)
{
lean_object* v_a_6197_; lean_object* v___x_6199_; uint8_t v_isShared_6200_; uint8_t v_isSharedCheck_6204_; 
v_a_6197_ = lean_ctor_get(v_x_6195_, 0);
v_isSharedCheck_6204_ = !lean_is_exclusive(v_x_6195_);
if (v_isSharedCheck_6204_ == 0)
{
v___x_6199_ = v_x_6195_;
v_isShared_6200_ = v_isSharedCheck_6204_;
goto v_resetjp_6198_;
}
else
{
lean_inc(v_a_6197_);
lean_dec(v_x_6195_);
v___x_6199_ = lean_box(0);
v_isShared_6200_ = v_isSharedCheck_6204_;
goto v_resetjp_6198_;
}
v_resetjp_6198_:
{
lean_object* v___x_6202_; 
if (v_isShared_6200_ == 0)
{
lean_ctor_set_tag(v___x_6199_, 1);
v___x_6202_ = v___x_6199_;
goto v_reusejp_6201_;
}
else
{
lean_object* v_reuseFailAlloc_6203_; 
v_reuseFailAlloc_6203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6203_, 0, v_a_6197_);
v___x_6202_ = v_reuseFailAlloc_6203_;
goto v_reusejp_6201_;
}
v_reusejp_6201_:
{
return v___x_6202_;
}
}
}
else
{
lean_object* v_a_6205_; lean_object* v___x_6207_; uint8_t v_isShared_6208_; uint8_t v_isSharedCheck_6212_; 
v_a_6205_ = lean_ctor_get(v_x_6195_, 0);
v_isSharedCheck_6212_ = !lean_is_exclusive(v_x_6195_);
if (v_isSharedCheck_6212_ == 0)
{
v___x_6207_ = v_x_6195_;
v_isShared_6208_ = v_isSharedCheck_6212_;
goto v_resetjp_6206_;
}
else
{
lean_inc(v_a_6205_);
lean_dec(v_x_6195_);
v___x_6207_ = lean_box(0);
v_isShared_6208_ = v_isSharedCheck_6212_;
goto v_resetjp_6206_;
}
v_resetjp_6206_:
{
lean_object* v___x_6210_; 
if (v_isShared_6208_ == 0)
{
lean_ctor_set_tag(v___x_6207_, 0);
v___x_6210_ = v___x_6207_;
goto v_reusejp_6209_;
}
else
{
lean_object* v_reuseFailAlloc_6211_; 
v_reuseFailAlloc_6211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6211_, 0, v_a_6205_);
v___x_6210_ = v_reuseFailAlloc_6211_;
goto v_reusejp_6209_;
}
v_reusejp_6209_:
{
return v___x_6210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6213_, lean_object* v___y_6214_){
_start:
{
lean_object* v_res_6215_; 
v_res_6215_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6213_);
return v_res_6215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6216_, lean_object* v_opt_6217_){
_start:
{
lean_object* v_name_6218_; lean_object* v_defValue_6219_; lean_object* v_map_6220_; lean_object* v___x_6221_; 
v_name_6218_ = lean_ctor_get(v_opt_6217_, 0);
v_defValue_6219_ = lean_ctor_get(v_opt_6217_, 1);
v_map_6220_ = lean_ctor_get(v_opts_6216_, 0);
v___x_6221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6220_, v_name_6218_);
if (lean_obj_tag(v___x_6221_) == 0)
{
lean_inc(v_defValue_6219_);
return v_defValue_6219_;
}
else
{
lean_object* v_val_6222_; 
v_val_6222_ = lean_ctor_get(v___x_6221_, 0);
lean_inc(v_val_6222_);
lean_dec_ref_known(v___x_6221_, 1);
if (lean_obj_tag(v_val_6222_) == 3)
{
lean_object* v_v_6223_; 
v_v_6223_ = lean_ctor_get(v_val_6222_, 0);
lean_inc(v_v_6223_);
lean_dec_ref_known(v_val_6222_, 1);
return v_v_6223_;
}
else
{
lean_dec(v_val_6222_);
lean_inc(v_defValue_6219_);
return v_defValue_6219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6224_, lean_object* v_opt_6225_){
_start:
{
lean_object* v_res_6226_; 
v_res_6226_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6224_, v_opt_6225_);
lean_dec_ref(v_opt_6225_);
lean_dec_ref(v_opts_6224_);
return v_res_6226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6227_, size_t v_i_6228_, lean_object* v_bs_6229_){
_start:
{
uint8_t v___x_6230_; 
v___x_6230_ = lean_usize_dec_lt(v_i_6228_, v_sz_6227_);
if (v___x_6230_ == 0)
{
return v_bs_6229_;
}
else
{
lean_object* v_v_6231_; lean_object* v_msg_6232_; lean_object* v___x_6233_; lean_object* v_bs_x27_6234_; size_t v___x_6235_; size_t v___x_6236_; lean_object* v___x_6237_; 
v_v_6231_ = lean_array_uget_borrowed(v_bs_6229_, v_i_6228_);
v_msg_6232_ = lean_ctor_get(v_v_6231_, 1);
lean_inc_ref(v_msg_6232_);
v___x_6233_ = lean_unsigned_to_nat(0u);
v_bs_x27_6234_ = lean_array_uset(v_bs_6229_, v_i_6228_, v___x_6233_);
v___x_6235_ = ((size_t)1ULL);
v___x_6236_ = lean_usize_add(v_i_6228_, v___x_6235_);
v___x_6237_ = lean_array_uset(v_bs_x27_6234_, v_i_6228_, v_msg_6232_);
v_i_6228_ = v___x_6236_;
v_bs_6229_ = v___x_6237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6239_, lean_object* v_i_6240_, lean_object* v_bs_6241_){
_start:
{
size_t v_sz_boxed_6242_; size_t v_i_boxed_6243_; lean_object* v_res_6244_; 
v_sz_boxed_6242_ = lean_unbox_usize(v_sz_6239_);
lean_dec(v_sz_6239_);
v_i_boxed_6243_ = lean_unbox_usize(v_i_6240_);
lean_dec(v_i_6240_);
v_res_6244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6242_, v_i_boxed_6243_, v_bs_6241_);
return v_res_6244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6245_, lean_object* v_data_6246_, lean_object* v_ref_6247_, lean_object* v_msg_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_){
_start:
{
lean_object* v_toCold_6254_; lean_object* v_currRecDepth_6255_; lean_object* v_ref_6256_; uint16_t v_optionFlags_6257_; uint8_t v_suppressElabErrors_6258_; uint8_t v_isRecordingDeps_6259_; lean_object* v_ref_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v_traceState_6263_; lean_object* v_traces_6264_; lean_object* v___x_6265_; size_t v_sz_6266_; size_t v___x_6267_; lean_object* v___x_6268_; lean_object* v_msg_6269_; lean_object* v___x_6270_; lean_object* v_a_6271_; lean_object* v___x_6273_; uint8_t v_isShared_6274_; uint8_t v_isSharedCheck_6309_; 
v_toCold_6254_ = lean_ctor_get(v___y_6251_, 0);
v_currRecDepth_6255_ = lean_ctor_get(v___y_6251_, 1);
v_ref_6256_ = lean_ctor_get(v___y_6251_, 2);
v_optionFlags_6257_ = lean_ctor_get_uint16(v___y_6251_, sizeof(void*)*3);
v_suppressElabErrors_6258_ = lean_ctor_get_uint8(v___y_6251_, sizeof(void*)*3 + 2);
v_isRecordingDeps_6259_ = lean_ctor_get_uint8(v___y_6251_, sizeof(void*)*3 + 3);
v_ref_6260_ = l_Lean_replaceRef(v_ref_6247_, v_ref_6256_);
lean_inc(v_currRecDepth_6255_);
lean_inc_ref(v_toCold_6254_);
v___x_6261_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_6261_, 0, v_toCold_6254_);
lean_ctor_set(v___x_6261_, 1, v_currRecDepth_6255_);
lean_ctor_set(v___x_6261_, 2, v_ref_6260_);
lean_ctor_set_uint16(v___x_6261_, sizeof(void*)*3, v_optionFlags_6257_);
lean_ctor_set_uint8(v___x_6261_, sizeof(void*)*3 + 2, v_suppressElabErrors_6258_);
lean_ctor_set_uint8(v___x_6261_, sizeof(void*)*3 + 3, v_isRecordingDeps_6259_);
v___x_6262_ = lean_st_ref_get(v___y_6252_);
v_traceState_6263_ = lean_ctor_get(v___x_6262_, 4);
lean_inc_ref(v_traceState_6263_);
lean_dec(v___x_6262_);
v_traces_6264_ = lean_ctor_get(v_traceState_6263_, 0);
lean_inc_ref(v_traces_6264_);
lean_dec_ref(v_traceState_6263_);
v___x_6265_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6264_);
lean_dec_ref(v_traces_6264_);
v_sz_6266_ = lean_array_size(v___x_6265_);
v___x_6267_ = ((size_t)0ULL);
v___x_6268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6266_, v___x_6267_, v___x_6265_);
v_msg_6269_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6269_, 0, v_data_6246_);
lean_ctor_set(v_msg_6269_, 1, v_msg_6248_);
lean_ctor_set(v_msg_6269_, 2, v___x_6268_);
v___x_6270_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6269_, v___y_6249_, v___y_6250_, v___x_6261_, v___y_6252_);
lean_dec_ref_known(v___x_6261_, 3);
v_a_6271_ = lean_ctor_get(v___x_6270_, 0);
v_isSharedCheck_6309_ = !lean_is_exclusive(v___x_6270_);
if (v_isSharedCheck_6309_ == 0)
{
v___x_6273_ = v___x_6270_;
v_isShared_6274_ = v_isSharedCheck_6309_;
goto v_resetjp_6272_;
}
else
{
lean_inc(v_a_6271_);
lean_dec(v___x_6270_);
v___x_6273_ = lean_box(0);
v_isShared_6274_ = v_isSharedCheck_6309_;
goto v_resetjp_6272_;
}
v_resetjp_6272_:
{
lean_object* v___x_6275_; lean_object* v_traceState_6276_; lean_object* v_env_6277_; lean_object* v_nextMacroScope_6278_; lean_object* v_ngen_6279_; lean_object* v_auxDeclNGen_6280_; lean_object* v_cache_6281_; lean_object* v_recordedDeps_6282_; lean_object* v_messages_6283_; lean_object* v_infoState_6284_; lean_object* v_snapshotTasks_6285_; lean_object* v___x_6287_; uint8_t v_isShared_6288_; uint8_t v_isSharedCheck_6308_; 
v___x_6275_ = lean_st_ref_take(v___y_6252_);
v_traceState_6276_ = lean_ctor_get(v___x_6275_, 4);
v_env_6277_ = lean_ctor_get(v___x_6275_, 0);
v_nextMacroScope_6278_ = lean_ctor_get(v___x_6275_, 1);
v_ngen_6279_ = lean_ctor_get(v___x_6275_, 2);
v_auxDeclNGen_6280_ = lean_ctor_get(v___x_6275_, 3);
v_cache_6281_ = lean_ctor_get(v___x_6275_, 5);
v_recordedDeps_6282_ = lean_ctor_get(v___x_6275_, 6);
v_messages_6283_ = lean_ctor_get(v___x_6275_, 7);
v_infoState_6284_ = lean_ctor_get(v___x_6275_, 8);
v_snapshotTasks_6285_ = lean_ctor_get(v___x_6275_, 9);
v_isSharedCheck_6308_ = !lean_is_exclusive(v___x_6275_);
if (v_isSharedCheck_6308_ == 0)
{
v___x_6287_ = v___x_6275_;
v_isShared_6288_ = v_isSharedCheck_6308_;
goto v_resetjp_6286_;
}
else
{
lean_inc(v_snapshotTasks_6285_);
lean_inc(v_infoState_6284_);
lean_inc(v_messages_6283_);
lean_inc(v_recordedDeps_6282_);
lean_inc(v_cache_6281_);
lean_inc(v_traceState_6276_);
lean_inc(v_auxDeclNGen_6280_);
lean_inc(v_ngen_6279_);
lean_inc(v_nextMacroScope_6278_);
lean_inc(v_env_6277_);
lean_dec(v___x_6275_);
v___x_6287_ = lean_box(0);
v_isShared_6288_ = v_isSharedCheck_6308_;
goto v_resetjp_6286_;
}
v_resetjp_6286_:
{
uint64_t v_tid_6289_; lean_object* v___x_6291_; uint8_t v_isShared_6292_; uint8_t v_isSharedCheck_6306_; 
v_tid_6289_ = lean_ctor_get_uint64(v_traceState_6276_, sizeof(void*)*1);
v_isSharedCheck_6306_ = !lean_is_exclusive(v_traceState_6276_);
if (v_isSharedCheck_6306_ == 0)
{
lean_object* v_unused_6307_; 
v_unused_6307_ = lean_ctor_get(v_traceState_6276_, 0);
lean_dec(v_unused_6307_);
v___x_6291_ = v_traceState_6276_;
v_isShared_6292_ = v_isSharedCheck_6306_;
goto v_resetjp_6290_;
}
else
{
lean_dec(v_traceState_6276_);
v___x_6291_ = lean_box(0);
v_isShared_6292_ = v_isSharedCheck_6306_;
goto v_resetjp_6290_;
}
v_resetjp_6290_:
{
lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6297_; 
v___x_6293_ = lean_box(0);
v___x_6294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6294_, 0, v_ref_6247_);
lean_ctor_set(v___x_6294_, 1, v_a_6271_);
v___x_6295_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6245_, v___x_6294_);
if (v_isShared_6292_ == 0)
{
lean_ctor_set(v___x_6291_, 0, v___x_6295_);
v___x_6297_ = v___x_6291_;
goto v_reusejp_6296_;
}
else
{
lean_object* v_reuseFailAlloc_6305_; 
v_reuseFailAlloc_6305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6305_, 0, v___x_6295_);
lean_ctor_set_uint64(v_reuseFailAlloc_6305_, sizeof(void*)*1, v_tid_6289_);
v___x_6297_ = v_reuseFailAlloc_6305_;
goto v_reusejp_6296_;
}
v_reusejp_6296_:
{
lean_object* v___x_6299_; 
if (v_isShared_6288_ == 0)
{
lean_ctor_set(v___x_6287_, 4, v___x_6297_);
v___x_6299_ = v___x_6287_;
goto v_reusejp_6298_;
}
else
{
lean_object* v_reuseFailAlloc_6304_; 
v_reuseFailAlloc_6304_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6304_, 0, v_env_6277_);
lean_ctor_set(v_reuseFailAlloc_6304_, 1, v_nextMacroScope_6278_);
lean_ctor_set(v_reuseFailAlloc_6304_, 2, v_ngen_6279_);
lean_ctor_set(v_reuseFailAlloc_6304_, 3, v_auxDeclNGen_6280_);
lean_ctor_set(v_reuseFailAlloc_6304_, 4, v___x_6297_);
lean_ctor_set(v_reuseFailAlloc_6304_, 5, v_cache_6281_);
lean_ctor_set(v_reuseFailAlloc_6304_, 6, v_recordedDeps_6282_);
lean_ctor_set(v_reuseFailAlloc_6304_, 7, v_messages_6283_);
lean_ctor_set(v_reuseFailAlloc_6304_, 8, v_infoState_6284_);
lean_ctor_set(v_reuseFailAlloc_6304_, 9, v_snapshotTasks_6285_);
v___x_6299_ = v_reuseFailAlloc_6304_;
goto v_reusejp_6298_;
}
v_reusejp_6298_:
{
lean_object* v___x_6300_; lean_object* v___x_6302_; 
v___x_6300_ = lean_st_ref_put(v___y_6252_, v___x_6299_);
if (v_isShared_6274_ == 0)
{
lean_ctor_set(v___x_6273_, 0, v___x_6293_);
v___x_6302_ = v___x_6273_;
goto v_reusejp_6301_;
}
else
{
lean_object* v_reuseFailAlloc_6303_; 
v_reuseFailAlloc_6303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6303_, 0, v___x_6293_);
v___x_6302_ = v_reuseFailAlloc_6303_;
goto v_reusejp_6301_;
}
v_reusejp_6301_:
{
return v___x_6302_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6310_, lean_object* v_data_6311_, lean_object* v_ref_6312_, lean_object* v_msg_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_){
_start:
{
lean_object* v_res_6319_; 
v_res_6319_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6310_, v_data_6311_, v_ref_6312_, v_msg_6313_, v___y_6314_, v___y_6315_, v___y_6316_, v___y_6317_);
lean_dec(v___y_6317_);
lean_dec_ref(v___y_6316_);
lean_dec(v___y_6315_);
lean_dec_ref(v___y_6314_);
return v_res_6319_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6321_; lean_object* v___x_6322_; 
v___x_6321_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6322_ = l_Lean_stringToMessageData(v___x_6321_);
return v___x_6322_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6323_; double v___x_6324_; 
v___x_6323_ = lean_unsigned_to_nat(1000u);
v___x_6324_ = lean_float_of_nat(v___x_6323_);
return v___x_6324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6325_, uint8_t v_collapsed_6326_, lean_object* v_tag_6327_, lean_object* v_opts_6328_, uint8_t v_clsEnabled_6329_, lean_object* v_oldTraces_6330_, lean_object* v_msg_6331_, lean_object* v_resStartStop_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_){
_start:
{
lean_object* v_fst_6345_; lean_object* v_snd_6346_; lean_object* v___y_6348_; lean_object* v___y_6349_; lean_object* v_data_6350_; lean_object* v_fst_6361_; lean_object* v_snd_6362_; lean_object* v___x_6363_; uint8_t v___x_6364_; lean_object* v___y_6366_; lean_object* v_a_6367_; uint8_t v___y_6382_; double v___y_6414_; 
v_fst_6345_ = lean_ctor_get(v_resStartStop_6332_, 0);
lean_inc(v_fst_6345_);
v_snd_6346_ = lean_ctor_get(v_resStartStop_6332_, 1);
lean_inc(v_snd_6346_);
lean_dec_ref(v_resStartStop_6332_);
v_fst_6361_ = lean_ctor_get(v_snd_6346_, 0);
lean_inc(v_fst_6361_);
v_snd_6362_ = lean_ctor_get(v_snd_6346_, 1);
lean_inc(v_snd_6362_);
lean_dec(v_snd_6346_);
v___x_6363_ = l_Lean_trace_profiler;
v___x_6364_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6328_, v___x_6363_);
if (v___x_6364_ == 0)
{
v___y_6382_ = v___x_6364_;
goto v___jp_6381_;
}
else
{
lean_object* v___x_6419_; uint8_t v___x_6420_; 
v___x_6419_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6420_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6328_, v___x_6419_);
if (v___x_6420_ == 0)
{
lean_object* v___x_6421_; lean_object* v___x_6422_; double v___x_6423_; double v___x_6424_; double v___x_6425_; 
v___x_6421_ = l_Lean_trace_profiler_threshold;
v___x_6422_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6328_, v___x_6421_);
v___x_6423_ = lean_float_of_nat(v___x_6422_);
v___x_6424_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6425_ = lean_float_div(v___x_6423_, v___x_6424_);
v___y_6414_ = v___x_6425_;
goto v___jp_6413_;
}
else
{
lean_object* v___x_6426_; lean_object* v___x_6427_; double v___x_6428_; 
v___x_6426_ = l_Lean_trace_profiler_threshold;
v___x_6427_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6328_, v___x_6426_);
v___x_6428_ = lean_float_of_nat(v___x_6427_);
v___y_6414_ = v___x_6428_;
goto v___jp_6413_;
}
}
v___jp_6347_:
{
lean_object* v___x_6351_; 
lean_inc(v___y_6349_);
v___x_6351_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6330_, v_data_6350_, v___y_6349_, v___y_6348_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_);
if (lean_obj_tag(v___x_6351_) == 0)
{
lean_object* v___x_6352_; 
lean_dec_ref_known(v___x_6351_, 1);
v___x_6352_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6345_);
return v___x_6352_;
}
else
{
lean_object* v_a_6353_; lean_object* v___x_6355_; uint8_t v_isShared_6356_; uint8_t v_isSharedCheck_6360_; 
lean_dec(v_fst_6345_);
v_a_6353_ = lean_ctor_get(v___x_6351_, 0);
v_isSharedCheck_6360_ = !lean_is_exclusive(v___x_6351_);
if (v_isSharedCheck_6360_ == 0)
{
v___x_6355_ = v___x_6351_;
v_isShared_6356_ = v_isSharedCheck_6360_;
goto v_resetjp_6354_;
}
else
{
lean_inc(v_a_6353_);
lean_dec(v___x_6351_);
v___x_6355_ = lean_box(0);
v_isShared_6356_ = v_isSharedCheck_6360_;
goto v_resetjp_6354_;
}
v_resetjp_6354_:
{
lean_object* v___x_6358_; 
if (v_isShared_6356_ == 0)
{
v___x_6358_ = v___x_6355_;
goto v_reusejp_6357_;
}
else
{
lean_object* v_reuseFailAlloc_6359_; 
v_reuseFailAlloc_6359_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_6365_:
{
uint8_t v_result_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; double v___x_6371_; lean_object* v_data_6372_; 
v_result_6368_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6345_);
v___x_6369_ = lean_box(v_result_6368_);
v___x_6370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6370_, 0, v___x_6369_);
v___x_6371_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6327_);
lean_inc_ref(v___x_6370_);
lean_inc(v_cls_6325_);
v_data_6372_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6372_, 0, v_cls_6325_);
lean_ctor_set(v_data_6372_, 1, v___x_6370_);
lean_ctor_set(v_data_6372_, 2, v_tag_6327_);
lean_ctor_set_float(v_data_6372_, sizeof(void*)*3, v___x_6371_);
lean_ctor_set_float(v_data_6372_, sizeof(void*)*3 + 8, v___x_6371_);
lean_ctor_set_uint8(v_data_6372_, sizeof(void*)*3 + 16, v_collapsed_6326_);
if (v___x_6364_ == 0)
{
lean_dec_ref_known(v___x_6370_, 1);
lean_dec(v_snd_6362_);
lean_dec(v_fst_6361_);
lean_dec_ref(v_tag_6327_);
lean_dec(v_cls_6325_);
v___y_6348_ = v_a_6367_;
v___y_6349_ = v___y_6366_;
v_data_6350_ = v_data_6372_;
goto v___jp_6347_;
}
else
{
lean_object* v_data_6373_; double v___x_6374_; double v___x_6375_; 
lean_dec_ref_known(v_data_6372_, 3);
v_data_6373_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6373_, 0, v_cls_6325_);
lean_ctor_set(v_data_6373_, 1, v___x_6370_);
lean_ctor_set(v_data_6373_, 2, v_tag_6327_);
v___x_6374_ = lean_unbox_float(v_fst_6361_);
lean_dec(v_fst_6361_);
lean_ctor_set_float(v_data_6373_, sizeof(void*)*3, v___x_6374_);
v___x_6375_ = lean_unbox_float(v_snd_6362_);
lean_dec(v_snd_6362_);
lean_ctor_set_float(v_data_6373_, sizeof(void*)*3 + 8, v___x_6375_);
lean_ctor_set_uint8(v_data_6373_, sizeof(void*)*3 + 16, v_collapsed_6326_);
v___y_6348_ = v_a_6367_;
v___y_6349_ = v___y_6366_;
v_data_6350_ = v_data_6373_;
goto v___jp_6347_;
}
}
v___jp_6376_:
{
lean_object* v_ref_6377_; lean_object* v___x_6378_; 
v_ref_6377_ = lean_ctor_get(v___y_6342_, 2);
lean_inc(v___y_6343_);
lean_inc_ref(v___y_6342_);
lean_inc(v___y_6341_);
lean_inc_ref(v___y_6340_);
lean_inc(v___y_6339_);
lean_inc_ref(v___y_6338_);
lean_inc(v___y_6337_);
lean_inc_ref(v___y_6336_);
lean_inc(v___y_6335_);
lean_inc(v___y_6334_);
lean_inc_ref(v___y_6333_);
lean_inc(v_fst_6345_);
v___x_6378_ = lean_apply_13(v_msg_6331_, v_fst_6345_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, lean_box(0));
if (lean_obj_tag(v___x_6378_) == 0)
{
lean_object* v_a_6379_; 
v_a_6379_ = lean_ctor_get(v___x_6378_, 0);
lean_inc(v_a_6379_);
lean_dec_ref_known(v___x_6378_, 1);
v___y_6366_ = v_ref_6377_;
v_a_6367_ = v_a_6379_;
goto v___jp_6365_;
}
else
{
lean_object* v___x_6380_; 
lean_dec_ref_known(v___x_6378_, 1);
v___x_6380_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6366_ = v_ref_6377_;
v_a_6367_ = v___x_6380_;
goto v___jp_6365_;
}
}
v___jp_6381_:
{
if (v_clsEnabled_6329_ == 0)
{
if (v___y_6382_ == 0)
{
lean_object* v___x_6383_; lean_object* v_traceState_6384_; lean_object* v_env_6385_; lean_object* v_nextMacroScope_6386_; lean_object* v_ngen_6387_; lean_object* v_auxDeclNGen_6388_; lean_object* v_cache_6389_; lean_object* v_recordedDeps_6390_; lean_object* v_messages_6391_; lean_object* v_infoState_6392_; lean_object* v_snapshotTasks_6393_; lean_object* v___x_6395_; uint8_t v_isShared_6396_; uint8_t v_isSharedCheck_6412_; 
lean_dec(v_snd_6362_);
lean_dec(v_fst_6361_);
lean_dec_ref(v_msg_6331_);
lean_dec_ref(v_tag_6327_);
lean_dec(v_cls_6325_);
v___x_6383_ = lean_st_ref_take(v___y_6343_);
v_traceState_6384_ = lean_ctor_get(v___x_6383_, 4);
v_env_6385_ = lean_ctor_get(v___x_6383_, 0);
v_nextMacroScope_6386_ = lean_ctor_get(v___x_6383_, 1);
v_ngen_6387_ = lean_ctor_get(v___x_6383_, 2);
v_auxDeclNGen_6388_ = lean_ctor_get(v___x_6383_, 3);
v_cache_6389_ = lean_ctor_get(v___x_6383_, 5);
v_recordedDeps_6390_ = lean_ctor_get(v___x_6383_, 6);
v_messages_6391_ = lean_ctor_get(v___x_6383_, 7);
v_infoState_6392_ = lean_ctor_get(v___x_6383_, 8);
v_snapshotTasks_6393_ = lean_ctor_get(v___x_6383_, 9);
v_isSharedCheck_6412_ = !lean_is_exclusive(v___x_6383_);
if (v_isSharedCheck_6412_ == 0)
{
v___x_6395_ = v___x_6383_;
v_isShared_6396_ = v_isSharedCheck_6412_;
goto v_resetjp_6394_;
}
else
{
lean_inc(v_snapshotTasks_6393_);
lean_inc(v_infoState_6392_);
lean_inc(v_messages_6391_);
lean_inc(v_recordedDeps_6390_);
lean_inc(v_cache_6389_);
lean_inc(v_traceState_6384_);
lean_inc(v_auxDeclNGen_6388_);
lean_inc(v_ngen_6387_);
lean_inc(v_nextMacroScope_6386_);
lean_inc(v_env_6385_);
lean_dec(v___x_6383_);
v___x_6395_ = lean_box(0);
v_isShared_6396_ = v_isSharedCheck_6412_;
goto v_resetjp_6394_;
}
v_resetjp_6394_:
{
uint64_t v_tid_6397_; lean_object* v_traces_6398_; lean_object* v___x_6400_; uint8_t v_isShared_6401_; uint8_t v_isSharedCheck_6411_; 
v_tid_6397_ = lean_ctor_get_uint64(v_traceState_6384_, sizeof(void*)*1);
v_traces_6398_ = lean_ctor_get(v_traceState_6384_, 0);
v_isSharedCheck_6411_ = !lean_is_exclusive(v_traceState_6384_);
if (v_isSharedCheck_6411_ == 0)
{
v___x_6400_ = v_traceState_6384_;
v_isShared_6401_ = v_isSharedCheck_6411_;
goto v_resetjp_6399_;
}
else
{
lean_inc(v_traces_6398_);
lean_dec(v_traceState_6384_);
v___x_6400_ = lean_box(0);
v_isShared_6401_ = v_isSharedCheck_6411_;
goto v_resetjp_6399_;
}
v_resetjp_6399_:
{
lean_object* v___x_6402_; lean_object* v___x_6404_; 
v___x_6402_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6330_, v_traces_6398_);
lean_dec_ref(v_traces_6398_);
if (v_isShared_6401_ == 0)
{
lean_ctor_set(v___x_6400_, 0, v___x_6402_);
v___x_6404_ = v___x_6400_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6410_; 
v_reuseFailAlloc_6410_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6410_, 0, v___x_6402_);
lean_ctor_set_uint64(v_reuseFailAlloc_6410_, sizeof(void*)*1, v_tid_6397_);
v___x_6404_ = v_reuseFailAlloc_6410_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
lean_object* v___x_6406_; 
if (v_isShared_6396_ == 0)
{
lean_ctor_set(v___x_6395_, 4, v___x_6404_);
v___x_6406_ = v___x_6395_;
goto v_reusejp_6405_;
}
else
{
lean_object* v_reuseFailAlloc_6409_; 
v_reuseFailAlloc_6409_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6409_, 0, v_env_6385_);
lean_ctor_set(v_reuseFailAlloc_6409_, 1, v_nextMacroScope_6386_);
lean_ctor_set(v_reuseFailAlloc_6409_, 2, v_ngen_6387_);
lean_ctor_set(v_reuseFailAlloc_6409_, 3, v_auxDeclNGen_6388_);
lean_ctor_set(v_reuseFailAlloc_6409_, 4, v___x_6404_);
lean_ctor_set(v_reuseFailAlloc_6409_, 5, v_cache_6389_);
lean_ctor_set(v_reuseFailAlloc_6409_, 6, v_recordedDeps_6390_);
lean_ctor_set(v_reuseFailAlloc_6409_, 7, v_messages_6391_);
lean_ctor_set(v_reuseFailAlloc_6409_, 8, v_infoState_6392_);
lean_ctor_set(v_reuseFailAlloc_6409_, 9, v_snapshotTasks_6393_);
v___x_6406_ = v_reuseFailAlloc_6409_;
goto v_reusejp_6405_;
}
v_reusejp_6405_:
{
lean_object* v___x_6407_; lean_object* v___x_6408_; 
v___x_6407_ = lean_st_ref_put(v___y_6343_, v___x_6406_);
v___x_6408_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6345_);
return v___x_6408_;
}
}
}
}
}
else
{
goto v___jp_6376_;
}
}
else
{
goto v___jp_6376_;
}
}
v___jp_6413_:
{
double v___x_6415_; double v___x_6416_; double v___x_6417_; uint8_t v___x_6418_; 
v___x_6415_ = lean_unbox_float(v_snd_6362_);
v___x_6416_ = lean_unbox_float(v_fst_6361_);
v___x_6417_ = lean_float_sub(v___x_6415_, v___x_6416_);
v___x_6418_ = lean_float_decLt(v___y_6414_, v___x_6417_);
v___y_6382_ = v___x_6418_;
goto v___jp_6381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6429_ = _args[0];
lean_object* v_collapsed_6430_ = _args[1];
lean_object* v_tag_6431_ = _args[2];
lean_object* v_opts_6432_ = _args[3];
lean_object* v_clsEnabled_6433_ = _args[4];
lean_object* v_oldTraces_6434_ = _args[5];
lean_object* v_msg_6435_ = _args[6];
lean_object* v_resStartStop_6436_ = _args[7];
lean_object* v___y_6437_ = _args[8];
lean_object* v___y_6438_ = _args[9];
lean_object* v___y_6439_ = _args[10];
lean_object* v___y_6440_ = _args[11];
lean_object* v___y_6441_ = _args[12];
lean_object* v___y_6442_ = _args[13];
lean_object* v___y_6443_ = _args[14];
lean_object* v___y_6444_ = _args[15];
lean_object* v___y_6445_ = _args[16];
lean_object* v___y_6446_ = _args[17];
lean_object* v___y_6447_ = _args[18];
lean_object* v___y_6448_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6449_; uint8_t v_clsEnabled_boxed_6450_; lean_object* v_res_6451_; 
v_collapsed_boxed_6449_ = lean_unbox(v_collapsed_6430_);
v_clsEnabled_boxed_6450_ = lean_unbox(v_clsEnabled_6433_);
v_res_6451_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6429_, v_collapsed_boxed_6449_, v_tag_6431_, v_opts_6432_, v_clsEnabled_boxed_6450_, v_oldTraces_6434_, v_msg_6435_, v_resStartStop_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_);
lean_dec(v___y_6447_);
lean_dec_ref(v___y_6446_);
lean_dec(v___y_6445_);
lean_dec_ref(v___y_6444_);
lean_dec(v___y_6443_);
lean_dec_ref(v___y_6442_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec(v___y_6439_);
lean_dec(v___y_6438_);
lean_dec_ref(v___y_6437_);
lean_dec_ref(v_opts_6432_);
return v_res_6451_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6457_ = l_Lean_stringToMessageData(v___x_6456_);
return v___x_6457_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6458_, lean_object* v_b_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_){
_start:
{
if (lean_obj_tag(v_as_x27_6458_) == 0)
{
lean_object* v___x_6472_; 
v___x_6472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6472_, 0, v_b_6459_);
return v___x_6472_;
}
else
{
lean_object* v_head_6473_; lean_object* v_toCold_6474_; lean_object* v_options_6475_; lean_object* v_tail_6476_; lean_object* v_name_6477_; lean_object* v_run_x27_6478_; lean_object* v_inheritedTraceOptions_6479_; uint8_t v_hasTrace_6480_; lean_object* v___x_6481_; uint8_t v___y_6483_; lean_object* v___x_6488_; lean_object* v___y_6490_; 
lean_dec_ref(v_b_6459_);
v_head_6473_ = lean_ctor_get(v_as_x27_6458_, 0);
v_toCold_6474_ = lean_ctor_get(v___y_6469_, 0);
v_options_6475_ = lean_ctor_get(v_toCold_6474_, 2);
v_tail_6476_ = lean_ctor_get(v_as_x27_6458_, 1);
v_name_6477_ = lean_ctor_get(v_head_6473_, 0);
v_run_x27_6478_ = lean_ctor_get(v_head_6473_, 1);
v_inheritedTraceOptions_6479_ = lean_ctor_get(v_toCold_6474_, 11);
v_hasTrace_6480_ = lean_ctor_get_uint8(v_options_6475_, sizeof(void*)*1);
v___x_6481_ = lean_box(0);
v___x_6488_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6480_ == 0)
{
lean_object* v___x_6518_; 
lean_inc_ref(v_run_x27_6478_);
lean_inc(v___y_6470_);
lean_inc_ref(v___y_6469_);
lean_inc(v___y_6468_);
lean_inc_ref(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
v___x_6518_ = lean_apply_12(v_run_x27_6478_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_, lean_box(0));
v___y_6490_ = v___x_6518_;
goto v___jp_6489_;
}
else
{
lean_object* v___f_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; uint8_t v___x_6523_; lean_object* v___y_6525_; lean_object* v___y_6526_; lean_object* v_a_6527_; lean_object* v___y_6540_; lean_object* v___y_6541_; lean_object* v_a_6542_; 
lean_inc(v_name_6477_);
v___f_6519_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6519_, 0, v_name_6477_);
v___x_6520_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6521_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6522_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6523_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6479_, v_options_6475_, v___x_6522_);
if (v___x_6523_ == 0)
{
lean_object* v___x_6592_; uint8_t v___x_6593_; 
v___x_6592_ = l_Lean_trace_profiler;
v___x_6593_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6475_, v___x_6592_);
if (v___x_6593_ == 0)
{
lean_object* v___x_6594_; 
lean_dec_ref(v___f_6519_);
lean_inc_ref(v_run_x27_6478_);
lean_inc(v___y_6470_);
lean_inc_ref(v___y_6469_);
lean_inc(v___y_6468_);
lean_inc_ref(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
v___x_6594_ = lean_apply_12(v_run_x27_6478_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_, lean_box(0));
v___y_6490_ = v___x_6594_;
goto v___jp_6489_;
}
else
{
goto v___jp_6551_;
}
}
else
{
goto v___jp_6551_;
}
v___jp_6524_:
{
lean_object* v___x_6528_; double v___x_6529_; double v___x_6530_; double v___x_6531_; double v___x_6532_; double v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; 
v___x_6528_ = lean_io_mono_nanos_now();
v___x_6529_ = lean_float_of_nat(v___y_6526_);
v___x_6530_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6531_ = lean_float_div(v___x_6529_, v___x_6530_);
v___x_6532_ = lean_float_of_nat(v___x_6528_);
v___x_6533_ = lean_float_div(v___x_6532_, v___x_6530_);
v___x_6534_ = lean_box_float(v___x_6531_);
v___x_6535_ = lean_box_float(v___x_6533_);
v___x_6536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6536_, 0, v___x_6534_);
lean_ctor_set(v___x_6536_, 1, v___x_6535_);
v___x_6537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6537_, 0, v_a_6527_);
lean_ctor_set(v___x_6537_, 1, v___x_6536_);
v___x_6538_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6520_, v_hasTrace_6480_, v___x_6521_, v_options_6475_, v___x_6523_, v___y_6525_, v___f_6519_, v___x_6537_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_);
v___y_6490_ = v___x_6538_;
goto v___jp_6489_;
}
v___jp_6539_:
{
lean_object* v___x_6543_; double v___x_6544_; double v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; 
v___x_6543_ = lean_io_get_num_heartbeats();
v___x_6544_ = lean_float_of_nat(v___y_6541_);
v___x_6545_ = lean_float_of_nat(v___x_6543_);
v___x_6546_ = lean_box_float(v___x_6544_);
v___x_6547_ = lean_box_float(v___x_6545_);
v___x_6548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6548_, 0, v___x_6546_);
lean_ctor_set(v___x_6548_, 1, v___x_6547_);
v___x_6549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6549_, 0, v_a_6542_);
lean_ctor_set(v___x_6549_, 1, v___x_6548_);
v___x_6550_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6520_, v_hasTrace_6480_, v___x_6521_, v_options_6475_, v___x_6523_, v___y_6540_, v___f_6519_, v___x_6549_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_);
v___y_6490_ = v___x_6550_;
goto v___jp_6489_;
}
v___jp_6551_:
{
lean_object* v___x_6552_; lean_object* v_a_6553_; lean_object* v___x_6554_; uint8_t v___x_6555_; 
v___x_6552_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6470_);
v_a_6553_ = lean_ctor_get(v___x_6552_, 0);
lean_inc(v_a_6553_);
lean_dec_ref(v___x_6552_);
v___x_6554_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6555_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6475_, v___x_6554_);
if (v___x_6555_ == 0)
{
lean_object* v___x_6556_; lean_object* v___x_6557_; 
v___x_6556_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_6478_);
lean_inc(v___y_6470_);
lean_inc_ref(v___y_6469_);
lean_inc(v___y_6468_);
lean_inc_ref(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
v___x_6557_ = lean_apply_12(v_run_x27_6478_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_, lean_box(0));
if (lean_obj_tag(v___x_6557_) == 0)
{
lean_object* v_a_6558_; lean_object* v___x_6560_; uint8_t v_isShared_6561_; uint8_t v_isSharedCheck_6565_; 
v_a_6558_ = lean_ctor_get(v___x_6557_, 0);
v_isSharedCheck_6565_ = !lean_is_exclusive(v___x_6557_);
if (v_isSharedCheck_6565_ == 0)
{
v___x_6560_ = v___x_6557_;
v_isShared_6561_ = v_isSharedCheck_6565_;
goto v_resetjp_6559_;
}
else
{
lean_inc(v_a_6558_);
lean_dec(v___x_6557_);
v___x_6560_ = lean_box(0);
v_isShared_6561_ = v_isSharedCheck_6565_;
goto v_resetjp_6559_;
}
v_resetjp_6559_:
{
lean_object* v___x_6563_; 
if (v_isShared_6561_ == 0)
{
lean_ctor_set_tag(v___x_6560_, 1);
v___x_6563_ = v___x_6560_;
goto v_reusejp_6562_;
}
else
{
lean_object* v_reuseFailAlloc_6564_; 
v_reuseFailAlloc_6564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6564_, 0, v_a_6558_);
v___x_6563_ = v_reuseFailAlloc_6564_;
goto v_reusejp_6562_;
}
v_reusejp_6562_:
{
v___y_6525_ = v_a_6553_;
v___y_6526_ = v___x_6556_;
v_a_6527_ = v___x_6563_;
goto v___jp_6524_;
}
}
}
else
{
lean_object* v_a_6566_; lean_object* v___x_6568_; uint8_t v_isShared_6569_; uint8_t v_isSharedCheck_6573_; 
v_a_6566_ = lean_ctor_get(v___x_6557_, 0);
v_isSharedCheck_6573_ = !lean_is_exclusive(v___x_6557_);
if (v_isSharedCheck_6573_ == 0)
{
v___x_6568_ = v___x_6557_;
v_isShared_6569_ = v_isSharedCheck_6573_;
goto v_resetjp_6567_;
}
else
{
lean_inc(v_a_6566_);
lean_dec(v___x_6557_);
v___x_6568_ = lean_box(0);
v_isShared_6569_ = v_isSharedCheck_6573_;
goto v_resetjp_6567_;
}
v_resetjp_6567_:
{
lean_object* v___x_6571_; 
if (v_isShared_6569_ == 0)
{
lean_ctor_set_tag(v___x_6568_, 0);
v___x_6571_ = v___x_6568_;
goto v_reusejp_6570_;
}
else
{
lean_object* v_reuseFailAlloc_6572_; 
v_reuseFailAlloc_6572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6572_, 0, v_a_6566_);
v___x_6571_ = v_reuseFailAlloc_6572_;
goto v_reusejp_6570_;
}
v_reusejp_6570_:
{
v___y_6525_ = v_a_6553_;
v___y_6526_ = v___x_6556_;
v_a_6527_ = v___x_6571_;
goto v___jp_6524_;
}
}
}
}
else
{
lean_object* v___x_6574_; lean_object* v___x_6575_; 
v___x_6574_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_6478_);
lean_inc(v___y_6470_);
lean_inc_ref(v___y_6469_);
lean_inc(v___y_6468_);
lean_inc_ref(v___y_6467_);
lean_inc(v___y_6466_);
lean_inc_ref(v___y_6465_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
v___x_6575_ = lean_apply_12(v_run_x27_6478_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_, lean_box(0));
if (lean_obj_tag(v___x_6575_) == 0)
{
lean_object* v_a_6576_; lean_object* v___x_6578_; uint8_t v_isShared_6579_; uint8_t v_isSharedCheck_6583_; 
v_a_6576_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6583_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6583_ == 0)
{
v___x_6578_ = v___x_6575_;
v_isShared_6579_ = v_isSharedCheck_6583_;
goto v_resetjp_6577_;
}
else
{
lean_inc(v_a_6576_);
lean_dec(v___x_6575_);
v___x_6578_ = lean_box(0);
v_isShared_6579_ = v_isSharedCheck_6583_;
goto v_resetjp_6577_;
}
v_resetjp_6577_:
{
lean_object* v___x_6581_; 
if (v_isShared_6579_ == 0)
{
lean_ctor_set_tag(v___x_6578_, 1);
v___x_6581_ = v___x_6578_;
goto v_reusejp_6580_;
}
else
{
lean_object* v_reuseFailAlloc_6582_; 
v_reuseFailAlloc_6582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6582_, 0, v_a_6576_);
v___x_6581_ = v_reuseFailAlloc_6582_;
goto v_reusejp_6580_;
}
v_reusejp_6580_:
{
v___y_6540_ = v_a_6553_;
v___y_6541_ = v___x_6574_;
v_a_6542_ = v___x_6581_;
goto v___jp_6539_;
}
}
}
else
{
lean_object* v_a_6584_; lean_object* v___x_6586_; uint8_t v_isShared_6587_; uint8_t v_isSharedCheck_6591_; 
v_a_6584_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6591_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6591_ == 0)
{
v___x_6586_ = v___x_6575_;
v_isShared_6587_ = v_isSharedCheck_6591_;
goto v_resetjp_6585_;
}
else
{
lean_inc(v_a_6584_);
lean_dec(v___x_6575_);
v___x_6586_ = lean_box(0);
v_isShared_6587_ = v_isSharedCheck_6591_;
goto v_resetjp_6585_;
}
v_resetjp_6585_:
{
lean_object* v___x_6589_; 
if (v_isShared_6587_ == 0)
{
lean_ctor_set_tag(v___x_6586_, 0);
v___x_6589_ = v___x_6586_;
goto v_reusejp_6588_;
}
else
{
lean_object* v_reuseFailAlloc_6590_; 
v_reuseFailAlloc_6590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
v___x_6589_ = v_reuseFailAlloc_6590_;
goto v_reusejp_6588_;
}
v_reusejp_6588_:
{
v___y_6540_ = v_a_6553_;
v___y_6541_ = v___x_6574_;
v_a_6542_ = v___x_6589_;
goto v___jp_6539_;
}
}
}
}
}
}
v___jp_6482_:
{
lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; 
v___x_6484_ = lean_box(v___y_6483_);
v___x_6485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6485_, 0, v___x_6484_);
v___x_6486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6486_, 0, v___x_6485_);
lean_ctor_set(v___x_6486_, 1, v___x_6481_);
v___x_6487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6487_, 0, v___x_6486_);
return v___x_6487_;
}
v___jp_6489_:
{
if (lean_obj_tag(v___y_6490_) == 0)
{
lean_object* v_a_6491_; uint8_t v___x_6492_; 
v_a_6491_ = lean_ctor_get(v___y_6490_, 0);
lean_inc(v_a_6491_);
lean_dec_ref_known(v___y_6490_, 1);
v___x_6492_ = lean_unbox(v_a_6491_);
if (v___x_6492_ == 0)
{
lean_dec(v_a_6491_);
v_as_x27_6458_ = v_tail_6476_;
v_b_6459_ = v___x_6488_;
goto _start;
}
else
{
if (v_hasTrace_6480_ == 0)
{
uint8_t v___x_6494_; 
v___x_6494_ = lean_unbox(v_a_6491_);
lean_dec(v_a_6491_);
v___y_6483_ = v___x_6494_;
goto v___jp_6482_;
}
else
{
lean_object* v___x_6495_; lean_object* v___x_6496_; uint8_t v___x_6497_; 
v___x_6495_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6496_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6497_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6479_, v_options_6475_, v___x_6496_);
if (v___x_6497_ == 0)
{
uint8_t v___x_6498_; 
v___x_6498_ = lean_unbox(v_a_6491_);
lean_dec(v_a_6491_);
v___y_6483_ = v___x_6498_;
goto v___jp_6482_;
}
else
{
lean_object* v___x_6499_; lean_object* v___x_6500_; 
v___x_6499_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_6500_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6495_, v___x_6499_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_);
if (lean_obj_tag(v___x_6500_) == 0)
{
uint8_t v___x_6501_; 
lean_dec_ref_known(v___x_6500_, 1);
v___x_6501_ = lean_unbox(v_a_6491_);
lean_dec(v_a_6491_);
v___y_6483_ = v___x_6501_;
goto v___jp_6482_;
}
else
{
lean_object* v_a_6502_; lean_object* v___x_6504_; uint8_t v_isShared_6505_; uint8_t v_isSharedCheck_6509_; 
lean_dec(v_a_6491_);
v_a_6502_ = lean_ctor_get(v___x_6500_, 0);
v_isSharedCheck_6509_ = !lean_is_exclusive(v___x_6500_);
if (v_isSharedCheck_6509_ == 0)
{
v___x_6504_ = v___x_6500_;
v_isShared_6505_ = v_isSharedCheck_6509_;
goto v_resetjp_6503_;
}
else
{
lean_inc(v_a_6502_);
lean_dec(v___x_6500_);
v___x_6504_ = lean_box(0);
v_isShared_6505_ = v_isSharedCheck_6509_;
goto v_resetjp_6503_;
}
v_resetjp_6503_:
{
lean_object* v___x_6507_; 
if (v_isShared_6505_ == 0)
{
v___x_6507_ = v___x_6504_;
goto v_reusejp_6506_;
}
else
{
lean_object* v_reuseFailAlloc_6508_; 
v_reuseFailAlloc_6508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6508_, 0, v_a_6502_);
v___x_6507_ = v_reuseFailAlloc_6508_;
goto v_reusejp_6506_;
}
v_reusejp_6506_:
{
return v___x_6507_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6510_; lean_object* v___x_6512_; uint8_t v_isShared_6513_; uint8_t v_isSharedCheck_6517_; 
v_a_6510_ = lean_ctor_get(v___y_6490_, 0);
v_isSharedCheck_6517_ = !lean_is_exclusive(v___y_6490_);
if (v_isSharedCheck_6517_ == 0)
{
v___x_6512_ = v___y_6490_;
v_isShared_6513_ = v_isSharedCheck_6517_;
goto v_resetjp_6511_;
}
else
{
lean_inc(v_a_6510_);
lean_dec(v___y_6490_);
v___x_6512_ = lean_box(0);
v_isShared_6513_ = v_isSharedCheck_6517_;
goto v_resetjp_6511_;
}
v_resetjp_6511_:
{
lean_object* v___x_6515_; 
if (v_isShared_6513_ == 0)
{
v___x_6515_ = v___x_6512_;
goto v_reusejp_6514_;
}
else
{
lean_object* v_reuseFailAlloc_6516_; 
v_reuseFailAlloc_6516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6516_, 0, v_a_6510_);
v___x_6515_ = v_reuseFailAlloc_6516_;
goto v_reusejp_6514_;
}
v_reusejp_6514_:
{
return v___x_6515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_6595_, lean_object* v_b_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_, lean_object* v___y_6604_, lean_object* v___y_6605_, lean_object* v___y_6606_, lean_object* v___y_6607_, lean_object* v___y_6608_){
_start:
{
lean_object* v_res_6609_; 
v_res_6609_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6595_, v_b_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
lean_dec(v___y_6607_);
lean_dec_ref(v___y_6606_);
lean_dec(v___y_6605_);
lean_dec_ref(v___y_6604_);
lean_dec(v___y_6603_);
lean_dec_ref(v___y_6602_);
lean_dec(v___y_6601_);
lean_dec_ref(v___y_6600_);
lean_dec(v___y_6599_);
lean_dec(v___y_6598_);
lean_dec_ref(v___y_6597_);
lean_dec(v_as_x27_6595_);
return v_res_6609_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_6612_; lean_object* v___x_6613_; 
v___x_6612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_6613_ = l_Lean_stringToMessageData(v___x_6612_);
return v___x_6613_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_6615_; lean_object* v___x_6616_; 
v___x_6615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_6616_ = l_Lean_stringToMessageData(v___x_6615_);
return v___x_6616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_, lean_object* v_a_6626_, lean_object* v_a_6627_, lean_object* v_a_6628_){
_start:
{
lean_object* v___x_6630_; lean_object* v___x_6631_; 
v___x_6630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_6631_ = l_Lean_Core_checkSystem(v___x_6630_, v_a_6627_, v_a_6628_);
if (lean_obj_tag(v___x_6631_) == 0)
{
lean_object* v___x_6632_; lean_object* v_caches_6633_; lean_object* v_typeAnalysis_6634_; lean_object* v_target_6635_; lean_object* v_hypotheses_6636_; lean_object* v___x_6638_; uint8_t v_isShared_6639_; uint8_t v_isSharedCheck_6721_; 
lean_dec_ref_known(v___x_6631_, 1);
v___x_6632_ = lean_st_ref_take(v_a_6619_);
v_caches_6633_ = lean_ctor_get(v___x_6632_, 0);
v_typeAnalysis_6634_ = lean_ctor_get(v___x_6632_, 1);
v_target_6635_ = lean_ctor_get(v___x_6632_, 2);
v_hypotheses_6636_ = lean_ctor_get(v___x_6632_, 3);
v_isSharedCheck_6721_ = !lean_is_exclusive(v___x_6632_);
if (v_isSharedCheck_6721_ == 0)
{
v___x_6638_ = v___x_6632_;
v_isShared_6639_ = v_isSharedCheck_6721_;
goto v_resetjp_6637_;
}
else
{
lean_inc(v_hypotheses_6636_);
lean_inc(v_target_6635_);
lean_inc(v_typeAnalysis_6634_);
lean_inc(v_caches_6633_);
lean_dec(v___x_6632_);
v___x_6638_ = lean_box(0);
v_isShared_6639_ = v_isSharedCheck_6721_;
goto v_resetjp_6637_;
}
v_resetjp_6637_:
{
uint8_t v___x_6640_; lean_object* v___x_6642_; 
v___x_6640_ = 0;
if (v_isShared_6639_ == 0)
{
v___x_6642_ = v___x_6638_;
goto v_reusejp_6641_;
}
else
{
lean_object* v_reuseFailAlloc_6720_; 
v_reuseFailAlloc_6720_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6720_, 0, v_caches_6633_);
lean_ctor_set(v_reuseFailAlloc_6720_, 1, v_typeAnalysis_6634_);
lean_ctor_set(v_reuseFailAlloc_6720_, 2, v_target_6635_);
lean_ctor_set(v_reuseFailAlloc_6720_, 3, v_hypotheses_6636_);
v___x_6642_ = v_reuseFailAlloc_6720_;
goto v_reusejp_6641_;
}
v_reusejp_6641_:
{
lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; 
lean_ctor_set_uint8(v___x_6642_, sizeof(void*)*4, v___x_6640_);
v___x_6643_ = lean_st_ref_put(v_a_6619_, v___x_6642_);
v___x_6644_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_6645_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_6617_, v___x_6644_, v_a_6618_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_, v_a_6623_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_, v_a_6628_);
if (lean_obj_tag(v___x_6645_) == 0)
{
lean_object* v_a_6646_; lean_object* v___x_6648_; uint8_t v_isShared_6649_; uint8_t v_isSharedCheck_6711_; 
v_a_6646_ = lean_ctor_get(v___x_6645_, 0);
v_isSharedCheck_6711_ = !lean_is_exclusive(v___x_6645_);
if (v_isSharedCheck_6711_ == 0)
{
v___x_6648_ = v___x_6645_;
v_isShared_6649_ = v_isSharedCheck_6711_;
goto v_resetjp_6647_;
}
else
{
lean_inc(v_a_6646_);
lean_dec(v___x_6645_);
v___x_6648_ = lean_box(0);
v_isShared_6649_ = v_isSharedCheck_6711_;
goto v_resetjp_6647_;
}
v_resetjp_6647_:
{
lean_object* v_fst_6650_; 
v_fst_6650_ = lean_ctor_get(v_a_6646_, 0);
lean_inc(v_fst_6650_);
lean_dec(v_a_6646_);
if (lean_obj_tag(v_fst_6650_) == 0)
{
lean_object* v___x_6651_; uint8_t v_didChange_6652_; 
v___x_6651_ = lean_st_ref_get(v_a_6619_);
v_didChange_6652_ = lean_ctor_get_uint8(v___x_6651_, sizeof(void*)*4);
lean_dec(v___x_6651_);
if (v_didChange_6652_ == 0)
{
lean_object* v_toCold_6653_; lean_object* v_options_6654_; uint8_t v_hasTrace_6655_; 
v_toCold_6653_ = lean_ctor_get(v_a_6627_, 0);
v_options_6654_ = lean_ctor_get(v_toCold_6653_, 2);
v_hasTrace_6655_ = lean_ctor_get_uint8(v_options_6654_, sizeof(void*)*1);
if (v_hasTrace_6655_ == 0)
{
lean_object* v___x_6656_; lean_object* v___x_6658_; 
v___x_6656_ = lean_box(v_didChange_6652_);
if (v_isShared_6649_ == 0)
{
lean_ctor_set(v___x_6648_, 0, v___x_6656_);
v___x_6658_ = v___x_6648_;
goto v_reusejp_6657_;
}
else
{
lean_object* v_reuseFailAlloc_6659_; 
v_reuseFailAlloc_6659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6659_, 0, v___x_6656_);
v___x_6658_ = v_reuseFailAlloc_6659_;
goto v_reusejp_6657_;
}
v_reusejp_6657_:
{
return v___x_6658_;
}
}
else
{
lean_object* v_inheritedTraceOptions_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; uint8_t v___x_6663_; 
v_inheritedTraceOptions_6660_ = lean_ctor_get(v_toCold_6653_, 11);
v___x_6661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6662_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6660_, v_options_6654_, v___x_6662_);
if (v___x_6663_ == 0)
{
lean_object* v___x_6664_; lean_object* v___x_6666_; 
v___x_6664_ = lean_box(v_didChange_6652_);
if (v_isShared_6649_ == 0)
{
lean_ctor_set(v___x_6648_, 0, v___x_6664_);
v___x_6666_ = v___x_6648_;
goto v_reusejp_6665_;
}
else
{
lean_object* v_reuseFailAlloc_6667_; 
v_reuseFailAlloc_6667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6667_, 0, v___x_6664_);
v___x_6666_ = v_reuseFailAlloc_6667_;
goto v_reusejp_6665_;
}
v_reusejp_6665_:
{
return v___x_6666_;
}
}
else
{
lean_object* v___x_6668_; lean_object* v___x_6669_; 
lean_del_object(v___x_6648_);
v___x_6668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6669_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6661_, v___x_6668_, v_a_6625_, v_a_6626_, v_a_6627_, v_a_6628_);
if (lean_obj_tag(v___x_6669_) == 0)
{
lean_object* v___x_6671_; uint8_t v_isShared_6672_; uint8_t v_isSharedCheck_6677_; 
v_isSharedCheck_6677_ = !lean_is_exclusive(v___x_6669_);
if (v_isSharedCheck_6677_ == 0)
{
lean_object* v_unused_6678_; 
v_unused_6678_ = lean_ctor_get(v___x_6669_, 0);
lean_dec(v_unused_6678_);
v___x_6671_ = v___x_6669_;
v_isShared_6672_ = v_isSharedCheck_6677_;
goto v_resetjp_6670_;
}
else
{
lean_dec(v___x_6669_);
v___x_6671_ = lean_box(0);
v_isShared_6672_ = v_isSharedCheck_6677_;
goto v_resetjp_6670_;
}
v_resetjp_6670_:
{
lean_object* v___x_6673_; lean_object* v___x_6675_; 
v___x_6673_ = lean_box(v_didChange_6652_);
if (v_isShared_6672_ == 0)
{
lean_ctor_set(v___x_6671_, 0, v___x_6673_);
v___x_6675_ = v___x_6671_;
goto v_reusejp_6674_;
}
else
{
lean_object* v_reuseFailAlloc_6676_; 
v_reuseFailAlloc_6676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6676_, 0, v___x_6673_);
v___x_6675_ = v_reuseFailAlloc_6676_;
goto v_reusejp_6674_;
}
v_reusejp_6674_:
{
return v___x_6675_;
}
}
}
else
{
lean_object* v_a_6679_; lean_object* v___x_6681_; uint8_t v_isShared_6682_; uint8_t v_isSharedCheck_6686_; 
v_a_6679_ = lean_ctor_get(v___x_6669_, 0);
v_isSharedCheck_6686_ = !lean_is_exclusive(v___x_6669_);
if (v_isSharedCheck_6686_ == 0)
{
v___x_6681_ = v___x_6669_;
v_isShared_6682_ = v_isSharedCheck_6686_;
goto v_resetjp_6680_;
}
else
{
lean_inc(v_a_6679_);
lean_dec(v___x_6669_);
v___x_6681_ = lean_box(0);
v_isShared_6682_ = v_isSharedCheck_6686_;
goto v_resetjp_6680_;
}
v_resetjp_6680_:
{
lean_object* v___x_6684_; 
if (v_isShared_6682_ == 0)
{
v___x_6684_ = v___x_6681_;
goto v_reusejp_6683_;
}
else
{
lean_object* v_reuseFailAlloc_6685_; 
v_reuseFailAlloc_6685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6685_, 0, v_a_6679_);
v___x_6684_ = v_reuseFailAlloc_6685_;
goto v_reusejp_6683_;
}
v_reusejp_6683_:
{
return v___x_6684_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_6687_; lean_object* v_options_6688_; uint8_t v_hasTrace_6689_; 
lean_del_object(v___x_6648_);
v_toCold_6687_ = lean_ctor_get(v_a_6627_, 0);
v_options_6688_ = lean_ctor_get(v_toCold_6687_, 2);
v_hasTrace_6689_ = lean_ctor_get_uint8(v_options_6688_, sizeof(void*)*1);
if (v_hasTrace_6689_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; uint8_t v___x_6694_; 
v_inheritedTraceOptions_6691_ = lean_ctor_get(v_toCold_6687_, 11);
v___x_6692_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6693_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6694_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6691_, v_options_6688_, v___x_6693_);
if (v___x_6694_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6696_; lean_object* v___x_6697_; 
v___x_6696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6697_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6692_, v___x_6696_, v_a_6625_, v_a_6626_, v_a_6627_, v_a_6628_);
if (lean_obj_tag(v___x_6697_) == 0)
{
lean_dec_ref_known(v___x_6697_, 1);
goto _start;
}
else
{
lean_object* v_a_6699_; lean_object* v___x_6701_; uint8_t v_isShared_6702_; uint8_t v_isSharedCheck_6706_; 
v_a_6699_ = lean_ctor_get(v___x_6697_, 0);
v_isSharedCheck_6706_ = !lean_is_exclusive(v___x_6697_);
if (v_isSharedCheck_6706_ == 0)
{
v___x_6701_ = v___x_6697_;
v_isShared_6702_ = v_isSharedCheck_6706_;
goto v_resetjp_6700_;
}
else
{
lean_inc(v_a_6699_);
lean_dec(v___x_6697_);
v___x_6701_ = lean_box(0);
v_isShared_6702_ = v_isSharedCheck_6706_;
goto v_resetjp_6700_;
}
v_resetjp_6700_:
{
lean_object* v___x_6704_; 
if (v_isShared_6702_ == 0)
{
v___x_6704_ = v___x_6701_;
goto v_reusejp_6703_;
}
else
{
lean_object* v_reuseFailAlloc_6705_; 
v_reuseFailAlloc_6705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6705_, 0, v_a_6699_);
v___x_6704_ = v_reuseFailAlloc_6705_;
goto v_reusejp_6703_;
}
v_reusejp_6703_:
{
return v___x_6704_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_6707_; lean_object* v___x_6709_; 
v_val_6707_ = lean_ctor_get(v_fst_6650_, 0);
lean_inc(v_val_6707_);
lean_dec_ref_known(v_fst_6650_, 1);
if (v_isShared_6649_ == 0)
{
lean_ctor_set(v___x_6648_, 0, v_val_6707_);
v___x_6709_ = v___x_6648_;
goto v_reusejp_6708_;
}
else
{
lean_object* v_reuseFailAlloc_6710_; 
v_reuseFailAlloc_6710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6710_, 0, v_val_6707_);
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
else
{
lean_object* v_a_6712_; lean_object* v___x_6714_; uint8_t v_isShared_6715_; uint8_t v_isSharedCheck_6719_; 
v_a_6712_ = lean_ctor_get(v___x_6645_, 0);
v_isSharedCheck_6719_ = !lean_is_exclusive(v___x_6645_);
if (v_isSharedCheck_6719_ == 0)
{
v___x_6714_ = v___x_6645_;
v_isShared_6715_ = v_isSharedCheck_6719_;
goto v_resetjp_6713_;
}
else
{
lean_inc(v_a_6712_);
lean_dec(v___x_6645_);
v___x_6714_ = lean_box(0);
v_isShared_6715_ = v_isSharedCheck_6719_;
goto v_resetjp_6713_;
}
v_resetjp_6713_:
{
lean_object* v___x_6717_; 
if (v_isShared_6715_ == 0)
{
v___x_6717_ = v___x_6714_;
goto v_reusejp_6716_;
}
else
{
lean_object* v_reuseFailAlloc_6718_; 
v_reuseFailAlloc_6718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6718_, 0, v_a_6712_);
v___x_6717_ = v_reuseFailAlloc_6718_;
goto v_reusejp_6716_;
}
v_reusejp_6716_:
{
return v___x_6717_;
}
}
}
}
}
}
else
{
lean_object* v_a_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6729_; 
v_a_6722_ = lean_ctor_get(v___x_6631_, 0);
v_isSharedCheck_6729_ = !lean_is_exclusive(v___x_6631_);
if (v_isSharedCheck_6729_ == 0)
{
v___x_6724_ = v___x_6631_;
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_a_6722_);
lean_dec(v___x_6631_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
lean_object* v___x_6727_; 
if (v_isShared_6725_ == 0)
{
v___x_6727_ = v___x_6724_;
goto v_reusejp_6726_;
}
else
{
lean_object* v_reuseFailAlloc_6728_; 
v_reuseFailAlloc_6728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6728_, 0, v_a_6722_);
v___x_6727_ = v_reuseFailAlloc_6728_;
goto v_reusejp_6726_;
}
v_reusejp_6726_:
{
return v___x_6727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6730_, lean_object* v_a_6731_, lean_object* v_a_6732_, lean_object* v_a_6733_, lean_object* v_a_6734_, lean_object* v_a_6735_, lean_object* v_a_6736_, lean_object* v_a_6737_, lean_object* v_a_6738_, lean_object* v_a_6739_, lean_object* v_a_6740_, lean_object* v_a_6741_, lean_object* v_a_6742_){
_start:
{
lean_object* v_res_6743_; 
v_res_6743_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6730_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_, v_a_6735_, v_a_6736_, v_a_6737_, v_a_6738_, v_a_6739_, v_a_6740_, v_a_6741_);
lean_dec(v_a_6741_);
lean_dec_ref(v_a_6740_);
lean_dec(v_a_6739_);
lean_dec_ref(v_a_6738_);
lean_dec(v_a_6737_);
lean_dec_ref(v_a_6736_);
lean_dec(v_a_6735_);
lean_dec_ref(v_a_6734_);
lean_dec(v_a_6733_);
lean_dec(v_a_6732_);
lean_dec_ref(v_a_6731_);
lean_dec(v_passes_6730_);
return v_res_6743_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6744_, lean_object* v_msg_6745_, lean_object* v___y_6746_, lean_object* v___y_6747_, lean_object* v___y_6748_, lean_object* v___y_6749_, lean_object* v___y_6750_, lean_object* v___y_6751_, lean_object* v___y_6752_, lean_object* v___y_6753_, lean_object* v___y_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_){
_start:
{
lean_object* v___x_6758_; 
v___x_6758_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6744_, v_msg_6745_, v___y_6753_, v___y_6754_, v___y_6755_, v___y_6756_);
return v___x_6758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6759_, lean_object* v_msg_6760_, lean_object* v___y_6761_, lean_object* v___y_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_, lean_object* v___y_6765_, lean_object* v___y_6766_, lean_object* v___y_6767_, lean_object* v___y_6768_, lean_object* v___y_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_, lean_object* v___y_6772_){
_start:
{
lean_object* v_res_6773_; 
v_res_6773_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6759_, v_msg_6760_, v___y_6761_, v___y_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_);
lean_dec(v___y_6771_);
lean_dec_ref(v___y_6770_);
lean_dec(v___y_6769_);
lean_dec_ref(v___y_6768_);
lean_dec(v___y_6767_);
lean_dec_ref(v___y_6766_);
lean_dec(v___y_6765_);
lean_dec_ref(v___y_6764_);
lean_dec(v___y_6763_);
lean_dec(v___y_6762_);
lean_dec_ref(v___y_6761_);
return v_res_6773_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6774_, lean_object* v_x_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_, lean_object* v___y_6786_){
_start:
{
lean_object* v___x_6788_; 
v___x_6788_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6775_);
return v___x_6788_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6789_, lean_object* v_x_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_){
_start:
{
lean_object* v_res_6803_; 
v_res_6803_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6789_, v_x_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_);
lean_dec(v___y_6801_);
lean_dec_ref(v___y_6800_);
lean_dec(v___y_6799_);
lean_dec_ref(v___y_6798_);
lean_dec(v___y_6797_);
lean_dec_ref(v___y_6796_);
lean_dec(v___y_6795_);
lean_dec_ref(v___y_6794_);
lean_dec(v___y_6793_);
lean_dec(v___y_6792_);
lean_dec_ref(v___y_6791_);
return v_res_6803_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6804_, lean_object* v_as_x27_6805_, lean_object* v_b_6806_, lean_object* v_a_6807_, lean_object* v___y_6808_, lean_object* v___y_6809_, lean_object* v___y_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_, lean_object* v___y_6816_, lean_object* v___y_6817_, lean_object* v___y_6818_){
_start:
{
lean_object* v___x_6820_; 
v___x_6820_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6805_, v_b_6806_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_, v___y_6813_, v___y_6814_, v___y_6815_, v___y_6816_, v___y_6817_, v___y_6818_);
return v___x_6820_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6821_, lean_object* v_as_x27_6822_, lean_object* v_b_6823_, lean_object* v_a_6824_, lean_object* v___y_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_, lean_object* v___y_6834_, lean_object* v___y_6835_, lean_object* v___y_6836_){
_start:
{
lean_object* v_res_6837_; 
v_res_6837_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6821_, v_as_x27_6822_, v_b_6823_, v_a_6824_, v___y_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_);
lean_dec(v___y_6835_);
lean_dec_ref(v___y_6834_);
lean_dec(v___y_6833_);
lean_dec_ref(v___y_6832_);
lean_dec(v___y_6831_);
lean_dec_ref(v___y_6830_);
lean_dec(v___y_6829_);
lean_dec_ref(v___y_6828_);
lean_dec(v___y_6827_);
lean_dec(v___y_6826_);
lean_dec_ref(v___y_6825_);
lean_dec(v_as_x27_6822_);
lean_dec(v_as_6821_);
return v_res_6837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6838_, lean_object* v_data_6839_, lean_object* v_ref_6840_, lean_object* v_msg_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_, lean_object* v___y_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_, lean_object* v___y_6850_, lean_object* v___y_6851_, lean_object* v___y_6852_){
_start:
{
lean_object* v___x_6854_; 
v___x_6854_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6838_, v_data_6839_, v_ref_6840_, v_msg_6841_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
return v___x_6854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6855_, lean_object* v_data_6856_, lean_object* v_ref_6857_, lean_object* v_msg_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_, lean_object* v___y_6868_, lean_object* v___y_6869_, lean_object* v___y_6870_){
_start:
{
lean_object* v_res_6871_; 
v_res_6871_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6855_, v_data_6856_, v_ref_6857_, v_msg_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_, v___y_6869_);
lean_dec(v___y_6869_);
lean_dec_ref(v___y_6868_);
lean_dec(v___y_6867_);
lean_dec_ref(v___y_6866_);
lean_dec(v___y_6865_);
lean_dec_ref(v___y_6864_);
lean_dec(v___y_6863_);
lean_dec_ref(v___y_6862_);
lean_dec(v___y_6861_);
lean_dec(v___y_6860_);
lean_dec_ref(v___y_6859_);
return v_res_6871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_, lean_object* v_a_6878_, lean_object* v_a_6879_, lean_object* v_a_6880_, lean_object* v_a_6881_, lean_object* v_a_6882_, lean_object* v_a_6883_){
_start:
{
lean_object* v___x_6885_; 
v___x_6885_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6872_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_, v_a_6877_, v_a_6878_, v_a_6879_, v_a_6880_, v_a_6881_, v_a_6882_, v_a_6883_);
if (lean_obj_tag(v___x_6885_) == 0)
{
lean_object* v_a_6886_; lean_object* v___x_6887_; lean_object* v___x_6889_; uint8_t v_isShared_6890_; uint8_t v_isSharedCheck_6894_; 
v_a_6886_ = lean_ctor_get(v___x_6885_, 0);
lean_inc(v_a_6886_);
lean_dec_ref_known(v___x_6885_, 1);
v___x_6887_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_6873_, v_a_6874_);
v_isSharedCheck_6894_ = !lean_is_exclusive(v___x_6887_);
if (v_isSharedCheck_6894_ == 0)
{
lean_object* v_unused_6895_; 
v_unused_6895_ = lean_ctor_get(v___x_6887_, 0);
lean_dec(v_unused_6895_);
v___x_6889_ = v___x_6887_;
v_isShared_6890_ = v_isSharedCheck_6894_;
goto v_resetjp_6888_;
}
else
{
lean_dec(v___x_6887_);
v___x_6889_ = lean_box(0);
v_isShared_6890_ = v_isSharedCheck_6894_;
goto v_resetjp_6888_;
}
v_resetjp_6888_:
{
lean_object* v___x_6892_; 
if (v_isShared_6890_ == 0)
{
lean_ctor_set(v___x_6889_, 0, v_a_6886_);
v___x_6892_ = v___x_6889_;
goto v_reusejp_6891_;
}
else
{
lean_object* v_reuseFailAlloc_6893_; 
v_reuseFailAlloc_6893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6893_, 0, v_a_6886_);
v___x_6892_ = v_reuseFailAlloc_6893_;
goto v_reusejp_6891_;
}
v_reusejp_6891_:
{
return v___x_6892_;
}
}
}
else
{
return v___x_6885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_, lean_object* v_a_6903_, lean_object* v_a_6904_, lean_object* v_a_6905_, lean_object* v_a_6906_, lean_object* v_a_6907_, lean_object* v_a_6908_){
_start:
{
lean_object* v_res_6909_; 
v_res_6909_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6896_, v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_, v_a_6905_, v_a_6906_, v_a_6907_);
lean_dec(v_a_6907_);
lean_dec_ref(v_a_6906_);
lean_dec(v_a_6905_);
lean_dec_ref(v_a_6904_);
lean_dec(v_a_6903_);
lean_dec_ref(v_a_6902_);
lean_dec(v_a_6901_);
lean_dec_ref(v_a_6900_);
lean_dec(v_a_6899_);
lean_dec(v_a_6898_);
lean_dec_ref(v_a_6897_);
lean_dec(v_passes_6896_);
return v_res_6909_;
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
