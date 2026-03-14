// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.Attr
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEST(lean_object*, lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_simpleEnum_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_enumWithDefault_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getPropHyps___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " on\n"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultOption___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Fixpoint iteration solved the goal"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Rerunning pipeline on:\n"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pipeline reached a fixpoint"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_info_8_; lean_object* v_ctors_9_; lean_object* v___x_10_; 
v_info_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_info_8_);
v_ctors_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_ctors_9_);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_info_8_, v_ctors_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object* v_t_23_, lean_object* v_simpleEnum_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___redArg(v_t_23_, v_simpleEnum_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_simpleEnum_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_simpleEnum_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___redArg(v_t_27_, v_simpleEnum_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object* v_t_31_, lean_object* v_enumWithDefault_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___redArg(v_t_31_, v_enumWithDefault_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_enumWithDefault_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_enumWithDefault_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_MatchKind_ctorElim___redArg(v_t_35_, v_enumWithDefault_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v_a_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig___redArg(v_a_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig(lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_a_45_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig(v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg(lean_object* v_fvar_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; lean_object* v_rewriteCache_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_66_ = lean_st_ref_get(v_a_64_);
v_rewriteCache_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_rewriteCache_67_);
lean_dec(v___x_66_);
v___x_68_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_69_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_70_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_68_, v___x_69_, v_rewriteCache_67_, v_fvar_63_);
lean_dec_ref(v_rewriteCache_67_);
v___x_71_ = lean_box(v___x_70_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___boxed(lean_object* v_fvar_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg(v_fvar_73_, v_a_74_);
lean_dec(v_a_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten(lean_object* v_fvar_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; lean_object* v_rewriteCache_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_85_ = lean_st_ref_get(v_a_79_);
v_rewriteCache_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_rewriteCache_86_);
lean_dec(v___x_85_);
v___x_87_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_88_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_89_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_87_, v___x_88_, v_rewriteCache_86_, v_fvar_77_);
lean_dec_ref(v_rewriteCache_86_);
v___x_90_ = lean_box(v___x_89_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___boxed(lean_object* v_fvar_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten(v_fvar_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf___redArg(lean_object* v_fvar_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; lean_object* v_acNfCache_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_104_ = lean_st_ref_get(v_a_102_);
v_acNfCache_105_ = lean_ctor_get(v___x_104_, 1);
lean_inc_ref(v_acNfCache_105_);
lean_dec(v___x_104_);
v___x_106_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_107_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_106_, v___x_107_, v_acNfCache_105_, v_fvar_101_);
lean_dec_ref(v_acNfCache_105_);
v___x_109_ = lean_box(v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf___redArg___boxed(lean_object* v_fvar_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf___redArg(v_fvar_111_, v_a_112_);
lean_dec(v_a_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf(lean_object* v_fvar_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; lean_object* v_acNfCache_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_123_ = lean_st_ref_get(v_a_117_);
v_acNfCache_124_ = lean_ctor_get(v___x_123_, 1);
lean_inc_ref(v_acNfCache_124_);
lean_dec(v___x_123_);
v___x_125_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_126_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_125_, v___x_126_, v_acNfCache_124_, v_fvar_115_);
lean_dec_ref(v_acNfCache_124_);
v___x_128_ = lean_box(v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf___boxed(lean_object* v_fvar_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkAcNf(v_fvar_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished___redArg(lean_object* v_fvar_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_142_; lean_object* v_rewriteCache_143_; lean_object* v_acNfCache_144_; lean_object* v_typeAnalysis_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_158_; 
v___x_142_ = lean_st_ref_take(v_a_140_);
v_rewriteCache_143_ = lean_ctor_get(v___x_142_, 0);
v_acNfCache_144_ = lean_ctor_get(v___x_142_, 1);
v_typeAnalysis_145_ = lean_ctor_get(v___x_142_, 2);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_158_ == 0)
{
v___x_147_ = v___x_142_;
v_isShared_148_ = v_isSharedCheck_158_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_typeAnalysis_145_);
lean_inc(v_acNfCache_144_);
lean_inc(v_rewriteCache_143_);
lean_dec(v___x_142_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_158_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_149_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_150_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_151_ = lean_box(0);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_149_, v___x_150_, v_rewriteCache_143_, v_fvar_139_, v___x_151_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_152_);
v___x_154_ = v___x_147_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_acNfCache_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_typeAnalysis_145_);
v___x_154_ = v_reuseFailAlloc_157_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_st_ref_set(v_a_140_, v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_151_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished___redArg___boxed(lean_object* v_fvar_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished___redArg(v_fvar_159_, v_a_160_);
lean_dec(v_a_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished(lean_object* v_fvar_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_171_; lean_object* v_rewriteCache_172_; lean_object* v_acNfCache_173_; lean_object* v_typeAnalysis_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_187_; 
v___x_171_ = lean_st_ref_take(v_a_165_);
v_rewriteCache_172_ = lean_ctor_get(v___x_171_, 0);
v_acNfCache_173_ = lean_ctor_get(v___x_171_, 1);
v_typeAnalysis_174_ = lean_ctor_get(v___x_171_, 2);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_187_ == 0)
{
v___x_176_ = v___x_171_;
v_isShared_177_ = v_isSharedCheck_187_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_typeAnalysis_174_);
lean_inc(v_acNfCache_173_);
lean_inc(v_rewriteCache_172_);
lean_dec(v___x_171_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_187_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_178_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_179_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_180_ = lean_box(0);
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_178_, v___x_179_, v_rewriteCache_172_, v_fvar_163_, v___x_180_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_181_);
v___x_183_ = v___x_176_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_acNfCache_173_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_typeAnalysis_174_);
v___x_183_ = v_reuseFailAlloc_186_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_st_ref_set(v_a_165_, v___x_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_180_);
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished___boxed(lean_object* v_fvar_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_rewriteFinished(v_fvar_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished___redArg(lean_object* v_fvar_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; lean_object* v_rewriteCache_201_; lean_object* v_acNfCache_202_; lean_object* v_typeAnalysis_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_216_; 
v___x_200_ = lean_st_ref_take(v_a_198_);
v_rewriteCache_201_ = lean_ctor_get(v___x_200_, 0);
v_acNfCache_202_ = lean_ctor_get(v___x_200_, 1);
v_typeAnalysis_203_ = lean_ctor_get(v___x_200_, 2);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_216_ == 0)
{
v___x_205_ = v___x_200_;
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_typeAnalysis_203_);
lean_inc(v_acNfCache_202_);
lean_inc(v_rewriteCache_201_);
lean_dec(v___x_200_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_207_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_208_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_209_ = lean_box(0);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_207_, v___x_208_, v_acNfCache_202_, v_fvar_197_, v___x_209_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_210_);
v___x_212_ = v___x_205_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_rewriteCache_201_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_typeAnalysis_203_);
v___x_212_ = v_reuseFailAlloc_215_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_st_ref_set(v_a_198_, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_209_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished___redArg___boxed(lean_object* v_fvar_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished___redArg(v_fvar_217_, v_a_218_);
lean_dec(v_a_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished(lean_object* v_fvar_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; lean_object* v_rewriteCache_230_; lean_object* v_acNfCache_231_; lean_object* v_typeAnalysis_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_245_; 
v___x_229_ = lean_st_ref_take(v_a_223_);
v_rewriteCache_230_ = lean_ctor_get(v___x_229_, 0);
v_acNfCache_231_ = lean_ctor_get(v___x_229_, 1);
v_typeAnalysis_232_ = lean_ctor_get(v___x_229_, 2);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_245_ == 0)
{
v___x_234_ = v___x_229_;
v_isShared_235_ = v_isSharedCheck_245_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_typeAnalysis_232_);
lean_inc(v_acNfCache_231_);
lean_inc(v_rewriteCache_230_);
lean_dec(v___x_229_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_245_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_236_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_237_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_238_ = lean_box(0);
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_236_, v___x_237_, v_acNfCache_231_, v_fvar_221_, v___x_238_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_239_);
v___x_241_ = v___x_234_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_rewriteCache_230_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_typeAnalysis_232_);
v___x_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_st_ref_set(v_a_223_, v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_238_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished___boxed(lean_object* v_fvar_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_acNfFinished(v_fvar_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_255_){
_start:
{
lean_object* v___x_257_; lean_object* v_typeAnalysis_258_; lean_object* v___x_259_; 
v___x_257_ = lean_st_ref_get(v_a_255_);
v_typeAnalysis_258_ = lean_ctor_get(v___x_257_, 2);
lean_inc_ref(v_typeAnalysis_258_);
lean_dec(v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_typeAnalysis_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_260_);
lean_dec(v_a_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_270_; lean_object* v_typeAnalysis_271_; lean_object* v___x_272_; 
v___x_270_ = lean_st_ref_get(v_a_264_);
v_typeAnalysis_271_ = lean_ctor_get(v___x_270_, 2);
lean_inc_ref(v_typeAnalysis_271_);
lean_dec(v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v_typeAnalysis_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getTypeAnalysis(v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; lean_object* v_typeAnalysis_290_; lean_object* v_interestingStructures_291_; lean_object* v_uninteresting_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_289_ = lean_st_ref_get(v_a_287_);
v_typeAnalysis_290_ = lean_ctor_get(v___x_289_, 2);
lean_inc_ref(v_typeAnalysis_290_);
lean_dec(v___x_289_);
v_interestingStructures_291_ = lean_ctor_get(v_typeAnalysis_290_, 0);
lean_inc_ref(v_interestingStructures_291_);
v_uninteresting_292_ = lean_ctor_get(v_typeAnalysis_290_, 3);
lean_inc_ref(v_uninteresting_292_);
lean_dec_ref(v_typeAnalysis_290_);
v___x_293_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_294_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_286_);
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_293_, v___x_294_, v_uninteresting_292_, v_n_286_);
lean_dec_ref(v_uninteresting_292_);
if (v___x_295_ == 0)
{
uint8_t v___x_296_; 
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_293_, v___x_294_, v_interestingStructures_291_, v_n_286_);
lean_dec_ref(v_interestingStructures_291_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_box(v___x_296_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_interestingStructures_291_);
lean_dec(v_n_286_);
v___x_302_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_304_, v_a_305_);
lean_dec(v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; lean_object* v_typeAnalysis_317_; lean_object* v_interestingStructures_318_; lean_object* v_uninteresting_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_316_ = lean_st_ref_get(v_a_310_);
v_typeAnalysis_317_ = lean_ctor_get(v___x_316_, 2);
lean_inc_ref(v_typeAnalysis_317_);
lean_dec(v___x_316_);
v_interestingStructures_318_ = lean_ctor_get(v_typeAnalysis_317_, 0);
lean_inc_ref(v_interestingStructures_318_);
v_uninteresting_319_ = lean_ctor_get(v_typeAnalysis_317_, 3);
lean_inc_ref(v_uninteresting_319_);
lean_dec_ref(v_typeAnalysis_317_);
v___x_320_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_321_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_308_);
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_320_, v___x_321_, v_uninteresting_319_, v_n_308_);
lean_dec_ref(v_uninteresting_319_);
if (v___x_322_ == 0)
{
uint8_t v___x_323_; 
v___x_323_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_320_, v___x_321_, v_interestingStructures_318_, v_n_308_);
lean_dec_ref(v_interestingStructures_318_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_box(0);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_box(v___x_323_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_interestingStructures_318_);
lean_dec(v_n_308_);
v___x_329_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure(v_n_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_rewriteCache_344_; lean_object* v_acNfCache_345_; lean_object* v_typeAnalysis_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_357_; 
v___x_343_ = lean_st_ref_take(v_a_341_);
v_rewriteCache_344_ = lean_ctor_get(v___x_343_, 0);
v_acNfCache_345_ = lean_ctor_get(v___x_343_, 1);
v_typeAnalysis_346_ = lean_ctor_get(v___x_343_, 2);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_357_ == 0)
{
v___x_348_ = v___x_343_;
v_isShared_349_ = v_isSharedCheck_357_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_typeAnalysis_346_);
lean_inc(v_acNfCache_345_);
lean_inc(v_rewriteCache_344_);
lean_dec(v___x_343_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_357_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_apply_1(v_f_340_, v_typeAnalysis_346_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 2, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_rewriteCache_344_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_acNfCache_345_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v___x_350_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_st_ref_set(v_a_341_, v___x_352_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_358_, v_a_359_);
lean_dec(v_a_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; lean_object* v_rewriteCache_371_; lean_object* v_acNfCache_372_; lean_object* v_typeAnalysis_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_384_; 
v___x_370_ = lean_st_ref_take(v_a_364_);
v_rewriteCache_371_ = lean_ctor_get(v___x_370_, 0);
v_acNfCache_372_ = lean_ctor_get(v___x_370_, 1);
v_typeAnalysis_373_ = lean_ctor_get(v___x_370_, 2);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_384_ == 0)
{
v___x_375_ = v___x_370_;
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_typeAnalysis_373_);
lean_inc(v_acNfCache_372_);
lean_inc(v_rewriteCache_371_);
lean_dec(v___x_370_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_apply_1(v_f_362_, v_typeAnalysis_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 2, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_rewriteCache_371_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_acNfCache_372_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v___x_377_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_st_ref_set(v_a_364_, v___x_379_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_modifyTypeAnalysis(v_f_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_typeAnalysis_398_; lean_object* v_rewriteCache_399_; lean_object* v_acNfCache_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_424_; 
v___x_397_ = lean_st_ref_take(v_a_395_);
v_typeAnalysis_398_ = lean_ctor_get(v___x_397_, 2);
v_rewriteCache_399_ = lean_ctor_get(v___x_397_, 0);
v_acNfCache_400_ = lean_ctor_get(v___x_397_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_424_ == 0)
{
v___x_402_ = v___x_397_;
v_isShared_403_ = v_isSharedCheck_424_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_typeAnalysis_398_);
lean_inc(v_acNfCache_400_);
lean_inc(v_rewriteCache_399_);
lean_dec(v___x_397_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_424_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_interestingStructures_404_; lean_object* v_interestingEnums_405_; lean_object* v_interestingMatchers_406_; lean_object* v_uninteresting_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_423_; 
v_interestingStructures_404_ = lean_ctor_get(v_typeAnalysis_398_, 0);
v_interestingEnums_405_ = lean_ctor_get(v_typeAnalysis_398_, 1);
v_interestingMatchers_406_ = lean_ctor_get(v_typeAnalysis_398_, 2);
v_uninteresting_407_ = lean_ctor_get(v_typeAnalysis_398_, 3);
v_isSharedCheck_423_ = !lean_is_exclusive(v_typeAnalysis_398_);
if (v_isSharedCheck_423_ == 0)
{
v___x_409_ = v_typeAnalysis_398_;
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_uninteresting_407_);
lean_inc(v_interestingMatchers_406_);
lean_inc(v_interestingEnums_405_);
lean_inc(v_interestingStructures_404_);
lean_dec(v_typeAnalysis_398_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_411_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_412_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_413_ = lean_box(0);
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_411_, v___x_412_, v_interestingStructures_404_, v_n_394_, v___x_413_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_414_);
v___x_416_ = v___x_409_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_interestingEnums_405_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_interestingMatchers_406_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_uninteresting_407_);
v___x_416_ = v_reuseFailAlloc_422_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 2, v___x_416_);
v___x_418_ = v___x_402_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_rewriteCache_399_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_acNfCache_400_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v___x_416_);
v___x_418_ = v_reuseFailAlloc_421_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_st_ref_set(v_a_395_, v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_413_);
return v___x_420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_425_, v_a_426_);
lean_dec(v_a_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; lean_object* v_typeAnalysis_438_; lean_object* v_rewriteCache_439_; lean_object* v_acNfCache_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_464_; 
v___x_437_ = lean_st_ref_take(v_a_431_);
v_typeAnalysis_438_ = lean_ctor_get(v___x_437_, 2);
v_rewriteCache_439_ = lean_ctor_get(v___x_437_, 0);
v_acNfCache_440_ = lean_ctor_get(v___x_437_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_464_ == 0)
{
v___x_442_ = v___x_437_;
v_isShared_443_ = v_isSharedCheck_464_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_typeAnalysis_438_);
lean_inc(v_acNfCache_440_);
lean_inc(v_rewriteCache_439_);
lean_dec(v___x_437_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_464_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v_interestingStructures_444_; lean_object* v_interestingEnums_445_; lean_object* v_interestingMatchers_446_; lean_object* v_uninteresting_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_463_; 
v_interestingStructures_444_ = lean_ctor_get(v_typeAnalysis_438_, 0);
v_interestingEnums_445_ = lean_ctor_get(v_typeAnalysis_438_, 1);
v_interestingMatchers_446_ = lean_ctor_get(v_typeAnalysis_438_, 2);
v_uninteresting_447_ = lean_ctor_get(v_typeAnalysis_438_, 3);
v_isSharedCheck_463_ = !lean_is_exclusive(v_typeAnalysis_438_);
if (v_isSharedCheck_463_ == 0)
{
v___x_449_ = v_typeAnalysis_438_;
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_uninteresting_447_);
lean_inc(v_interestingMatchers_446_);
lean_inc(v_interestingEnums_445_);
lean_inc(v_interestingStructures_444_);
lean_dec(v_typeAnalysis_438_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_451_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_452_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_453_ = lean_box(0);
v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_451_, v___x_452_, v_interestingStructures_444_, v_n_429_, v___x_453_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_454_);
v___x_456_ = v___x_449_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_interestingEnums_445_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_interestingMatchers_446_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_uninteresting_447_);
v___x_456_ = v_reuseFailAlloc_462_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 2, v___x_456_);
v___x_458_ = v___x_442_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_rewriteCache_439_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_acNfCache_440_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v___x_456_);
v___x_458_ = v_reuseFailAlloc_461_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_st_ref_set(v_a_431_, v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_453_);
return v___x_460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingStructure(v_n_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; lean_object* v_typeAnalysis_478_; lean_object* v_rewriteCache_479_; lean_object* v_acNfCache_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_504_; 
v___x_477_ = lean_st_ref_take(v_a_475_);
v_typeAnalysis_478_ = lean_ctor_get(v___x_477_, 2);
v_rewriteCache_479_ = lean_ctor_get(v___x_477_, 0);
v_acNfCache_480_ = lean_ctor_get(v___x_477_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_504_ == 0)
{
v___x_482_ = v___x_477_;
v_isShared_483_ = v_isSharedCheck_504_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_typeAnalysis_478_);
lean_inc(v_acNfCache_480_);
lean_inc(v_rewriteCache_479_);
lean_dec(v___x_477_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_504_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_interestingStructures_484_; lean_object* v_interestingEnums_485_; lean_object* v_interestingMatchers_486_; lean_object* v_uninteresting_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_503_; 
v_interestingStructures_484_ = lean_ctor_get(v_typeAnalysis_478_, 0);
v_interestingEnums_485_ = lean_ctor_get(v_typeAnalysis_478_, 1);
v_interestingMatchers_486_ = lean_ctor_get(v_typeAnalysis_478_, 2);
v_uninteresting_487_ = lean_ctor_get(v_typeAnalysis_478_, 3);
v_isSharedCheck_503_ = !lean_is_exclusive(v_typeAnalysis_478_);
if (v_isSharedCheck_503_ == 0)
{
v___x_489_ = v_typeAnalysis_478_;
v_isShared_490_ = v_isSharedCheck_503_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_uninteresting_487_);
lean_inc(v_interestingMatchers_486_);
lean_inc(v_interestingEnums_485_);
lean_inc(v_interestingStructures_484_);
lean_dec(v_typeAnalysis_478_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_503_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_491_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_492_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_493_ = lean_box(0);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_491_, v___x_492_, v_interestingEnums_485_, v_n_474_, v___x_493_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_494_);
v___x_496_ = v___x_489_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_interestingStructures_484_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_interestingMatchers_486_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_uninteresting_487_);
v___x_496_ = v_reuseFailAlloc_502_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 2, v___x_496_);
v___x_498_ = v___x_482_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_rewriteCache_479_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_acNfCache_480_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v___x_496_);
v___x_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_st_ref_set(v_a_475_, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_493_);
return v___x_500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_505_, v_a_506_);
lean_dec(v_a_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_typeAnalysis_518_; lean_object* v_rewriteCache_519_; lean_object* v_acNfCache_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_544_; 
v___x_517_ = lean_st_ref_take(v_a_511_);
v_typeAnalysis_518_ = lean_ctor_get(v___x_517_, 2);
v_rewriteCache_519_ = lean_ctor_get(v___x_517_, 0);
v_acNfCache_520_ = lean_ctor_get(v___x_517_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_544_ == 0)
{
v___x_522_ = v___x_517_;
v_isShared_523_ = v_isSharedCheck_544_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_typeAnalysis_518_);
lean_inc(v_acNfCache_520_);
lean_inc(v_rewriteCache_519_);
lean_dec(v___x_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_544_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_interestingStructures_524_; lean_object* v_interestingEnums_525_; lean_object* v_interestingMatchers_526_; lean_object* v_uninteresting_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_543_; 
v_interestingStructures_524_ = lean_ctor_get(v_typeAnalysis_518_, 0);
v_interestingEnums_525_ = lean_ctor_get(v_typeAnalysis_518_, 1);
v_interestingMatchers_526_ = lean_ctor_get(v_typeAnalysis_518_, 2);
v_uninteresting_527_ = lean_ctor_get(v_typeAnalysis_518_, 3);
v_isSharedCheck_543_ = !lean_is_exclusive(v_typeAnalysis_518_);
if (v_isSharedCheck_543_ == 0)
{
v___x_529_ = v_typeAnalysis_518_;
v_isShared_530_ = v_isSharedCheck_543_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_uninteresting_527_);
lean_inc(v_interestingMatchers_526_);
lean_inc(v_interestingEnums_525_);
lean_inc(v_interestingStructures_524_);
lean_dec(v_typeAnalysis_518_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_543_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_531_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_532_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_533_ = lean_box(0);
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_531_, v___x_532_, v_interestingEnums_525_, v_n_509_, v___x_533_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v___x_534_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_interestingStructures_524_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_interestingMatchers_526_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_uninteresting_527_);
v___x_536_ = v_reuseFailAlloc_542_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 2, v___x_536_);
v___x_538_ = v___x_522_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_rewriteCache_519_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_acNfCache_520_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v___x_536_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_set(v_a_511_, v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_533_);
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingEnum(v_n_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_554_, lean_object* v_k_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_558_; lean_object* v_typeAnalysis_559_; lean_object* v_rewriteCache_560_; lean_object* v_acNfCache_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_585_; 
v___x_558_ = lean_st_ref_take(v_a_556_);
v_typeAnalysis_559_ = lean_ctor_get(v___x_558_, 2);
v_rewriteCache_560_ = lean_ctor_get(v___x_558_, 0);
v_acNfCache_561_ = lean_ctor_get(v___x_558_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_585_ == 0)
{
v___x_563_ = v___x_558_;
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_typeAnalysis_559_);
lean_inc(v_acNfCache_561_);
lean_inc(v_rewriteCache_560_);
lean_dec(v___x_558_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_interestingStructures_565_; lean_object* v_interestingEnums_566_; lean_object* v_interestingMatchers_567_; lean_object* v_uninteresting_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_584_; 
v_interestingStructures_565_ = lean_ctor_get(v_typeAnalysis_559_, 0);
v_interestingEnums_566_ = lean_ctor_get(v_typeAnalysis_559_, 1);
v_interestingMatchers_567_ = lean_ctor_get(v_typeAnalysis_559_, 2);
v_uninteresting_568_ = lean_ctor_get(v_typeAnalysis_559_, 3);
v_isSharedCheck_584_ = !lean_is_exclusive(v_typeAnalysis_559_);
if (v_isSharedCheck_584_ == 0)
{
v___x_570_ = v_typeAnalysis_559_;
v_isShared_571_ = v_isSharedCheck_584_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_uninteresting_568_);
lean_inc(v_interestingMatchers_567_);
lean_inc(v_interestingEnums_566_);
lean_inc(v_interestingStructures_565_);
lean_dec(v_typeAnalysis_559_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_584_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_572_, v___x_573_, v_interestingMatchers_567_, v_n_554_, v_k_555_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v___x_574_);
v___x_576_ = v___x_570_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_interestingStructures_565_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_interestingEnums_566_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_uninteresting_568_);
v___x_576_ = v_reuseFailAlloc_583_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 2, v___x_576_);
v___x_578_ = v___x_563_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_rewriteCache_560_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_acNfCache_561_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v___x_576_);
v___x_578_ = v_reuseFailAlloc_582_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_st_ref_set(v_a_556_, v___x_578_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_586_, lean_object* v_k_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_586_, v_k_587_, v_a_588_);
lean_dec(v_a_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_591_, lean_object* v_k_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_600_; lean_object* v_typeAnalysis_601_; lean_object* v_rewriteCache_602_; lean_object* v_acNfCache_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_627_; 
v___x_600_ = lean_st_ref_take(v_a_594_);
v_typeAnalysis_601_ = lean_ctor_get(v___x_600_, 2);
v_rewriteCache_602_ = lean_ctor_get(v___x_600_, 0);
v_acNfCache_603_ = lean_ctor_get(v___x_600_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_627_ == 0)
{
v___x_605_ = v___x_600_;
v_isShared_606_ = v_isSharedCheck_627_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_typeAnalysis_601_);
lean_inc(v_acNfCache_603_);
lean_inc(v_rewriteCache_602_);
lean_dec(v___x_600_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_627_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_interestingStructures_607_; lean_object* v_interestingEnums_608_; lean_object* v_interestingMatchers_609_; lean_object* v_uninteresting_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_626_; 
v_interestingStructures_607_ = lean_ctor_get(v_typeAnalysis_601_, 0);
v_interestingEnums_608_ = lean_ctor_get(v_typeAnalysis_601_, 1);
v_interestingMatchers_609_ = lean_ctor_get(v_typeAnalysis_601_, 2);
v_uninteresting_610_ = lean_ctor_get(v_typeAnalysis_601_, 3);
v_isSharedCheck_626_ = !lean_is_exclusive(v_typeAnalysis_601_);
if (v_isSharedCheck_626_ == 0)
{
v___x_612_ = v_typeAnalysis_601_;
v_isShared_613_ = v_isSharedCheck_626_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_uninteresting_610_);
lean_inc(v_interestingMatchers_609_);
lean_inc(v_interestingEnums_608_);
lean_inc(v_interestingStructures_607_);
lean_dec(v_typeAnalysis_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_626_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_614_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_615_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_614_, v___x_615_, v_interestingMatchers_609_, v_n_591_, v_k_592_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 2, v___x_616_);
v___x_618_ = v___x_612_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_interestingStructures_607_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_interestingEnums_608_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_uninteresting_610_);
v___x_618_ = v_reuseFailAlloc_625_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 2, v___x_618_);
v___x_620_ = v___x_605_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_rewriteCache_602_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_acNfCache_603_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v___x_618_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_st_ref_set(v_a_594_, v___x_620_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_628_, lean_object* v_k_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markInterestingMatcher(v_n_628_, v_k_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; lean_object* v_typeAnalysis_642_; lean_object* v_rewriteCache_643_; lean_object* v_acNfCache_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_668_; 
v___x_641_ = lean_st_ref_take(v_a_639_);
v_typeAnalysis_642_ = lean_ctor_get(v___x_641_, 2);
v_rewriteCache_643_ = lean_ctor_get(v___x_641_, 0);
v_acNfCache_644_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_668_ == 0)
{
v___x_646_ = v___x_641_;
v_isShared_647_ = v_isSharedCheck_668_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_typeAnalysis_642_);
lean_inc(v_acNfCache_644_);
lean_inc(v_rewriteCache_643_);
lean_dec(v___x_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_668_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_interestingStructures_648_; lean_object* v_interestingEnums_649_; lean_object* v_interestingMatchers_650_; lean_object* v_uninteresting_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_667_; 
v_interestingStructures_648_ = lean_ctor_get(v_typeAnalysis_642_, 0);
v_interestingEnums_649_ = lean_ctor_get(v_typeAnalysis_642_, 1);
v_interestingMatchers_650_ = lean_ctor_get(v_typeAnalysis_642_, 2);
v_uninteresting_651_ = lean_ctor_get(v_typeAnalysis_642_, 3);
v_isSharedCheck_667_ = !lean_is_exclusive(v_typeAnalysis_642_);
if (v_isSharedCheck_667_ == 0)
{
v___x_653_ = v_typeAnalysis_642_;
v_isShared_654_ = v_isSharedCheck_667_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_uninteresting_651_);
lean_inc(v_interestingMatchers_650_);
lean_inc(v_interestingEnums_649_);
lean_inc(v_interestingStructures_648_);
lean_dec(v_typeAnalysis_642_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_667_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_655_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_656_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_657_ = lean_box(0);
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_655_, v___x_656_, v_uninteresting_651_, v_n_638_, v___x_657_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 3, v___x_658_);
v___x_660_ = v___x_653_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_interestingStructures_648_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_interestingEnums_649_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_interestingMatchers_650_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v___x_658_);
v___x_660_ = v_reuseFailAlloc_666_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 2, v___x_660_);
v___x_662_ = v___x_646_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_rewriteCache_643_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_acNfCache_644_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v___x_660_);
v___x_662_ = v_reuseFailAlloc_665_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_st_ref_set(v_a_639_, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_657_);
return v___x_664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_669_, v_a_670_);
lean_dec(v_a_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; lean_object* v_typeAnalysis_682_; lean_object* v_rewriteCache_683_; lean_object* v_acNfCache_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_708_; 
v___x_681_ = lean_st_ref_take(v_a_675_);
v_typeAnalysis_682_ = lean_ctor_get(v___x_681_, 2);
v_rewriteCache_683_ = lean_ctor_get(v___x_681_, 0);
v_acNfCache_684_ = lean_ctor_get(v___x_681_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_708_ == 0)
{
v___x_686_ = v___x_681_;
v_isShared_687_ = v_isSharedCheck_708_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_typeAnalysis_682_);
lean_inc(v_acNfCache_684_);
lean_inc(v_rewriteCache_683_);
lean_dec(v___x_681_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_708_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_interestingStructures_688_; lean_object* v_interestingEnums_689_; lean_object* v_interestingMatchers_690_; lean_object* v_uninteresting_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_707_; 
v_interestingStructures_688_ = lean_ctor_get(v_typeAnalysis_682_, 0);
v_interestingEnums_689_ = lean_ctor_get(v_typeAnalysis_682_, 1);
v_interestingMatchers_690_ = lean_ctor_get(v_typeAnalysis_682_, 2);
v_uninteresting_691_ = lean_ctor_get(v_typeAnalysis_682_, 3);
v_isSharedCheck_707_ = !lean_is_exclusive(v_typeAnalysis_682_);
if (v_isSharedCheck_707_ == 0)
{
v___x_693_ = v_typeAnalysis_682_;
v_isShared_694_ = v_isSharedCheck_707_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_uninteresting_691_);
lean_inc(v_interestingMatchers_690_);
lean_inc(v_interestingEnums_689_);
lean_inc(v_interestingStructures_688_);
lean_dec(v_typeAnalysis_682_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_707_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_695_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_696_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_697_ = lean_box(0);
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_695_, v___x_696_, v_uninteresting_691_, v_n_673_, v___x_697_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 3, v___x_698_);
v___x_700_ = v___x_693_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_interestingStructures_688_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_interestingEnums_689_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_interestingMatchers_690_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v___x_698_);
v___x_700_ = v_reuseFailAlloc_706_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 2, v___x_700_);
v___x_702_ = v___x_686_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_rewriteCache_683_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_acNfCache_684_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v___x_700_);
v___x_702_ = v_reuseFailAlloc_705_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_st_ref_set(v_a_675_, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_697_);
return v___x_704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_markUninterestingConst(v_n_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_717_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0);
v___x_720_ = l_ReaderT_instMonad___redArg(v___x_719_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_box(0);
v___x_727_ = lean_unsigned_to_nat(16u);
v___x_728_ = lean_mk_array(v___x_727_, v___x_726_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__8(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__7);
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__8);
v___x_733_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
lean_ctor_set(v___x_733_, 3, v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg(lean_object* v_cfg_734_, lean_object* v_goal_735_, lean_object* v_x_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_toApplicative_743_; lean_object* v_toFunctor_744_; lean_object* v_toSeq_745_; lean_object* v_toSeqLeft_746_; lean_object* v_toSeqRight_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_858_; 
v___x_742_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc_ref(v_toApplicative_743_);
v_toFunctor_744_ = lean_ctor_get(v_toApplicative_743_, 0);
v_toSeq_745_ = lean_ctor_get(v_toApplicative_743_, 2);
v_toSeqLeft_746_ = lean_ctor_get(v_toApplicative_743_, 3);
v_toSeqRight_747_ = lean_ctor_get(v_toApplicative_743_, 4);
v_isSharedCheck_858_ = !lean_is_exclusive(v_toApplicative_743_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_toApplicative_743_, 1);
lean_dec(v_unused_859_);
v___x_749_ = v_toApplicative_743_;
v_isShared_750_ = v_isSharedCheck_858_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_toSeqRight_747_);
lean_inc(v_toSeqLeft_746_);
lean_inc(v_toSeq_745_);
lean_inc(v_toFunctor_744_);
lean_dec(v_toApplicative_743_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_858_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___x_760_; 
v___f_751_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2));
v___f_752_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3));
lean_inc_ref(v_toFunctor_744_);
v___f_753_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_753_, 0, v_toFunctor_744_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_754_, 0, v_toFunctor_744_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___f_753_);
lean_ctor_set(v___x_755_, 1, v___f_754_);
v___f_756_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_756_, 0, v_toSeqRight_747_);
v___f_757_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_757_, 0, v_toSeqLeft_746_);
v___f_758_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_758_, 0, v_toSeq_745_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 4, v___f_756_);
lean_ctor_set(v___x_749_, 3, v___f_757_);
lean_ctor_set(v___x_749_, 2, v___f_758_);
lean_ctor_set(v___x_749_, 1, v___f_751_);
lean_ctor_set(v___x_749_, 0, v___x_755_);
v___x_760_ = v___x_749_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___f_751_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v___f_758_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v___f_757_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v___f_756_);
v___x_760_ = v_reuseFailAlloc_857_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_toApplicative_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_855_; 
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___f_752_);
v___x_762_ = l_ReaderT_instMonad___redArg(v___x_761_);
v_toApplicative_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v___x_762_, 1);
lean_dec(v_unused_856_);
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_855_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_toApplicative_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_855_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_toFunctor_767_; lean_object* v_toSeq_768_; lean_object* v_toSeqLeft_769_; lean_object* v_toSeqRight_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_853_; 
v_toFunctor_767_ = lean_ctor_get(v_toApplicative_763_, 0);
v_toSeq_768_ = lean_ctor_get(v_toApplicative_763_, 2);
v_toSeqLeft_769_ = lean_ctor_get(v_toApplicative_763_, 3);
v_toSeqRight_770_ = lean_ctor_get(v_toApplicative_763_, 4);
v_isSharedCheck_853_ = !lean_is_exclusive(v_toApplicative_763_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_toApplicative_763_, 1);
lean_dec(v_unused_854_);
v___x_772_ = v_toApplicative_763_;
v_isShared_773_ = v_isSharedCheck_853_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_toSeqRight_770_);
lean_inc(v_toSeqLeft_769_);
lean_inc(v_toSeq_768_);
lean_inc(v_toFunctor_767_);
lean_dec(v_toApplicative_763_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_853_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___f_779_; lean_object* v___f_780_; lean_object* v___f_781_; lean_object* v___x_783_; 
v___f_774_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4));
v___f_775_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5));
lean_inc_ref(v_toFunctor_767_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_776_, 0, v_toFunctor_767_);
v___f_777_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_777_, 0, v_toFunctor_767_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___f_776_);
lean_ctor_set(v___x_778_, 1, v___f_777_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_779_, 0, v_toSeqRight_770_);
v___f_780_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_780_, 0, v_toSeqLeft_769_);
v___f_781_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_781_, 0, v_toSeq_768_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v___f_779_);
lean_ctor_set(v___x_772_, 3, v___f_780_);
lean_ctor_set(v___x_772_, 2, v___f_781_);
lean_ctor_set(v___x_772_, 1, v___f_774_);
lean_ctor_set(v___x_772_, 0, v___x_778_);
v___x_783_ = v___x_772_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___f_774_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v___f_781_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v___f_780_);
lean_ctor_set(v_reuseFailAlloc_852_, 4, v___f_779_);
v___x_783_ = v_reuseFailAlloc_852_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___f_775_);
lean_ctor_set(v___x_765_, 0, v___x_783_);
v___x_785_ = v___x_765_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___f_775_);
v___x_785_ = v_reuseFailAlloc_851_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v_toApplicative_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_849_; 
v_toApplicative_786_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_742_, 1);
lean_dec(v_unused_850_);
v___x_788_ = v___x_742_;
v_isShared_789_ = v_isSharedCheck_849_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_toApplicative_786_);
lean_dec(v___x_742_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_849_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_toFunctor_790_; lean_object* v_toSeq_791_; lean_object* v_toSeqLeft_792_; lean_object* v_toSeqRight_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_847_; 
v_toFunctor_790_ = lean_ctor_get(v_toApplicative_786_, 0);
v_toSeq_791_ = lean_ctor_get(v_toApplicative_786_, 2);
v_toSeqLeft_792_ = lean_ctor_get(v_toApplicative_786_, 3);
v_toSeqRight_793_ = lean_ctor_get(v_toApplicative_786_, 4);
v_isSharedCheck_847_ = !lean_is_exclusive(v_toApplicative_786_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v_toApplicative_786_, 1);
lean_dec(v_unused_848_);
v___x_795_ = v_toApplicative_786_;
v_isShared_796_ = v_isSharedCheck_847_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_toSeqRight_793_);
lean_inc(v_toSeqLeft_792_);
lean_inc(v_toSeq_791_);
lean_inc(v_toFunctor_790_);
lean_dec(v_toApplicative_786_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_847_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_804_; 
lean_inc_ref(v_toFunctor_790_);
v___f_797_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_797_, 0, v_toFunctor_790_);
v___f_798_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_798_, 0, v_toFunctor_790_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___f_797_);
lean_ctor_set(v___x_799_, 1, v___f_798_);
v___f_800_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_800_, 0, v_toSeqRight_793_);
v___f_801_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_801_, 0, v_toSeqLeft_792_);
v___f_802_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_802_, 0, v_toSeq_791_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v___f_800_);
lean_ctor_set(v___x_795_, 3, v___f_801_);
lean_ctor_set(v___x_795_, 2, v___f_802_);
lean_ctor_set(v___x_795_, 1, v___f_751_);
lean_ctor_set(v___x_795_, 0, v___x_799_);
v___x_804_ = v___x_795_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___f_751_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v___f_802_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v___f_801_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v___f_800_);
v___x_804_ = v_reuseFailAlloc_846_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___f_752_);
lean_ctor_set(v___x_788_, 0, v___x_804_);
v___x_806_ = v___x_788_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___f_752_);
v___x_806_ = v_reuseFailAlloc_845_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_668__overap_811_; lean_object* v___x_812_; 
v___x_807_ = l_ReaderT_instMonad___redArg(v___x_806_);
v___x_808_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_808_, 0, lean_box(0));
lean_closure_set(v___x_808_, 1, lean_box(0));
lean_closure_set(v___x_808_, 2, v___x_807_);
v___x_809_ = l_instMonadControlTOfPure___redArg(v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6));
v___x_668__overap_811_ = l_Lean_MVarId_withContext___redArg(v___x_809_, v___x_785_, v_goal_735_, v___x_810_);
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
v___x_812_ = lean_apply_5(v___x_668__overap_811_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, lean_box(0));
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_812_);
v___x_814_ = lean_array_get_size(v_a_813_);
lean_dec(v_a_813_);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_unsigned_to_nat(4u);
v___x_817_ = lean_nat_mul(v___x_814_, v___x_816_);
v___x_818_ = lean_unsigned_to_nat(3u);
v___x_819_ = lean_nat_div(v___x_817_, v___x_818_);
lean_dec(v___x_817_);
v___x_820_ = l_Nat_nextPowerOfTwo(v___x_819_);
lean_dec(v___x_819_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_mk_array(v___x_820_, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_815_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9);
lean_inc_ref(v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_823_);
lean_ctor_set(v___x_825_, 2, v___x_824_);
v___x_826_ = lean_st_mk_ref(v___x_825_);
lean_inc(v___x_826_);
v___x_827_ = lean_apply_7(v_x_736_, v_cfg_734_, v___x_826_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, lean_box(0));
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_836_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_st_ref_get(v___x_826_);
lean_dec(v___x_826_);
lean_dec(v___x_832_);
if (v_isShared_831_ == 0)
{
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_828_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_dec(v___x_826_);
return v___x_827_;
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_x_736_);
lean_dec_ref(v_cfg_734_);
v_a_837_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_812_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_812_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_cfg_860_, lean_object* v_goal_861_, lean_object* v_x_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg(v_cfg_860_, v_goal_861_, v_x_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run(lean_object* v_00_u03b1_869_, lean_object* v_cfg_870_, lean_object* v_goal_871_, lean_object* v_x_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_878_; lean_object* v_toApplicative_879_; lean_object* v_toFunctor_880_; lean_object* v_toSeq_881_; lean_object* v_toSeqLeft_882_; lean_object* v_toSeqRight_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_994_; 
v___x_878_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc_ref(v_toApplicative_879_);
v_toFunctor_880_ = lean_ctor_get(v_toApplicative_879_, 0);
v_toSeq_881_ = lean_ctor_get(v_toApplicative_879_, 2);
v_toSeqLeft_882_ = lean_ctor_get(v_toApplicative_879_, 3);
v_toSeqRight_883_ = lean_ctor_get(v_toApplicative_879_, 4);
v_isSharedCheck_994_ = !lean_is_exclusive(v_toApplicative_879_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v_toApplicative_879_, 1);
lean_dec(v_unused_995_);
v___x_885_ = v_toApplicative_879_;
v_isShared_886_ = v_isSharedCheck_994_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_toSeqRight_883_);
lean_inc(v_toSeqLeft_882_);
lean_inc(v_toSeq_881_);
lean_inc(v_toFunctor_880_);
lean_dec(v_toApplicative_879_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_994_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___f_892_; lean_object* v___f_893_; lean_object* v___f_894_; lean_object* v___x_896_; 
v___f_887_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2));
v___f_888_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3));
lean_inc_ref(v_toFunctor_880_);
v___f_889_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_889_, 0, v_toFunctor_880_);
v___f_890_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_890_, 0, v_toFunctor_880_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___f_889_);
lean_ctor_set(v___x_891_, 1, v___f_890_);
v___f_892_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_892_, 0, v_toSeqRight_883_);
v___f_893_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_893_, 0, v_toSeqLeft_882_);
v___f_894_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_894_, 0, v_toSeq_881_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 4, v___f_892_);
lean_ctor_set(v___x_885_, 3, v___f_893_);
lean_ctor_set(v___x_885_, 2, v___f_894_);
lean_ctor_set(v___x_885_, 1, v___f_887_);
lean_ctor_set(v___x_885_, 0, v___x_891_);
v___x_896_ = v___x_885_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___f_887_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v___f_894_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v___f_893_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v___f_892_);
v___x_896_ = v_reuseFailAlloc_993_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_toApplicative_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_991_; 
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___f_888_);
v___x_898_ = l_ReaderT_instMonad___redArg(v___x_897_);
v_toApplicative_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_898_, 1);
lean_dec(v_unused_992_);
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_991_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_toApplicative_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_991_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_toFunctor_903_; lean_object* v_toSeq_904_; lean_object* v_toSeqLeft_905_; lean_object* v_toSeqRight_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_989_; 
v_toFunctor_903_ = lean_ctor_get(v_toApplicative_899_, 0);
v_toSeq_904_ = lean_ctor_get(v_toApplicative_899_, 2);
v_toSeqLeft_905_ = lean_ctor_get(v_toApplicative_899_, 3);
v_toSeqRight_906_ = lean_ctor_get(v_toApplicative_899_, 4);
v_isSharedCheck_989_ = !lean_is_exclusive(v_toApplicative_899_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_toApplicative_899_, 1);
lean_dec(v_unused_990_);
v___x_908_ = v_toApplicative_899_;
v_isShared_909_ = v_isSharedCheck_989_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_toSeqRight_906_);
lean_inc(v_toSeqLeft_905_);
lean_inc(v_toSeq_904_);
lean_inc(v_toFunctor_903_);
lean_dec(v_toApplicative_899_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_989_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___f_916_; lean_object* v___f_917_; lean_object* v___x_919_; 
v___f_910_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4));
v___f_911_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5));
lean_inc_ref(v_toFunctor_903_);
v___f_912_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_912_, 0, v_toFunctor_903_);
v___f_913_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_913_, 0, v_toFunctor_903_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___f_912_);
lean_ctor_set(v___x_914_, 1, v___f_913_);
v___f_915_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_915_, 0, v_toSeqRight_906_);
v___f_916_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_916_, 0, v_toSeqLeft_905_);
v___f_917_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_917_, 0, v_toSeq_904_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 4, v___f_915_);
lean_ctor_set(v___x_908_, 3, v___f_916_);
lean_ctor_set(v___x_908_, 2, v___f_917_);
lean_ctor_set(v___x_908_, 1, v___f_910_);
lean_ctor_set(v___x_908_, 0, v___x_914_);
v___x_919_ = v___x_908_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___f_910_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v___f_917_);
lean_ctor_set(v_reuseFailAlloc_988_, 3, v___f_916_);
lean_ctor_set(v_reuseFailAlloc_988_, 4, v___f_915_);
v___x_919_ = v_reuseFailAlloc_988_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___f_911_);
lean_ctor_set(v___x_901_, 0, v___x_919_);
v___x_921_ = v___x_901_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___f_911_);
v___x_921_ = v_reuseFailAlloc_987_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v_toApplicative_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_985_; 
v_toApplicative_922_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; 
v_unused_986_ = lean_ctor_get(v___x_878_, 1);
lean_dec(v_unused_986_);
v___x_924_ = v___x_878_;
v_isShared_925_ = v_isSharedCheck_985_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_toApplicative_922_);
lean_dec(v___x_878_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_985_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_toFunctor_926_; lean_object* v_toSeq_927_; lean_object* v_toSeqLeft_928_; lean_object* v_toSeqRight_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_983_; 
v_toFunctor_926_ = lean_ctor_get(v_toApplicative_922_, 0);
v_toSeq_927_ = lean_ctor_get(v_toApplicative_922_, 2);
v_toSeqLeft_928_ = lean_ctor_get(v_toApplicative_922_, 3);
v_toSeqRight_929_ = lean_ctor_get(v_toApplicative_922_, 4);
v_isSharedCheck_983_ = !lean_is_exclusive(v_toApplicative_922_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v_toApplicative_922_, 1);
lean_dec(v_unused_984_);
v___x_931_ = v_toApplicative_922_;
v_isShared_932_ = v_isSharedCheck_983_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_toSeqRight_929_);
lean_inc(v_toSeqLeft_928_);
lean_inc(v_toSeq_927_);
lean_inc(v_toFunctor_926_);
lean_dec(v_toApplicative_922_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_983_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___f_933_; lean_object* v___f_934_; lean_object* v___x_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___f_938_; lean_object* v___x_940_; 
lean_inc_ref(v_toFunctor_926_);
v___f_933_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_933_, 0, v_toFunctor_926_);
v___f_934_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_934_, 0, v_toFunctor_926_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___f_933_);
lean_ctor_set(v___x_935_, 1, v___f_934_);
v___f_936_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_936_, 0, v_toSeqRight_929_);
v___f_937_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_937_, 0, v_toSeqLeft_928_);
v___f_938_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_938_, 0, v_toSeq_927_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___f_936_);
lean_ctor_set(v___x_931_, 3, v___f_937_);
lean_ctor_set(v___x_931_, 2, v___f_938_);
lean_ctor_set(v___x_931_, 1, v___f_887_);
lean_ctor_set(v___x_931_, 0, v___x_935_);
v___x_940_ = v___x_931_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___f_887_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v___f_938_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v___f_937_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v___f_936_);
v___x_940_ = v_reuseFailAlloc_982_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___f_888_);
lean_ctor_set(v___x_924_, 0, v___x_940_);
v___x_942_ = v___x_924_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___f_888_);
v___x_942_ = v_reuseFailAlloc_981_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_896__overap_947_; lean_object* v___x_948_; 
v___x_943_ = l_ReaderT_instMonad___redArg(v___x_942_);
v___x_944_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_944_, 0, lean_box(0));
lean_closure_set(v___x_944_, 1, lean_box(0));
lean_closure_set(v___x_944_, 2, v___x_943_);
v___x_945_ = l_instMonadControlTOfPure___redArg(v___x_944_);
v___x_946_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6));
v___x_896__overap_947_ = l_Lean_MVarId_withContext___redArg(v___x_945_, v___x_921_, v_goal_871_, v___x_946_);
lean_inc(v_a_876_);
lean_inc_ref(v_a_875_);
lean_inc(v_a_874_);
lean_inc_ref(v_a_873_);
v___x_948_ = lean_apply_5(v___x_896__overap_947_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, lean_box(0));
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v___x_948_);
v___x_950_ = lean_array_get_size(v_a_949_);
lean_dec(v_a_949_);
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = lean_unsigned_to_nat(4u);
v___x_953_ = lean_nat_mul(v___x_950_, v___x_952_);
v___x_954_ = lean_unsigned_to_nat(3u);
v___x_955_ = lean_nat_div(v___x_953_, v___x_954_);
lean_dec(v___x_953_);
v___x_956_ = l_Nat_nextPowerOfTwo(v___x_955_);
lean_dec(v___x_955_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_mk_array(v___x_956_, v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_951_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9);
lean_inc_ref(v___x_959_);
v___x_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_959_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
v___x_962_ = lean_st_mk_ref(v___x_961_);
lean_inc(v___x_962_);
v___x_963_ = lean_apply_7(v_x_872_, v_cfg_870_, v___x_962_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, lean_box(0));
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_st_ref_get(v___x_962_);
lean_dec(v___x_962_);
lean_dec(v___x_968_);
if (v_isShared_967_ == 0)
{
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_964_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_dec(v___x_962_);
return v___x_963_;
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec_ref(v_x_872_);
lean_dec_ref(v_cfg_870_);
v_a_973_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_948_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_948_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_996_, lean_object* v_cfg_997_, lean_object* v_goal_998_, lean_object* v_x_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run(v_00_u03b1_996_, v_cfg_997_, v_goal_998_, v_x_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v_res_1005_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__0));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__2));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0(lean_object* v_name_1012_, lean_object* v_goal_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1022_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1);
v___x_1023_ = l_Lean_MessageData_ofName(v_name_1012_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_goal_1013_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_1030_, lean_object* v_goal_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0(v_name_1030_, v_goal_1031_, v_x_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_x_1032_);
return v_res_1040_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1044_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1045_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1044_, v___x_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2);
v___f_1047_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___x_1048_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1047_, v___x_1046_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3);
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1051_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1050_, v___x_1049_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4);
v___f_1053_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___x_1054_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1053_, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; 
v___x_1056_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___f_1058_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6));
v___x_1059_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1058_, v___x_1057_, v___x_1056_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; 
v___x_1060_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7);
v___f_1061_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1062_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6));
v___x_1063_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1062_, v___f_1061_, v___x_1060_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; 
v___x_1064_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8);
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___f_1066_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6));
v___x_1067_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1066_, v___x_1065_, v___x_1064_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
v___x_1068_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9);
v___f_1069_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1070_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6));
v___x_1071_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1070_, v___f_1069_, v___x_1068_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_instMonadExceptOfEST(lean_box(0), lean_box(0));
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11);
v___x_1074_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12);
v___x_1076_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13);
v___x_1078_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14);
v___x_1080_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15);
v___x_1082_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16);
v___x_1084_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___f_1103_; 
v___x_1101_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1102_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1103_, 0, v___x_1102_);
lean_closure_set(v___f_1103_, 1, v___x_1101_);
return v___f_1103_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28(void){
_start:
{
lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___f_1106_; 
v___f_1104_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1105_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27);
v___f_1106_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1106_, 0, v___f_1105_);
lean_closure_set(v___f_1106_, 1, v___f_1104_);
return v___f_1106_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31(void){
_start:
{
lean_object* v___x_1109_; double v___x_1110_; 
v___x_1109_ = lean_unsigned_to_nat(1000000000u);
v___x_1110_ = lean_float_of_nat(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run(lean_object* v_pass_1111_, lean_object* v_goal_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v_toApplicative_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1302_; 
v___x_1120_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v___x_1120_, 1);
lean_dec(v_unused_1303_);
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1302_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_toApplicative_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1302_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_toFunctor_1125_; lean_object* v_toSeq_1126_; lean_object* v_toSeqLeft_1127_; lean_object* v_toSeqRight_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1300_; 
v_toFunctor_1125_ = lean_ctor_get(v_toApplicative_1121_, 0);
v_toSeq_1126_ = lean_ctor_get(v_toApplicative_1121_, 2);
v_toSeqLeft_1127_ = lean_ctor_get(v_toApplicative_1121_, 3);
v_toSeqRight_1128_ = lean_ctor_get(v_toApplicative_1121_, 4);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_toApplicative_1121_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v_toApplicative_1121_, 1);
lean_dec(v_unused_1301_);
v___x_1130_ = v_toApplicative_1121_;
v_isShared_1131_ = v_isSharedCheck_1300_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_toSeqRight_1128_);
lean_inc(v_toSeqLeft_1127_);
lean_inc(v_toSeq_1126_);
lean_inc(v_toFunctor_1125_);
lean_dec(v_toApplicative_1121_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1300_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___f_1139_; lean_object* v___x_1141_; 
v___f_1132_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2));
v___f_1133_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3));
lean_inc_ref(v_toFunctor_1125_);
v___f_1134_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1134_, 0, v_toFunctor_1125_);
v___f_1135_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1135_, 0, v_toFunctor_1125_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___f_1134_);
lean_ctor_set(v___x_1136_, 1, v___f_1135_);
v___f_1137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1137_, 0, v_toSeqRight_1128_);
v___f_1138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1138_, 0, v_toSeqLeft_1127_);
v___f_1139_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1139_, 0, v_toSeq_1126_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v___f_1137_);
lean_ctor_set(v___x_1130_, 3, v___f_1138_);
lean_ctor_set(v___x_1130_, 2, v___f_1139_);
lean_ctor_set(v___x_1130_, 1, v___f_1132_);
lean_ctor_set(v___x_1130_, 0, v___x_1136_);
v___x_1141_ = v___x_1130_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___f_1132_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v___f_1139_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v___f_1138_);
lean_ctor_set(v_reuseFailAlloc_1299_, 4, v___f_1137_);
v___x_1141_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v___f_1133_);
lean_ctor_set(v___x_1123_, 0, v___x_1141_);
v___x_1143_ = v___x_1123_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___f_1133_);
v___x_1143_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v_toApplicative_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1296_; 
v___x_1144_ = l_ReaderT_instMonad___redArg(v___x_1143_);
v_toApplicative_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v___x_1144_, 1);
lean_dec(v_unused_1297_);
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1296_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_toApplicative_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1296_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_toFunctor_1149_; lean_object* v_toSeq_1150_; lean_object* v_toSeqLeft_1151_; lean_object* v_toSeqRight_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1294_; 
v_toFunctor_1149_ = lean_ctor_get(v_toApplicative_1145_, 0);
v_toSeq_1150_ = lean_ctor_get(v_toApplicative_1145_, 2);
v_toSeqLeft_1151_ = lean_ctor_get(v_toApplicative_1145_, 3);
v_toSeqRight_1152_ = lean_ctor_get(v_toApplicative_1145_, 4);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_toApplicative_1145_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_toApplicative_1145_, 1);
lean_dec(v_unused_1295_);
v___x_1154_ = v_toApplicative_1145_;
v_isShared_1155_ = v_isSharedCheck_1294_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_toSeqRight_1152_);
lean_inc(v_toSeqLeft_1151_);
lean_inc(v_toSeq_1150_);
lean_inc(v_toFunctor_1149_);
lean_dec(v_toApplicative_1145_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1294_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___f_1156_; lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___x_1165_; 
v___f_1156_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4));
v___f_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5));
lean_inc_ref(v_toFunctor_1149_);
v___f_1158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1158_, 0, v_toFunctor_1149_);
v___f_1159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1159_, 0, v_toFunctor_1149_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___f_1158_);
lean_ctor_set(v___x_1160_, 1, v___f_1159_);
v___f_1161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1161_, 0, v_toSeqRight_1152_);
v___f_1162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1162_, 0, v_toSeqLeft_1151_);
v___f_1163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1163_, 0, v_toSeq_1150_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 4, v___f_1161_);
lean_ctor_set(v___x_1154_, 3, v___f_1162_);
lean_ctor_set(v___x_1154_, 2, v___f_1163_);
lean_ctor_set(v___x_1154_, 1, v___f_1156_);
lean_ctor_set(v___x_1154_, 0, v___x_1160_);
v___x_1165_ = v___x_1154_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___f_1156_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v___f_1163_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v___f_1162_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v___f_1161_);
v___x_1165_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___f_1157_);
lean_ctor_set(v___x_1147_, 0, v___x_1165_);
v___x_1167_ = v___x_1147_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v___f_1157_);
v___x_1167_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_toMonadRef_1172_; lean_object* v___x_1173_; lean_object* v_options_1174_; uint8_t v_hasTrace_1175_; 
v___x_1168_ = l_ReaderT_instMonad___redArg(v___x_1167_);
v___x_1169_ = l_ReaderT_instMonad___redArg(v___x_1168_);
v___x_1170_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5);
v___x_1171_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10);
v_toMonadRef_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc_ref(v_toMonadRef_1172_);
v___x_1173_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17);
v_options_1174_ = lean_ctor_get(v_a_1117_, 2);
v_hasTrace_1175_ = lean_ctor_get_uint8(v_options_1174_, sizeof(void*)*1);
if (v_hasTrace_1175_ == 0)
{
lean_object* v_run_x27_1176_; lean_object* v___x_1177_; 
lean_dec_ref(v_toMonadRef_1172_);
lean_dec_ref(v___x_1169_);
v_run_x27_1176_ = lean_ctor_get(v_pass_1111_, 1);
lean_inc_ref(v_run_x27_1176_);
lean_dec_ref(v_pass_1111_);
v___x_1177_ = lean_apply_8(v_run_x27_1176_, v_goal_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
return v___x_1177_;
}
else
{
lean_object* v_name_1178_; lean_object* v_run_x27_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1291_; 
v_name_1178_ = lean_ctor_get(v_pass_1111_, 0);
v_run_x27_1179_ = lean_ctor_get(v_pass_1111_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_pass_1111_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1181_ = v_pass_1111_;
v_isShared_1182_ = v_isSharedCheck_1291_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_run_x27_1179_);
lean_inc(v_name_1178_);
lean_dec(v_pass_1111_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1291_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_7746__overap_1185_; lean_object* v___x_1186_; 
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22));
v___x_1184_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26));
lean_inc_ref(v___x_1169_);
v___x_7746__overap_1185_ = l_Lean_isTracingEnabledFor___redArg(v___x_1169_, v___x_1170_, v___x_1183_, v___x_1184_);
lean_inc(v_a_1118_);
lean_inc_ref(v_a_1117_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
v___x_1186_ = lean_apply_7(v___x_7746__overap_1185_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v_a_1195_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v_a_1214_; uint8_t v___x_1277_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
lean_inc(v_goal_1112_);
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1188_, 0, v_name_1178_);
lean_closure_set(v___f_1188_, 1, v_goal_1112_);
v___f_1189_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28);
v___f_1190_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29));
v___x_1191_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30));
v___x_1277_ = lean_unbox(v_a_1187_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1278_ = l_Lean_KVMap_instValueBool;
v___x_1279_ = l_Lean_trace_profiler;
v___x_1280_ = l_Lean_Option_get___redArg(v___x_1278_, v_options_1174_, v___x_1279_);
v___x_1281_ = lean_unbox(v___x_1280_);
lean_dec(v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref(v___f_1188_);
lean_dec(v_a_1187_);
lean_del_object(v___x_1181_);
lean_dec_ref(v_toMonadRef_1172_);
lean_dec_ref(v___x_1169_);
v___x_1282_ = lean_apply_8(v_run_x27_1179_, v_goal_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
return v___x_1282_;
}
else
{
goto v___jp_1225_;
}
}
else
{
goto v___jp_1225_;
}
v___jp_1192_:
{
lean_object* v___x_1196_; double v___x_1197_; double v___x_1198_; double v___x_1199_; double v___x_1200_; double v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1196_ = lean_io_mono_nanos_now();
v___x_1197_ = lean_float_of_nat(v___y_1193_);
v___x_1198_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31);
v___x_1199_ = lean_float_div(v___x_1197_, v___x_1198_);
v___x_1200_ = lean_float_of_nat(v___x_1196_);
v___x_1201_ = lean_float_div(v___x_1200_, v___x_1198_);
v___x_1202_ = lean_box_float(v___x_1199_);
v___x_1203_ = lean_box_float(v___x_1201_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1203_);
lean_ctor_set(v___x_1181_, 0, v___x_1202_);
v___x_1205_ = v___x_1181_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_7890__overap_1208_; lean_object* v___x_1209_; 
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_a_1195_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_unbox(v_a_1187_);
lean_dec(v_a_1187_);
v___x_7890__overap_1208_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_1169_, v___x_1170_, v_toMonadRef_1172_, v___f_1189_, lean_box(0), v___x_1173_, v___f_1190_, v___x_1184_, v_hasTrace_1175_, v___x_1191_, v_options_1174_, v___x_1207_, v___y_1194_, v___f_1188_, v___x_1206_);
v___x_1209_ = lean_apply_7(v___x_7890__overap_1208_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
return v___x_1209_;
}
}
v___jp_1211_:
{
lean_object* v___x_1215_; double v___x_1216_; double v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; lean_object* v___x_7894__overap_1223_; lean_object* v___x_1224_; 
v___x_1215_ = lean_io_get_num_heartbeats();
v___x_1216_ = lean_float_of_nat(v___y_1212_);
v___x_1217_ = lean_float_of_nat(v___x_1215_);
v___x_1218_ = lean_box_float(v___x_1216_);
v___x_1219_ = lean_box_float(v___x_1217_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_a_1214_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_unbox(v_a_1187_);
lean_dec(v_a_1187_);
v___x_7894__overap_1223_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_1169_, v___x_1170_, v_toMonadRef_1172_, v___f_1189_, lean_box(0), v___x_1173_, v___f_1190_, v___x_1184_, v_hasTrace_1175_, v___x_1191_, v_options_1174_, v___x_1222_, v___y_1213_, v___f_1188_, v___x_1221_);
v___x_1224_ = lean_apply_7(v___x_7894__overap_1223_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
return v___x_1224_;
}
v___jp_1225_:
{
lean_object* v___x_7750__overap_1226_; lean_object* v___x_1227_; 
lean_inc_ref(v___x_1169_);
v___x_7750__overap_1226_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_1169_, v___x_1170_);
lean_inc(v_a_1118_);
lean_inc_ref(v_a_1117_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
v___x_1227_ = lean_apply_7(v___x_7750__overap_1226_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = l_Lean_KVMap_instValueBool;
v___x_1230_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1231_ = l_Lean_Option_get___redArg(v___x_1229_, v_options_1174_, v___x_1230_);
v___x_1232_ = lean_unbox(v___x_1231_);
lean_dec(v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_io_mono_nanos_now();
lean_inc(v_a_1118_);
lean_inc_ref(v_a_1117_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
v___x_1234_ = lean_apply_8(v_run_x27_1179_, v_goal_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 1);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
v___y_1193_ = v___x_1233_;
v___y_1194_ = v_a_1228_;
v_a_1195_ = v___x_1240_;
goto v___jp_1192_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_a_1243_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1234_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1234_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 0);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
v___y_1193_ = v___x_1233_;
v___y_1194_ = v_a_1228_;
v_a_1195_ = v___x_1248_;
goto v___jp_1192_;
}
}
}
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_del_object(v___x_1181_);
v___x_1251_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1118_);
lean_inc_ref(v_a_1117_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
v___x_1252_ = lean_apply_8(v_run_x27_1179_, v_goal_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v___y_1212_ = v___x_1251_;
v___y_1213_ = v_a_1228_;
v_a_1214_ = v___x_1258_;
goto v___jp_1211_;
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1252_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1252_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 0);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v___y_1212_ = v___x_1251_;
v___y_1213_ = v_a_1228_;
v_a_1214_ = v___x_1266_;
goto v___jp_1211_;
}
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v___f_1188_);
lean_dec(v_a_1187_);
lean_del_object(v___x_1181_);
lean_dec_ref(v_run_x27_1179_);
lean_dec_ref(v_toMonadRef_1172_);
lean_dec_ref(v___x_1169_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_goal_1112_);
v_a_1269_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1227_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1227_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1181_);
lean_dec_ref(v_run_x27_1179_);
lean_dec(v_name_1178_);
lean_dec_ref(v_toMonadRef_1172_);
lean_dec_ref(v___x_1169_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_goal_1112_);
v_a_1283_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1186_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1186_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___boxed(lean_object* v_pass_1304_, lean_object* v_goal_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run(v_pass_1304_, v_goal_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(lean_object* v_cls_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_options_1320_; uint8_t v_hasTrace_1321_; 
v_options_1320_ = lean_ctor_get(v___y_1318_, 2);
v_hasTrace_1321_ = lean_ctor_get_uint8(v_options_1320_, sizeof(void*)*1);
if (v_hasTrace_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v_cls_1317_);
v___x_1322_ = lean_box(v_hasTrace_1321_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
else
{
lean_object* v_inheritedTraceOptions_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_inheritedTraceOptions_1324_ = lean_ctor_get(v___y_1318_, 13);
v___x_1325_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__1));
v___x_1326_ = l_Lean_Name_append(v___x_1325_, v_cls_1317_);
v___x_1327_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1324_, v_options_1320_, v___x_1326_);
lean_dec(v___x_1326_);
v___x_1328_ = lean_box(v___x_1327_);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___boxed(lean_object* v_cls_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_1330_, v___y_1331_);
lean_dec_ref(v___y_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0(lean_object* v_cls_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_1334_, v___y_1339_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___boxed(lean_object* v_cls_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0(v_cls_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1351_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_unsigned_to_nat(32u);
v___x_1353_ = lean_mk_empty_array_with_capacity(v___x_1352_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1355_ = ((size_t)5ULL);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_unsigned_to_nat(32u);
v___x_1358_ = lean_mk_empty_array_with_capacity(v___x_1357_);
v___x_1359_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0);
v___x_1360_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___x_1358_);
lean_ctor_set(v___x_1360_, 2, v___x_1356_);
lean_ctor_set(v___x_1360_, 3, v___x_1356_);
lean_ctor_set_usize(v___x_1360_, 4, v___x_1355_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v_traceState_1364_; lean_object* v_traces_1365_; lean_object* v___x_1366_; lean_object* v_traceState_1367_; lean_object* v_env_1368_; lean_object* v_nextMacroScope_1369_; lean_object* v_ngen_1370_; lean_object* v_auxDeclNGen_1371_; lean_object* v_cache_1372_; lean_object* v_messages_1373_; lean_object* v_infoState_1374_; lean_object* v_snapshotTasks_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1394_; 
v___x_1363_ = lean_st_ref_get(v___y_1361_);
v_traceState_1364_ = lean_ctor_get(v___x_1363_, 4);
lean_inc_ref(v_traceState_1364_);
lean_dec(v___x_1363_);
v_traces_1365_ = lean_ctor_get(v_traceState_1364_, 0);
lean_inc_ref(v_traces_1365_);
lean_dec_ref(v_traceState_1364_);
v___x_1366_ = lean_st_ref_take(v___y_1361_);
v_traceState_1367_ = lean_ctor_get(v___x_1366_, 4);
v_env_1368_ = lean_ctor_get(v___x_1366_, 0);
v_nextMacroScope_1369_ = lean_ctor_get(v___x_1366_, 1);
v_ngen_1370_ = lean_ctor_get(v___x_1366_, 2);
v_auxDeclNGen_1371_ = lean_ctor_get(v___x_1366_, 3);
v_cache_1372_ = lean_ctor_get(v___x_1366_, 5);
v_messages_1373_ = lean_ctor_get(v___x_1366_, 6);
v_infoState_1374_ = lean_ctor_get(v___x_1366_, 7);
v_snapshotTasks_1375_ = lean_ctor_get(v___x_1366_, 8);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1377_ = v___x_1366_;
v_isShared_1378_ = v_isSharedCheck_1394_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_snapshotTasks_1375_);
lean_inc(v_infoState_1374_);
lean_inc(v_messages_1373_);
lean_inc(v_cache_1372_);
lean_inc(v_traceState_1367_);
lean_inc(v_auxDeclNGen_1371_);
lean_inc(v_ngen_1370_);
lean_inc(v_nextMacroScope_1369_);
lean_inc(v_env_1368_);
lean_dec(v___x_1366_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1394_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
uint64_t v_tid_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1392_; 
v_tid_1379_ = lean_ctor_get_uint64(v_traceState_1367_, sizeof(void*)*1);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_traceState_1367_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v_traceState_1367_, 0);
lean_dec(v_unused_1393_);
v___x_1381_ = v_traceState_1367_;
v_isShared_1382_ = v_isSharedCheck_1392_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v_traceState_1367_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1392_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1383_);
lean_ctor_set_uint64(v_reuseFailAlloc_1391_, sizeof(void*)*1, v_tid_1379_);
v___x_1385_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 4, v___x_1385_);
v___x_1387_ = v___x_1377_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_env_1368_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_nextMacroScope_1369_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_ngen_1370_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_auxDeclNGen_1371_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v_cache_1372_);
lean_ctor_set(v_reuseFailAlloc_1390_, 6, v_messages_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 7, v_infoState_1374_);
lean_ctor_set(v_reuseFailAlloc_1390_, 8, v_snapshotTasks_1375_);
v___x_1387_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_st_ref_set(v___y_1361_, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_traces_1365_);
return v___x_1389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___boxed(lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(v___y_1395_);
lean_dec(v___y_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___boxed(lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1413_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(lean_object* v_opts_1414_, lean_object* v_opt_1415_){
_start:
{
lean_object* v_name_1416_; lean_object* v_defValue_1417_; lean_object* v_map_1418_; lean_object* v___x_1419_; 
v_name_1416_ = lean_ctor_get(v_opt_1415_, 0);
v_defValue_1417_ = lean_ctor_get(v_opt_1415_, 1);
v_map_1418_ = lean_ctor_get(v_opts_1414_, 0);
v___x_1419_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1418_, v_name_1416_);
if (lean_obj_tag(v___x_1419_) == 0)
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_unbox(v_defValue_1417_);
return v___x_1420_;
}
else
{
lean_object* v_val_1421_; 
v_val_1421_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1421_);
lean_dec_ref(v___x_1419_);
if (lean_obj_tag(v_val_1421_) == 1)
{
uint8_t v_v_1422_; 
v_v_1422_ = lean_ctor_get_uint8(v_val_1421_, 0);
lean_dec_ref(v_val_1421_);
return v_v_1422_;
}
else
{
uint8_t v___x_1423_; 
lean_dec(v_val_1421_);
v___x_1423_ = lean_unbox(v_defValue_1417_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___boxed(lean_object* v_opts_1424_, lean_object* v_opt_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_opts_1424_, v_opt_1425_);
lean_dec_ref(v_opt_1425_);
lean_dec_ref(v_opts_1424_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1430_ = lean_ctor_get(v_x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v_x_1428_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v_x_1428_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 1);
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_a_1438_ = lean_ctor_get(v_x_1428_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_x_1428_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v_x_1428_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v_x_1428_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 0);
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg___boxed(lean_object* v_x_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(v_x_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(lean_object* v_opts_1449_, lean_object* v_opt_1450_){
_start:
{
lean_object* v_name_1451_; lean_object* v_defValue_1452_; lean_object* v_map_1453_; lean_object* v___x_1454_; 
v_name_1451_ = lean_ctor_get(v_opt_1450_, 0);
v_defValue_1452_ = lean_ctor_get(v_opt_1450_, 1);
v_map_1453_ = lean_ctor_get(v_opts_1449_, 0);
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1453_, v_name_1451_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_inc(v_defValue_1452_);
return v_defValue_1452_;
}
else
{
lean_object* v_val_1455_; 
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1455_);
lean_dec_ref(v___x_1454_);
if (lean_obj_tag(v_val_1455_) == 3)
{
lean_object* v_v_1456_; 
v_v_1456_ = lean_ctor_get(v_val_1455_, 0);
lean_inc(v_v_1456_);
lean_dec_ref(v_val_1455_);
return v_v_1456_;
}
else
{
lean_dec(v_val_1455_);
lean_inc(v_defValue_1452_);
return v_defValue_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8___boxed(lean_object* v_opts_1457_, lean_object* v_opt_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(v_opts_1457_, v_opt_1458_);
lean_dec_ref(v_opt_1458_);
lean_dec_ref(v_opts_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5(lean_object* v_e_1460_){
_start:
{
if (lean_obj_tag(v_e_1460_) == 0)
{
uint8_t v___x_1461_; 
v___x_1461_ = 2;
return v___x_1461_;
}
else
{
lean_object* v_a_1462_; 
v_a_1462_ = lean_ctor_get(v_e_1460_, 0);
if (lean_obj_tag(v_a_1462_) == 0)
{
uint8_t v___x_1463_; 
v___x_1463_ = 1;
return v___x_1463_;
}
else
{
uint8_t v___x_1464_; 
v___x_1464_ = 0;
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5___boxed(lean_object* v_e_1465_){
_start:
{
uint8_t v_res_1466_; lean_object* v_r_1467_; 
v_res_1466_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5(v_e_1465_);
lean_dec_ref(v_e_1465_);
v_r_1467_ = lean_box(v_res_1466_);
return v_r_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7(size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_bs_1470_){
_start:
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_usize_dec_lt(v_i_1469_, v_sz_1468_);
if (v___x_1471_ == 0)
{
return v_bs_1470_;
}
else
{
lean_object* v_v_1472_; lean_object* v_msg_1473_; lean_object* v___x_1474_; lean_object* v_bs_x27_1475_; size_t v___x_1476_; size_t v___x_1477_; lean_object* v___x_1478_; 
v_v_1472_ = lean_array_uget_borrowed(v_bs_1470_, v_i_1469_);
v_msg_1473_ = lean_ctor_get(v_v_1472_, 1);
lean_inc_ref(v_msg_1473_);
v___x_1474_ = lean_unsigned_to_nat(0u);
v_bs_x27_1475_ = lean_array_uset(v_bs_1470_, v_i_1469_, v___x_1474_);
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_add(v_i_1469_, v___x_1476_);
v___x_1478_ = lean_array_uset(v_bs_x27_1475_, v_i_1469_, v_msg_1473_);
v_i_1469_ = v___x_1477_;
v_bs_1470_ = v___x_1478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7___boxed(lean_object* v_sz_1480_, lean_object* v_i_1481_, lean_object* v_bs_1482_){
_start:
{
size_t v_sz_boxed_1483_; size_t v_i_boxed_1484_; lean_object* v_res_1485_; 
v_sz_boxed_1483_ = lean_unbox_usize(v_sz_1480_);
lean_dec(v_sz_1480_);
v_i_boxed_1484_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7(v_sz_boxed_1483_, v_i_boxed_1484_, v_bs_1482_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(lean_object* v_msgData_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v_env_1493_; lean_object* v___x_1494_; lean_object* v_mctx_1495_; lean_object* v_lctx_1496_; lean_object* v_options_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1492_ = lean_st_ref_get(v___y_1490_);
v_env_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc_ref(v_env_1493_);
lean_dec(v___x_1492_);
v___x_1494_ = lean_st_ref_get(v___y_1488_);
v_mctx_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc_ref(v_mctx_1495_);
lean_dec(v___x_1494_);
v_lctx_1496_ = lean_ctor_get(v___y_1487_, 2);
v_options_1497_ = lean_ctor_get(v___y_1489_, 2);
lean_inc_ref(v_options_1497_);
lean_inc_ref(v_lctx_1496_);
v___x_1498_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1498_, 0, v_env_1493_);
lean_ctor_set(v___x_1498_, 1, v_mctx_1495_);
lean_ctor_set(v___x_1498_, 2, v_lctx_1496_);
lean_ctor_set(v___x_1498_, 3, v_options_1497_);
v___x_1499_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v_msgData_1486_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1___boxed(lean_object* v_msgData_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(v_msgData_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(lean_object* v_oldTraces_1508_, lean_object* v_data_1509_, lean_object* v_ref_1510_, lean_object* v_msg_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_fileName_1517_; lean_object* v_fileMap_1518_; lean_object* v_options_1519_; lean_object* v_currRecDepth_1520_; lean_object* v_maxRecDepth_1521_; lean_object* v_ref_1522_; lean_object* v_currNamespace_1523_; lean_object* v_openDecls_1524_; lean_object* v_initHeartbeats_1525_; lean_object* v_maxHeartbeats_1526_; lean_object* v_quotContext_1527_; lean_object* v_currMacroScope_1528_; uint8_t v_diag_1529_; lean_object* v_cancelTk_x3f_1530_; uint8_t v_suppressElabErrors_1531_; lean_object* v_inheritedTraceOptions_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1587_; 
v_fileName_1517_ = lean_ctor_get(v___y_1514_, 0);
v_fileMap_1518_ = lean_ctor_get(v___y_1514_, 1);
v_options_1519_ = lean_ctor_get(v___y_1514_, 2);
v_currRecDepth_1520_ = lean_ctor_get(v___y_1514_, 3);
v_maxRecDepth_1521_ = lean_ctor_get(v___y_1514_, 4);
v_ref_1522_ = lean_ctor_get(v___y_1514_, 5);
v_currNamespace_1523_ = lean_ctor_get(v___y_1514_, 6);
v_openDecls_1524_ = lean_ctor_get(v___y_1514_, 7);
v_initHeartbeats_1525_ = lean_ctor_get(v___y_1514_, 8);
v_maxHeartbeats_1526_ = lean_ctor_get(v___y_1514_, 9);
v_quotContext_1527_ = lean_ctor_get(v___y_1514_, 10);
v_currMacroScope_1528_ = lean_ctor_get(v___y_1514_, 11);
v_diag_1529_ = lean_ctor_get_uint8(v___y_1514_, sizeof(void*)*14);
v_cancelTk_x3f_1530_ = lean_ctor_get(v___y_1514_, 12);
v_suppressElabErrors_1531_ = lean_ctor_get_uint8(v___y_1514_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1532_ = lean_ctor_get(v___y_1514_, 13);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___y_1514_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1534_ = v___y_1514_;
v_isShared_1535_ = v_isSharedCheck_1587_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_inheritedTraceOptions_1532_);
lean_inc(v_cancelTk_x3f_1530_);
lean_inc(v_currMacroScope_1528_);
lean_inc(v_quotContext_1527_);
lean_inc(v_maxHeartbeats_1526_);
lean_inc(v_initHeartbeats_1525_);
lean_inc(v_openDecls_1524_);
lean_inc(v_currNamespace_1523_);
lean_inc(v_ref_1522_);
lean_inc(v_maxRecDepth_1521_);
lean_inc(v_currRecDepth_1520_);
lean_inc(v_options_1519_);
lean_inc(v_fileMap_1518_);
lean_inc(v_fileName_1517_);
lean_dec(v___y_1514_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1587_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v_traceState_1537_; lean_object* v_traces_1538_; lean_object* v_ref_1539_; lean_object* v___x_1541_; 
v___x_1536_ = lean_st_ref_get(v___y_1515_);
v_traceState_1537_ = lean_ctor_get(v___x_1536_, 4);
lean_inc_ref(v_traceState_1537_);
lean_dec(v___x_1536_);
v_traces_1538_ = lean_ctor_get(v_traceState_1537_, 0);
lean_inc_ref(v_traces_1538_);
lean_dec_ref(v_traceState_1537_);
v_ref_1539_ = l_Lean_replaceRef(v_ref_1510_, v_ref_1522_);
lean_dec(v_ref_1522_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 5, v_ref_1539_);
v___x_1541_ = v___x_1534_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_fileName_1517_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_fileMap_1518_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_options_1519_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_currRecDepth_1520_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_maxRecDepth_1521_);
lean_ctor_set(v_reuseFailAlloc_1586_, 5, v_ref_1539_);
lean_ctor_set(v_reuseFailAlloc_1586_, 6, v_currNamespace_1523_);
lean_ctor_set(v_reuseFailAlloc_1586_, 7, v_openDecls_1524_);
lean_ctor_set(v_reuseFailAlloc_1586_, 8, v_initHeartbeats_1525_);
lean_ctor_set(v_reuseFailAlloc_1586_, 9, v_maxHeartbeats_1526_);
lean_ctor_set(v_reuseFailAlloc_1586_, 10, v_quotContext_1527_);
lean_ctor_set(v_reuseFailAlloc_1586_, 11, v_currMacroScope_1528_);
lean_ctor_set(v_reuseFailAlloc_1586_, 12, v_cancelTk_x3f_1530_);
lean_ctor_set(v_reuseFailAlloc_1586_, 13, v_inheritedTraceOptions_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*14, v_diag_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*14 + 1, v_suppressElabErrors_1531_);
v___x_1541_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; size_t v_sz_1543_; size_t v___x_1544_; lean_object* v___x_1545_; lean_object* v_msg_1546_; lean_object* v___x_1547_; lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1585_; 
v___x_1542_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1538_);
lean_dec_ref(v_traces_1538_);
v_sz_1543_ = lean_array_size(v___x_1542_);
v___x_1544_ = ((size_t)0ULL);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7(v_sz_1543_, v___x_1544_, v___x_1542_);
v_msg_1546_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1546_, 0, v_data_1509_);
lean_ctor_set(v_msg_1546_, 1, v_msg_1511_);
lean_ctor_set(v_msg_1546_, 2, v___x_1545_);
v___x_1547_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(v_msg_1546_, v___y_1512_, v___y_1513_, v___x_1541_, v___y_1515_);
lean_dec_ref(v___x_1541_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1585_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1585_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v_traceState_1553_; lean_object* v_env_1554_; lean_object* v_nextMacroScope_1555_; lean_object* v_ngen_1556_; lean_object* v_auxDeclNGen_1557_; lean_object* v_cache_1558_; lean_object* v_messages_1559_; lean_object* v_infoState_1560_; lean_object* v_snapshotTasks_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1584_; 
v___x_1552_ = lean_st_ref_take(v___y_1515_);
v_traceState_1553_ = lean_ctor_get(v___x_1552_, 4);
v_env_1554_ = lean_ctor_get(v___x_1552_, 0);
v_nextMacroScope_1555_ = lean_ctor_get(v___x_1552_, 1);
v_ngen_1556_ = lean_ctor_get(v___x_1552_, 2);
v_auxDeclNGen_1557_ = lean_ctor_get(v___x_1552_, 3);
v_cache_1558_ = lean_ctor_get(v___x_1552_, 5);
v_messages_1559_ = lean_ctor_get(v___x_1552_, 6);
v_infoState_1560_ = lean_ctor_get(v___x_1552_, 7);
v_snapshotTasks_1561_ = lean_ctor_get(v___x_1552_, 8);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1563_ = v___x_1552_;
v_isShared_1564_ = v_isSharedCheck_1584_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_snapshotTasks_1561_);
lean_inc(v_infoState_1560_);
lean_inc(v_messages_1559_);
lean_inc(v_cache_1558_);
lean_inc(v_traceState_1553_);
lean_inc(v_auxDeclNGen_1557_);
lean_inc(v_ngen_1556_);
lean_inc(v_nextMacroScope_1555_);
lean_inc(v_env_1554_);
lean_dec(v___x_1552_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1584_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
uint64_t v_tid_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1582_; 
v_tid_1565_ = lean_ctor_get_uint64(v_traceState_1553_, sizeof(void*)*1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_traceState_1553_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_traceState_1553_, 0);
lean_dec(v_unused_1583_);
v___x_1567_ = v_traceState_1553_;
v_isShared_1568_ = v_isSharedCheck_1582_;
goto v_resetjp_1566_;
}
else
{
lean_dec(v_traceState_1553_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1582_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_ref_1510_);
lean_ctor_set(v___x_1569_, 1, v_a_1548_);
v___x_1570_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1508_, v___x_1569_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1570_);
v___x_1572_ = v___x_1567_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1570_);
lean_ctor_set_uint64(v_reuseFailAlloc_1581_, sizeof(void*)*1, v_tid_1565_);
v___x_1572_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1574_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 4, v___x_1572_);
v___x_1574_ = v___x_1563_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_env_1554_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_nextMacroScope_1555_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_ngen_1556_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_auxDeclNGen_1557_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1580_, 5, v_cache_1558_);
lean_ctor_set(v_reuseFailAlloc_1580_, 6, v_messages_1559_);
lean_ctor_set(v_reuseFailAlloc_1580_, 7, v_infoState_1560_);
lean_ctor_set(v_reuseFailAlloc_1580_, 8, v_snapshotTasks_1561_);
v___x_1574_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = lean_st_ref_set(v___y_1515_, v___x_1574_);
v___x_1576_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1576_);
v___x_1578_ = v___x_1550_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg___boxed(lean_object* v_oldTraces_1588_, lean_object* v_data_1589_, lean_object* v_ref_1590_, lean_object* v_msg_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(v_oldTraces_1588_, v_data_1589_, v_ref_1590_, v_msg_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1597_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__0));
v___x_1600_ = l_Lean_stringToMessageData(v___x_1599_);
return v___x_1600_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1601_; double v___x_1602_; 
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_float_of_nat(v___x_1601_);
return v___x_1602_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__3));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1606_; double v___x_1607_; 
v___x_1606_ = lean_unsigned_to_nat(1000u);
v___x_1607_ = lean_float_of_nat(v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(lean_object* v_cls_1608_, uint8_t v_collapsed_1609_, lean_object* v_tag_1610_, lean_object* v_opts_1611_, uint8_t v_clsEnabled_1612_, lean_object* v_oldTraces_1613_, lean_object* v_msg_1614_, lean_object* v_resStartStop_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_fst_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1722_; 
v_fst_1623_ = lean_ctor_get(v_resStartStop_1615_, 0);
v_snd_1624_ = lean_ctor_get(v_resStartStop_1615_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_resStartStop_1615_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1626_ = v_resStartStop_1615_;
v_isShared_1627_ = v_isSharedCheck_1722_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_inc(v_fst_1623_);
lean_dec(v_resStartStop_1615_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1722_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v_data_1631_; lean_object* v_fst_1642_; lean_object* v_snd_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1721_; 
v_fst_1642_ = lean_ctor_get(v_snd_1624_, 0);
v_snd_1643_ = lean_ctor_get(v_snd_1624_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_snd_1624_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1645_ = v_snd_1624_;
v_isShared_1646_ = v_isSharedCheck_1721_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_snd_1643_);
lean_inc(v_fst_1642_);
lean_dec(v_snd_1624_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1721_;
goto v_resetjp_1644_;
}
v___jp_1628_:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(v_oldTraces_1613_, v_data_1631_, v___y_1630_, v___y_1629_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v___x_1632_);
v___x_1633_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(v_fst_1623_);
return v___x_1633_;
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v_fst_1623_);
v_a_1634_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1632_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v___y_1650_; lean_object* v_a_1651_; uint8_t v___y_1675_; double v___y_1706_; 
v___x_1647_ = l_Lean_trace_profiler;
v___x_1648_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_opts_1611_, v___x_1647_);
if (v___x_1648_ == 0)
{
v___y_1675_ = v___x_1648_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1712_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_opts_1611_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; double v___x_1715_; double v___x_1716_; double v___x_1717_; 
v___x_1713_ = l_Lean_trace_profiler_threshold;
v___x_1714_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(v_opts_1611_, v___x_1713_);
v___x_1715_ = lean_float_of_nat(v___x_1714_);
v___x_1716_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5);
v___x_1717_ = lean_float_div(v___x_1715_, v___x_1716_);
v___y_1706_ = v___x_1717_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; double v___x_1720_; 
v___x_1718_ = l_Lean_trace_profiler_threshold;
v___x_1719_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(v_opts_1611_, v___x_1718_);
v___x_1720_ = lean_float_of_nat(v___x_1719_);
v___y_1706_ = v___x_1720_;
goto v___jp_1705_;
}
}
v___jp_1649_:
{
uint8_t v_result_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v_result_1652_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5(v_fst_1623_);
v___x_1653_ = l_Lean_TraceResult_toEmoji(v_result_1652_);
v___x_1654_ = l_Lean_stringToMessageData(v___x_1653_);
v___x_1655_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1);
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 7);
lean_ctor_set(v___x_1645_, 1, v___x_1655_);
lean_ctor_set(v___x_1645_, 0, v___x_1654_);
v___x_1657_ = v___x_1645_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v_m_1659_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 7);
lean_ctor_set(v___x_1626_, 1, v_a_1651_);
lean_ctor_set(v___x_1626_, 0, v___x_1657_);
v_m_1659_ = v___x_1626_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_a_1651_);
v_m_1659_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; double v___x_1662_; lean_object* v_data_1663_; 
v___x_1660_ = lean_box(v_result_1652_);
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
v___x_1662_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2);
lean_inc_ref(v_tag_1610_);
lean_inc_ref(v___x_1661_);
lean_inc(v_cls_1608_);
v_data_1663_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1663_, 0, v_cls_1608_);
lean_ctor_set(v_data_1663_, 1, v___x_1661_);
lean_ctor_set(v_data_1663_, 2, v_tag_1610_);
lean_ctor_set_float(v_data_1663_, sizeof(void*)*3, v___x_1662_);
lean_ctor_set_float(v_data_1663_, sizeof(void*)*3 + 8, v___x_1662_);
lean_ctor_set_uint8(v_data_1663_, sizeof(void*)*3 + 16, v_collapsed_1609_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v___x_1661_);
lean_dec(v_snd_1643_);
lean_dec(v_fst_1642_);
lean_dec_ref(v_tag_1610_);
lean_dec(v_cls_1608_);
v___y_1629_ = v_m_1659_;
v___y_1630_ = v___y_1650_;
v_data_1631_ = v_data_1663_;
goto v___jp_1628_;
}
else
{
lean_object* v_data_1664_; double v___x_1665_; double v___x_1666_; 
lean_dec_ref(v_data_1663_);
v_data_1664_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1664_, 0, v_cls_1608_);
lean_ctor_set(v_data_1664_, 1, v___x_1661_);
lean_ctor_set(v_data_1664_, 2, v_tag_1610_);
v___x_1665_ = lean_unbox_float(v_fst_1642_);
lean_dec(v_fst_1642_);
lean_ctor_set_float(v_data_1664_, sizeof(void*)*3, v___x_1665_);
v___x_1666_ = lean_unbox_float(v_snd_1643_);
lean_dec(v_snd_1643_);
lean_ctor_set_float(v_data_1664_, sizeof(void*)*3 + 8, v___x_1666_);
lean_ctor_set_uint8(v_data_1664_, sizeof(void*)*3 + 16, v_collapsed_1609_);
v___y_1629_ = v_m_1659_;
v___y_1630_ = v___y_1650_;
v_data_1631_ = v_data_1664_;
goto v___jp_1628_;
}
}
}
}
v___jp_1669_:
{
lean_object* v_ref_1670_; lean_object* v___x_1671_; 
v_ref_1670_ = lean_ctor_get(v___y_1620_, 5);
lean_inc(v___y_1621_);
lean_inc_ref(v___y_1620_);
lean_inc(v___y_1619_);
lean_inc_ref(v___y_1618_);
lean_inc(v_fst_1623_);
v___x_1671_ = lean_apply_8(v_msg_1614_, v_fst_1623_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, lean_box(0));
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
lean_inc(v_ref_1670_);
v___y_1650_ = v_ref_1670_;
v_a_1651_ = v_a_1672_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1673_; 
lean_dec_ref(v___x_1671_);
v___x_1673_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4);
lean_inc(v_ref_1670_);
v___y_1650_ = v_ref_1670_;
v_a_1651_ = v___x_1673_;
goto v___jp_1649_;
}
}
v___jp_1674_:
{
if (v_clsEnabled_1612_ == 0)
{
if (v___y_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v_traceState_1677_; lean_object* v_env_1678_; lean_object* v_nextMacroScope_1679_; lean_object* v_ngen_1680_; lean_object* v_auxDeclNGen_1681_; lean_object* v_cache_1682_; lean_object* v_messages_1683_; lean_object* v_infoState_1684_; lean_object* v_snapshotTasks_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1704_; 
lean_del_object(v___x_1645_);
lean_dec(v_snd_1643_);
lean_dec(v_fst_1642_);
lean_del_object(v___x_1626_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec_ref(v_msg_1614_);
lean_dec_ref(v_tag_1610_);
lean_dec(v_cls_1608_);
v___x_1676_ = lean_st_ref_take(v___y_1621_);
v_traceState_1677_ = lean_ctor_get(v___x_1676_, 4);
v_env_1678_ = lean_ctor_get(v___x_1676_, 0);
v_nextMacroScope_1679_ = lean_ctor_get(v___x_1676_, 1);
v_ngen_1680_ = lean_ctor_get(v___x_1676_, 2);
v_auxDeclNGen_1681_ = lean_ctor_get(v___x_1676_, 3);
v_cache_1682_ = lean_ctor_get(v___x_1676_, 5);
v_messages_1683_ = lean_ctor_get(v___x_1676_, 6);
v_infoState_1684_ = lean_ctor_get(v___x_1676_, 7);
v_snapshotTasks_1685_ = lean_ctor_get(v___x_1676_, 8);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1687_ = v___x_1676_;
v_isShared_1688_ = v_isSharedCheck_1704_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_snapshotTasks_1685_);
lean_inc(v_infoState_1684_);
lean_inc(v_messages_1683_);
lean_inc(v_cache_1682_);
lean_inc(v_traceState_1677_);
lean_inc(v_auxDeclNGen_1681_);
lean_inc(v_ngen_1680_);
lean_inc(v_nextMacroScope_1679_);
lean_inc(v_env_1678_);
lean_dec(v___x_1676_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1704_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
uint64_t v_tid_1689_; lean_object* v_traces_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1703_; 
v_tid_1689_ = lean_ctor_get_uint64(v_traceState_1677_, sizeof(void*)*1);
v_traces_1690_ = lean_ctor_get(v_traceState_1677_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_traceState_1677_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1692_ = v_traceState_1677_;
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_traces_1690_);
lean_dec(v_traceState_1677_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1613_, v_traces_1690_);
lean_dec_ref(v_traces_1690_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1694_);
lean_ctor_set_uint64(v_reuseFailAlloc_1702_, sizeof(void*)*1, v_tid_1689_);
v___x_1696_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 4, v___x_1696_);
v___x_1698_ = v___x_1687_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_env_1678_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_nextMacroScope_1679_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_ngen_1680_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_auxDeclNGen_1681_);
lean_ctor_set(v_reuseFailAlloc_1701_, 4, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1701_, 5, v_cache_1682_);
lean_ctor_set(v_reuseFailAlloc_1701_, 6, v_messages_1683_);
lean_ctor_set(v_reuseFailAlloc_1701_, 7, v_infoState_1684_);
lean_ctor_set(v_reuseFailAlloc_1701_, 8, v_snapshotTasks_1685_);
v___x_1698_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_st_ref_set(v___y_1621_, v___x_1698_);
lean_dec(v___y_1621_);
v___x_1700_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(v_fst_1623_);
return v___x_1700_;
}
}
}
}
}
else
{
goto v___jp_1669_;
}
}
else
{
goto v___jp_1669_;
}
}
v___jp_1705_:
{
double v___x_1707_; double v___x_1708_; double v___x_1709_; uint8_t v___x_1710_; 
v___x_1707_ = lean_unbox_float(v_snd_1643_);
v___x_1708_ = lean_unbox_float(v_fst_1642_);
v___x_1709_ = lean_float_sub(v___x_1707_, v___x_1708_);
v___x_1710_ = lean_float_decLt(v___y_1706_, v___x_1709_);
v___y_1675_ = v___x_1710_;
goto v___jp_1674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___boxed(lean_object* v_cls_1723_, lean_object* v_collapsed_1724_, lean_object* v_tag_1725_, lean_object* v_opts_1726_, lean_object* v_clsEnabled_1727_, lean_object* v_oldTraces_1728_, lean_object* v_msg_1729_, lean_object* v_resStartStop_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v_collapsed_boxed_1738_; uint8_t v_clsEnabled_boxed_1739_; lean_object* v_res_1740_; 
v_collapsed_boxed_1738_ = lean_unbox(v_collapsed_1724_);
v_clsEnabled_boxed_1739_ = lean_unbox(v_clsEnabled_1727_);
v_res_1740_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(v_cls_1723_, v_collapsed_boxed_1738_, v_tag_1725_, v_opts_1726_, v_clsEnabled_boxed_1739_, v_oldTraces_1728_, v_msg_1729_, v_resStartStop_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec_ref(v_opts_1726_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(lean_object* v_cls_1743_, lean_object* v_msg_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_ref_1750_; lean_object* v___x_1751_; lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1796_; 
v_ref_1750_ = lean_ctor_get(v___y_1747_, 5);
v___x_1751_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(v_msg_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1796_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1796_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v_traceState_1757_; lean_object* v_env_1758_; lean_object* v_nextMacroScope_1759_; lean_object* v_ngen_1760_; lean_object* v_auxDeclNGen_1761_; lean_object* v_cache_1762_; lean_object* v_messages_1763_; lean_object* v_infoState_1764_; lean_object* v_snapshotTasks_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1795_; 
v___x_1756_ = lean_st_ref_take(v___y_1748_);
v_traceState_1757_ = lean_ctor_get(v___x_1756_, 4);
v_env_1758_ = lean_ctor_get(v___x_1756_, 0);
v_nextMacroScope_1759_ = lean_ctor_get(v___x_1756_, 1);
v_ngen_1760_ = lean_ctor_get(v___x_1756_, 2);
v_auxDeclNGen_1761_ = lean_ctor_get(v___x_1756_, 3);
v_cache_1762_ = lean_ctor_get(v___x_1756_, 5);
v_messages_1763_ = lean_ctor_get(v___x_1756_, 6);
v_infoState_1764_ = lean_ctor_get(v___x_1756_, 7);
v_snapshotTasks_1765_ = lean_ctor_get(v___x_1756_, 8);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1767_ = v___x_1756_;
v_isShared_1768_ = v_isSharedCheck_1795_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snapshotTasks_1765_);
lean_inc(v_infoState_1764_);
lean_inc(v_messages_1763_);
lean_inc(v_cache_1762_);
lean_inc(v_traceState_1757_);
lean_inc(v_auxDeclNGen_1761_);
lean_inc(v_ngen_1760_);
lean_inc(v_nextMacroScope_1759_);
lean_inc(v_env_1758_);
lean_dec(v___x_1756_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1795_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
uint64_t v_tid_1769_; lean_object* v_traces_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1794_; 
v_tid_1769_ = lean_ctor_get_uint64(v_traceState_1757_, sizeof(void*)*1);
v_traces_1770_ = lean_ctor_get(v_traceState_1757_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_traceState_1757_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1772_ = v_traceState_1757_;
v_isShared_1773_ = v_isSharedCheck_1794_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_traces_1770_);
lean_dec(v_traceState_1757_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1794_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; double v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1774_ = lean_box(0);
v___x_1775_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2);
v___x_1776_ = 0;
v___x_1777_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30));
v___x_1778_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1778_, 0, v_cls_1743_);
lean_ctor_set(v___x_1778_, 1, v___x_1774_);
lean_ctor_set(v___x_1778_, 2, v___x_1777_);
lean_ctor_set_float(v___x_1778_, sizeof(void*)*3, v___x_1775_);
lean_ctor_set_float(v___x_1778_, sizeof(void*)*3 + 8, v___x_1775_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*3 + 16, v___x_1776_);
v___x_1779_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0));
v___x_1780_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v_a_1752_);
lean_ctor_set(v___x_1780_, 2, v___x_1779_);
lean_inc(v_ref_1750_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_ref_1750_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_Lean_PersistentArray_push___redArg(v_traces_1770_, v___x_1781_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1782_);
v___x_1784_ = v___x_1772_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1782_);
lean_ctor_set_uint64(v_reuseFailAlloc_1793_, sizeof(void*)*1, v_tid_1769_);
v___x_1784_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1786_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 4, v___x_1784_);
v___x_1786_ = v___x_1767_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_env_1758_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_nextMacroScope_1759_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_ngen_1760_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_auxDeclNGen_1761_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1792_, 5, v_cache_1762_);
lean_ctor_set(v_reuseFailAlloc_1792_, 6, v_messages_1763_);
lean_ctor_set(v_reuseFailAlloc_1792_, 7, v_infoState_1764_);
lean_ctor_set(v_reuseFailAlloc_1792_, 8, v_snapshotTasks_1765_);
v___x_1786_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1787_ = lean_st_ref_set(v___y_1748_, v___x_1786_);
v___x_1788_ = lean_box(0);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1788_);
v___x_1790_ = v___x_1754_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(lean_object* v_cls_1797_, lean_object* v_msg_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v_cls_1797_, v_msg_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0(lean_object* v_name_1805_, lean_object* v_snd_1806_, lean_object* v_x_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1815_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1);
v___x_1816_ = l_Lean_MessageData_ofName(v_name_1805_);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_snd_1806_);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0___boxed(lean_object* v_name_1823_, lean_object* v_snd_1824_, lean_object* v_x_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0(v_name_1823_, v_snd_1824_, v_x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec_ref(v_x_1825_);
return v_res_1833_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__1));
v___x_1838_ = l_Lean_stringToMessageData(v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(lean_object* v_as_x27_1839_, lean_object* v_b_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
if (lean_obj_tag(v_as_x27_1839_) == 0)
{
lean_object* v___x_1848_; 
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_b_1840_);
return v___x_1848_;
}
else
{
lean_object* v_head_1849_; lean_object* v_tail_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1987_; 
v_head_1849_ = lean_ctor_get(v_as_x27_1839_, 0);
v_tail_1850_ = lean_ctor_get(v_as_x27_1839_, 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_as_x27_1839_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1852_ = v_as_x27_1839_;
v_isShared_1853_ = v_isSharedCheck_1987_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_tail_1850_);
lean_inc(v_head_1849_);
lean_dec(v_as_x27_1839_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1987_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_snd_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1985_; 
v_snd_1854_ = lean_ctor_get(v_b_1840_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_b_1840_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v_b_1840_, 0);
lean_dec(v_unused_1986_);
v___x_1856_ = v_b_1840_;
v_isShared_1857_ = v_isSharedCheck_1985_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_snd_1854_);
lean_dec(v_b_1840_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1985_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_options_1864_; lean_object* v_name_1865_; lean_object* v_run_x27_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1984_; 
v_options_1864_ = lean_ctor_get(v___y_1845_, 2);
v_name_1865_ = lean_ctor_get(v_head_1849_, 0);
v_run_x27_1866_ = lean_ctor_get(v_head_1849_, 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_head_1849_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1868_ = v_head_1849_;
v_isShared_1869_ = v_isSharedCheck_1984_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_run_x27_1866_);
lean_inc(v_name_1865_);
lean_dec(v_head_1849_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1984_;
goto v_resetjp_1867_;
}
v___jp_1858_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__0));
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1859_);
v___x_1861_ = v___x_1856_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_snd_1854_);
v___x_1861_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
v_resetjp_1867_:
{
uint8_t v_hasTrace_1870_; lean_object* v___x_1871_; lean_object* v___y_1873_; 
v_hasTrace_1870_ = lean_ctor_get_uint8(v_options_1864_, sizeof(void*)*1);
v___x_1871_ = lean_box(0);
if (v_hasTrace_1870_ == 0)
{
lean_object* v___x_1902_; 
lean_dec(v_name_1865_);
lean_del_object(v___x_1852_);
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v_snd_1854_);
v___x_1902_ = lean_apply_8(v_run_x27_1866_, v_snd_1854_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, lean_box(0));
v___y_1873_ = v___x_1902_;
goto v___jp_1872_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_a_1905_; lean_object* v___f_1906_; lean_object* v___x_1907_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_a_1911_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v_a_1929_; uint8_t v___x_1980_; 
v___x_1903_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26));
v___x_1904_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1903_, v___y_1845_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref(v___x_1904_);
lean_inc(v_snd_1854_);
v___f_1906_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1906_, 0, v_name_1865_);
lean_closure_set(v___f_1906_, 1, v_snd_1854_);
v___x_1907_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30));
v___x_1980_ = lean_unbox(v_a_1905_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = l_Lean_trace_profiler;
v___x_1982_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_options_1864_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_dec_ref(v___f_1906_);
lean_dec(v_a_1905_);
lean_del_object(v___x_1852_);
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v_snd_1854_);
v___x_1983_ = lean_apply_8(v_run_x27_1866_, v_snd_1854_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, lean_box(0));
v___y_1873_ = v___x_1983_;
goto v___jp_1872_;
}
else
{
goto v___jp_1939_;
}
}
else
{
goto v___jp_1939_;
}
v___jp_1908_:
{
lean_object* v___x_1912_; double v___x_1913_; double v___x_1914_; double v___x_1915_; double v___x_1916_; double v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1912_ = lean_io_mono_nanos_now();
v___x_1913_ = lean_float_of_nat(v___y_1910_);
v___x_1914_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31);
v___x_1915_ = lean_float_div(v___x_1913_, v___x_1914_);
v___x_1916_ = lean_float_of_nat(v___x_1912_);
v___x_1917_ = lean_float_div(v___x_1916_, v___x_1914_);
v___x_1918_ = lean_box_float(v___x_1915_);
v___x_1919_ = lean_box_float(v___x_1917_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 0);
lean_ctor_set(v___x_1852_, 1, v___x_1919_);
lean_ctor_set(v___x_1852_, 0, v___x_1918_);
v___x_1921_ = v___x_1852_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1911_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_unbox(v_a_1905_);
lean_dec(v_a_1905_);
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
v___x_1924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(v___x_1903_, v_hasTrace_1870_, v___x_1907_, v_options_1864_, v___x_1923_, v___y_1909_, v___f_1906_, v___x_1922_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
v___y_1873_ = v___x_1924_;
goto v___jp_1872_;
}
}
v___jp_1926_:
{
lean_object* v___x_1930_; double v___x_1931_; double v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1930_ = lean_io_get_num_heartbeats();
v___x_1931_ = lean_float_of_nat(v___y_1927_);
v___x_1932_ = lean_float_of_nat(v___x_1930_);
v___x_1933_ = lean_box_float(v___x_1931_);
v___x_1934_ = lean_box_float(v___x_1932_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_a_1929_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_unbox(v_a_1905_);
lean_dec(v_a_1905_);
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
v___x_1938_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(v___x_1903_, v_hasTrace_1870_, v___x_1907_, v_options_1864_, v___x_1937_, v___y_1928_, v___f_1906_, v___x_1936_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
v___y_1873_ = v___x_1938_;
goto v___jp_1872_;
}
v___jp_1939_:
{
lean_object* v___x_1940_; lean_object* v_a_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1940_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(v___y_1846_);
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref(v___x_1940_);
v___x_1942_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1943_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_options_1864_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_io_mono_nanos_now();
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v_snd_1854_);
v___x_1945_ = lean_apply_8(v_run_x27_1866_, v_snd_1854_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, lean_box(0));
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 1);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v___y_1909_ = v_a_1941_;
v___y_1910_ = v___x_1944_;
v_a_1911_ = v___x_1951_;
goto v___jp_1908_;
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1945_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1945_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 0);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v___y_1909_ = v_a_1941_;
v___y_1910_ = v___x_1944_;
v_a_1911_ = v___x_1959_;
goto v___jp_1908_;
}
}
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_del_object(v___x_1852_);
v___x_1962_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v_snd_1854_);
v___x_1963_ = lean_apply_8(v_run_x27_1866_, v_snd_1854_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, lean_box(0));
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 1);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
v___y_1927_ = v___x_1962_;
v___y_1928_ = v_a_1941_;
v_a_1929_ = v___x_1969_;
goto v___jp_1926_;
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1963_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1963_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set_tag(v___x_1974_, 0);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
v___y_1927_ = v___x_1962_;
v___y_1928_ = v_a_1941_;
v_a_1929_ = v___x_1977_;
goto v___jp_1926_;
}
}
}
}
}
}
v___jp_1872_:
{
if (lean_obj_tag(v___y_1873_) == 0)
{
lean_object* v_a_1874_; 
v_a_1874_ = lean_ctor_get(v___y_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___y_1873_);
if (lean_obj_tag(v_a_1874_) == 1)
{
lean_object* v_val_1875_; lean_object* v___x_1877_; 
lean_del_object(v___x_1856_);
lean_dec(v_snd_1854_);
v_val_1875_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref(v_a_1874_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v_val_1875_);
lean_ctor_set(v___x_1868_, 0, v___x_1871_);
v___x_1877_ = v___x_1868_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_val_1875_);
v___x_1877_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
v_as_x27_1839_ = v_tail_1850_;
v_b_1840_ = v___x_1877_;
goto _start;
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v_a_1882_; uint8_t v___x_1883_; 
lean_dec(v_a_1874_);
lean_del_object(v___x_1868_);
lean_dec(v_tail_1850_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
v___x_1880_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26));
v___x_1881_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1880_, v___y_1845_);
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = lean_unbox(v_a_1882_);
lean_dec(v_a_1882_);
if (v___x_1883_ == 0)
{
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
goto v___jp_1858_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2);
v___x_1885_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___x_1880_, v___x_1884_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_dec_ref(v___x_1885_);
goto v___jp_1858_;
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_del_object(v___x_1856_);
lean_dec(v_snd_1854_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1868_);
lean_del_object(v___x_1856_);
lean_dec(v_snd_1854_);
lean_dec(v_tail_1850_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
v_a_1894_ = lean_ctor_get(v___y_1873_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___y_1873_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___y_1873_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___y_1873_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___boxed(lean_object* v_as_x27_1988_, lean_object* v_b_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(v_as_x27_1988_, v_b_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
return v_res_1997_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2));
v___x_2003_ = l_Lean_stringToMessageData(v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(lean_object* v_passes_2004_, lean_object* v_goal_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = lean_box(0);
lean_inc(v_goal_2005_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v_goal_2005_);
lean_inc(v_a_2011_);
lean_inc_ref(v_a_2010_);
lean_inc(v_a_2009_);
lean_inc_ref(v_a_2008_);
lean_inc(v_a_2007_);
lean_inc_ref(v_a_2006_);
lean_inc(v_passes_2004_);
v___x_2015_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(v_passes_2004_, v___x_2014_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2090_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2090_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2090_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_fst_2020_; lean_object* v_snd_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2089_; 
v_fst_2020_ = lean_ctor_get(v_a_2016_, 0);
v_snd_2021_ = lean_ctor_get(v_a_2016_, 1);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_a_2016_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2023_ = v_a_2016_;
v_isShared_2024_ = v_isSharedCheck_2089_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_snd_2021_);
lean_inc(v_fst_2020_);
lean_dec(v_a_2016_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2089_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
if (lean_obj_tag(v_fst_2020_) == 0)
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_instBEqMVarId_beq(v_goal_2005_, v_snd_2021_);
lean_dec(v_goal_2005_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_del_object(v___x_2018_);
v___x_2031_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26));
v___x_2032_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_2031_, v_a_2010_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; uint8_t v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2032_);
v___x_2034_ = lean_unbox(v_a_2033_);
lean_dec(v_a_2033_);
if (v___x_2034_ == 0)
{
lean_del_object(v___x_2023_);
v_goal_2005_ = v_snd_2021_;
goto _start;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2036_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1);
lean_inc(v_snd_2021_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v_snd_2021_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set_tag(v___x_2023_, 7);
lean_ctor_set(v___x_2023_, 1, v___x_2037_);
lean_ctor_set(v___x_2023_, 0, v___x_2036_);
v___x_2039_ = v___x_2023_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___x_2031_, v___x_2039_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_dec_ref(v___x_2040_);
v_goal_2005_ = v_snd_2021_;
goto _start;
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_snd_2021_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_passes_2004_);
v_a_2042_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2040_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2040_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_2023_);
lean_dec(v_snd_2021_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_passes_2004_);
v_a_2051_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2032_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2032_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_del_object(v___x_2023_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_passes_2004_);
v___x_2059_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26));
v___x_2060_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_2059_, v_a_2010_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; uint8_t v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2060_);
v___x_2062_ = lean_unbox(v_a_2061_);
lean_dec(v_a_2061_);
if (v___x_2062_ == 0)
{
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
goto v___jp_2025_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3);
v___x_2064_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___x_2059_, v___x_2063_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_dec_ref(v___x_2064_);
goto v___jp_2025_;
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v_snd_2021_);
lean_del_object(v___x_2018_);
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_snd_2021_);
lean_del_object(v___x_2018_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
v_a_2073_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2060_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2060_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
else
{
lean_object* v_val_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_del_object(v___x_2023_);
lean_dec(v_snd_2021_);
lean_del_object(v___x_2018_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_goal_2005_);
lean_dec(v_passes_2004_);
v_val_2081_ = lean_ctor_get(v_fst_2020_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_fst_2020_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v_fst_2020_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_val_2081_);
lean_dec(v_fst_2020_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 0);
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_val_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
v___jp_2025_:
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_snd_2021_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2026_);
v___x_2028_ = v___x_2018_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_goal_2005_);
lean_dec(v_passes_2004_);
v_a_2091_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2015_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2015_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_2099_, lean_object* v_goal_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(v_passes_2099_, v_goal_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1(lean_object* v_cls_2109_, lean_object* v_msg_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v_cls_2109_, v_msg_2110_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___boxed(lean_object* v_cls_2119_, lean_object* v_msg_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1(v_cls_2119_, v_msg_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7(lean_object* v_00_u03b1_2129_, lean_object* v_x_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(v_x_2130_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_x_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7(v_00_u03b1_2139_, v_x_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(lean_object* v_as_2149_, lean_object* v_as_x27_2150_, lean_object* v_b_2151_, lean_object* v_a_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(v_as_x27_2150_, v_b_2151_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___boxed(lean_object* v_as_2161_, lean_object* v_as_x27_2162_, lean_object* v_b_2163_, lean_object* v_a_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(v_as_2161_, v_as_x27_2162_, v_b_2163_, v_a_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v_as_2161_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6(lean_object* v_oldTraces_2173_, lean_object* v_data_2174_, lean_object* v_ref_2175_, lean_object* v_msg_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(v_oldTraces_2173_, v_data_2174_, v_ref_2175_, v_msg_2176_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___boxed(lean_object* v_oldTraces_2185_, lean_object* v_data_2186_, lean_object* v_ref_2187_, lean_object* v_msg_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6(v_oldTraces_2185_, v_data_2186_, v_ref_2187_, v_msg_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
return v_res_2196_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
