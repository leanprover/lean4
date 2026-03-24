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
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7_value;
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
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultOption___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32;
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
lean_inc_ref(v_a_39_);
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
lean_dec_ref(v_a_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_getConfig(lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
lean_inc_ref(v_a_45_);
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
lean_dec_ref(v_a_53_);
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
v___x_718_ = l_instMonadEIO(lean_box(0));
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__0);
v___x_720_ = l_StateRefT_x27_instMonad___redArg(v___x_719_);
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
v___x_762_ = l_StateRefT_x27_instMonad___redArg(v___x_761_);
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
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_664__overap_811_; lean_object* v___x_812_; 
v___x_807_ = l_StateRefT_x27_instMonad___redArg(v___x_806_);
v___x_808_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_808_, 0, lean_box(0));
lean_closure_set(v___x_808_, 1, lean_box(0));
lean_closure_set(v___x_808_, 2, v___x_807_);
v___x_809_ = l_instMonadControlTOfPure___redArg(v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6));
v___x_664__overap_811_ = l_Lean_MVarId_withContext___redArg(v___x_809_, v___x_785_, v_goal_735_, v___x_810_);
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
v___x_812_ = lean_apply_5(v___x_664__overap_811_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, lean_box(0));
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
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
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
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
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
v___x_898_ = l_StateRefT_x27_instMonad___redArg(v___x_897_);
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
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_887__overap_947_; lean_object* v___x_948_; 
v___x_943_ = l_StateRefT_x27_instMonad___redArg(v___x_942_);
v___x_944_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_944_, 0, lean_box(0));
lean_closure_set(v___x_944_, 1, lean_box(0));
lean_closure_set(v___x_944_, 2, v___x_943_);
v___x_945_ = l_instMonadControlTOfPure___redArg(v___x_944_);
v___x_946_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6));
v___x_887__overap_947_ = l_Lean_MVarId_withContext___redArg(v___x_945_, v___x_921_, v_goal_871_, v___x_946_);
lean_inc(v_a_876_);
lean_inc_ref(v_a_875_);
lean_inc(v_a_874_);
lean_inc_ref(v_a_873_);
v___x_948_ = lean_apply_5(v___x_887__overap_947_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, lean_box(0));
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
lean_inc(v_a_876_);
lean_inc_ref(v_a_875_);
lean_inc(v_a_874_);
lean_inc_ref(v_a_873_);
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
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
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
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7));
v___x_1060_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1059_, v___x_1058_, v___x_1057_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8);
v___f_1062_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1063_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6));
v___x_1064_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1063_, v___f_1062_, v___x_1061_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1065_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9);
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7));
v___x_1068_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1067_, v___x_1066_, v___x_1065_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___x_1072_; 
v___x_1069_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10);
v___f_1070_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6));
v___x_1072_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1071_, v___f_1070_, v___x_1069_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12(void){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12);
v___x_1075_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13);
v___x_1077_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14);
v___x_1079_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15);
v___x_1081_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16);
v___x_1083_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17);
v___x_1085_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___f_1104_; 
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1103_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1104_, 0, v___x_1103_);
lean_closure_set(v___f_1104_, 1, v___x_1102_);
return v___f_1104_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29(void){
_start:
{
lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___f_1107_; 
v___f_1105_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1106_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28);
v___f_1107_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1107_, 0, v___f_1106_);
lean_closure_set(v___f_1107_, 1, v___f_1105_);
return v___f_1107_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32(void){
_start:
{
lean_object* v___x_1110_; double v___x_1111_; 
v___x_1110_ = lean_unsigned_to_nat(1000000000u);
v___x_1111_ = lean_float_of_nat(v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run(lean_object* v_pass_1112_, lean_object* v_goal_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v_toApplicative_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1303_; 
v___x_1121_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; 
v_unused_1304_ = lean_ctor_get(v___x_1121_, 1);
lean_dec(v_unused_1304_);
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1303_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_toApplicative_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1303_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_toFunctor_1126_; lean_object* v_toSeq_1127_; lean_object* v_toSeqLeft_1128_; lean_object* v_toSeqRight_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1301_; 
v_toFunctor_1126_ = lean_ctor_get(v_toApplicative_1122_, 0);
v_toSeq_1127_ = lean_ctor_get(v_toApplicative_1122_, 2);
v_toSeqLeft_1128_ = lean_ctor_get(v_toApplicative_1122_, 3);
v_toSeqRight_1129_ = lean_ctor_get(v_toApplicative_1122_, 4);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_toApplicative_1122_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v_toApplicative_1122_, 1);
lean_dec(v_unused_1302_);
v___x_1131_ = v_toApplicative_1122_;
v_isShared_1132_ = v_isSharedCheck_1301_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_toSeqRight_1129_);
lean_inc(v_toSeqLeft_1128_);
lean_inc(v_toSeq_1127_);
lean_inc(v_toFunctor_1126_);
lean_dec(v_toApplicative_1122_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1301_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___f_1138_; lean_object* v___f_1139_; lean_object* v___f_1140_; lean_object* v___x_1142_; 
v___f_1133_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2));
v___f_1134_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3));
lean_inc_ref(v_toFunctor_1126_);
v___f_1135_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1135_, 0, v_toFunctor_1126_);
v___f_1136_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1136_, 0, v_toFunctor_1126_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___f_1135_);
lean_ctor_set(v___x_1137_, 1, v___f_1136_);
v___f_1138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1138_, 0, v_toSeqRight_1129_);
v___f_1139_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1139_, 0, v_toSeqLeft_1128_);
v___f_1140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1140_, 0, v_toSeq_1127_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 4, v___f_1138_);
lean_ctor_set(v___x_1131_, 3, v___f_1139_);
lean_ctor_set(v___x_1131_, 2, v___f_1140_);
lean_ctor_set(v___x_1131_, 1, v___f_1133_);
lean_ctor_set(v___x_1131_, 0, v___x_1137_);
v___x_1142_ = v___x_1131_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___f_1133_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v___f_1140_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v___f_1139_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v___f_1138_);
v___x_1142_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v___f_1134_);
lean_ctor_set(v___x_1124_, 0, v___x_1142_);
v___x_1144_ = v___x_1124_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___f_1134_);
v___x_1144_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; lean_object* v_toApplicative_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1297_; 
v___x_1145_ = l_StateRefT_x27_instMonad___redArg(v___x_1144_);
v_toApplicative_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v___x_1145_, 1);
lean_dec(v_unused_1298_);
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1297_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_toApplicative_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1297_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_toFunctor_1150_; lean_object* v_toSeq_1151_; lean_object* v_toSeqLeft_1152_; lean_object* v_toSeqRight_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1295_; 
v_toFunctor_1150_ = lean_ctor_get(v_toApplicative_1146_, 0);
v_toSeq_1151_ = lean_ctor_get(v_toApplicative_1146_, 2);
v_toSeqLeft_1152_ = lean_ctor_get(v_toApplicative_1146_, 3);
v_toSeqRight_1153_ = lean_ctor_get(v_toApplicative_1146_, 4);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_toApplicative_1146_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v_toApplicative_1146_, 1);
lean_dec(v_unused_1296_);
v___x_1155_ = v_toApplicative_1146_;
v_isShared_1156_ = v_isSharedCheck_1295_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_toSeqRight_1153_);
lean_inc(v_toSeqLeft_1152_);
lean_inc(v_toSeq_1151_);
lean_inc(v_toFunctor_1150_);
lean_dec(v_toApplicative_1146_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1295_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___x_1166_; 
v___f_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4));
v___f_1158_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5));
lean_inc_ref(v_toFunctor_1150_);
v___f_1159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1159_, 0, v_toFunctor_1150_);
v___f_1160_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1160_, 0, v_toFunctor_1150_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___f_1159_);
lean_ctor_set(v___x_1161_, 1, v___f_1160_);
v___f_1162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1162_, 0, v_toSeqRight_1153_);
v___f_1163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1163_, 0, v_toSeqLeft_1152_);
v___f_1164_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1164_, 0, v_toSeq_1151_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 4, v___f_1162_);
lean_ctor_set(v___x_1155_, 3, v___f_1163_);
lean_ctor_set(v___x_1155_, 2, v___f_1164_);
lean_ctor_set(v___x_1155_, 1, v___f_1157_);
lean_ctor_set(v___x_1155_, 0, v___x_1161_);
v___x_1166_ = v___x_1155_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___f_1157_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v___f_1164_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v___f_1163_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v___f_1162_);
v___x_1166_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___f_1158_);
lean_ctor_set(v___x_1148_, 0, v___x_1166_);
v___x_1168_ = v___x_1148_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___f_1158_);
v___x_1168_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_toMonadRef_1173_; lean_object* v___x_1174_; lean_object* v_options_1175_; uint8_t v_hasTrace_1176_; 
v___x_1169_ = l_StateRefT_x27_instMonad___redArg(v___x_1168_);
v___x_1170_ = l_ReaderT_instMonad___redArg(v___x_1169_);
v___x_1171_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5);
v___x_1172_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11);
v_toMonadRef_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc_ref(v_toMonadRef_1173_);
v___x_1174_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18);
v_options_1175_ = lean_ctor_get(v_a_1118_, 2);
v_hasTrace_1176_ = lean_ctor_get_uint8(v_options_1175_, sizeof(void*)*1);
if (v_hasTrace_1176_ == 0)
{
lean_object* v_run_x27_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_toMonadRef_1173_);
lean_dec_ref(v___x_1170_);
v_run_x27_1177_ = lean_ctor_get(v_pass_1112_, 1);
lean_inc_ref(v_run_x27_1177_);
lean_dec_ref(v_pass_1112_);
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
v___x_1178_ = lean_apply_8(v_run_x27_1177_, v_goal_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, lean_box(0));
return v___x_1178_;
}
else
{
lean_object* v_name_1179_; lean_object* v_run_x27_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1292_; 
v_name_1179_ = lean_ctor_get(v_pass_1112_, 0);
v_run_x27_1180_ = lean_ctor_get(v_pass_1112_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_pass_1112_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1182_ = v_pass_1112_;
v_isShared_1183_ = v_isSharedCheck_1292_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_run_x27_1180_);
lean_inc(v_name_1179_);
lean_dec(v_pass_1112_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1292_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_7704__overap_1186_; lean_object* v___x_1187_; 
v___x_1184_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23));
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27));
lean_inc_ref(v___x_1170_);
v___x_7704__overap_1186_ = l_Lean_isTracingEnabledFor___redArg(v___x_1170_, v___x_1171_, v___x_1184_, v___x_1185_);
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
v___x_1187_ = lean_apply_7(v___x_7704__overap_1186_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, lean_box(0));
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v_a_1196_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v_a_1215_; uint8_t v___x_1278_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
lean_inc(v_goal_1113_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1189_, 0, v_name_1179_);
lean_closure_set(v___f_1189_, 1, v_goal_1113_);
v___f_1190_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29);
v___f_1191_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30));
v___x_1192_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31));
v___x_1278_ = lean_unbox(v_a_1188_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1279_ = l_Lean_KVMap_instValueBool;
v___x_1280_ = l_Lean_trace_profiler;
v___x_1281_ = l_Lean_Option_get___redArg(v___x_1279_, v_options_1175_, v___x_1280_);
v___x_1282_ = lean_unbox(v___x_1281_);
lean_dec(v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_dec_ref(v___f_1189_);
lean_dec(v_a_1188_);
lean_del_object(v___x_1182_);
lean_dec_ref(v_toMonadRef_1173_);
lean_dec_ref(v___x_1170_);
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
v___x_1283_ = lean_apply_8(v_run_x27_1180_, v_goal_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, lean_box(0));
return v___x_1283_;
}
else
{
goto v___jp_1226_;
}
}
else
{
goto v___jp_1226_;
}
v___jp_1193_:
{
lean_object* v___x_1197_; double v___x_1198_; double v___x_1199_; double v___x_1200_; double v___x_1201_; double v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1197_ = lean_io_mono_nanos_now();
v___x_1198_ = lean_float_of_nat(v___y_1194_);
v___x_1199_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32);
v___x_1200_ = lean_float_div(v___x_1198_, v___x_1199_);
v___x_1201_ = lean_float_of_nat(v___x_1197_);
v___x_1202_ = lean_float_div(v___x_1201_, v___x_1199_);
v___x_1203_ = lean_box_float(v___x_1200_);
v___x_1204_ = lean_box_float(v___x_1202_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v___x_1204_);
lean_ctor_set(v___x_1182_, 0, v___x_1203_);
v___x_1206_ = v___x_1182_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_7848__overap_1209_; lean_object* v___x_1210_; 
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_a_1196_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_unbox(v_a_1188_);
lean_dec(v_a_1188_);
v___x_7848__overap_1209_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_1170_, v___x_1171_, v_toMonadRef_1173_, v___f_1190_, lean_box(0), v___x_1174_, v___f_1191_, v___x_1185_, v_hasTrace_1176_, v___x_1192_, v_options_1175_, v___x_1208_, v___y_1195_, v___f_1189_, v___x_1207_);
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
v___x_1210_ = lean_apply_7(v___x_7848__overap_1209_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, lean_box(0));
return v___x_1210_;
}
}
v___jp_1212_:
{
lean_object* v___x_1216_; double v___x_1217_; double v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_7852__overap_1224_; lean_object* v___x_1225_; 
v___x_1216_ = lean_io_get_num_heartbeats();
v___x_1217_ = lean_float_of_nat(v___y_1213_);
v___x_1218_ = lean_float_of_nat(v___x_1216_);
v___x_1219_ = lean_box_float(v___x_1217_);
v___x_1220_ = lean_box_float(v___x_1218_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_a_1215_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_unbox(v_a_1188_);
lean_dec(v_a_1188_);
v___x_7852__overap_1224_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_1170_, v___x_1171_, v_toMonadRef_1173_, v___f_1190_, lean_box(0), v___x_1174_, v___f_1191_, v___x_1185_, v_hasTrace_1176_, v___x_1192_, v_options_1175_, v___x_1223_, v___y_1214_, v___f_1189_, v___x_1222_);
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
v___x_1225_ = lean_apply_7(v___x_7852__overap_1224_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, lean_box(0));
return v___x_1225_;
}
v___jp_1226_:
{
lean_object* v___x_7708__overap_1227_; lean_object* v___x_1228_; 
lean_inc_ref(v___x_1170_);
v___x_7708__overap_1227_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_1170_, v___x_1171_);
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
v___x_1228_ = lean_apply_7(v___x_7708__overap_1227_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, lean_box(0));
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = l_Lean_KVMap_instValueBool;
v___x_1231_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1232_ = l_Lean_Option_get___redArg(v___x_1230_, v_options_1175_, v___x_1231_);
v___x_1233_ = lean_unbox(v___x_1232_);
lean_dec(v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_io_mono_nanos_now();
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
v___x_1235_ = lean_apply_8(v_run_x27_1180_, v_goal_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, lean_box(0));
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 1);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
v___y_1194_ = v___x_1234_;
v___y_1195_ = v_a_1229_;
v_a_1196_ = v___x_1241_;
goto v___jp_1193_;
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_a_1244_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1235_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1235_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 0);
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
v___y_1194_ = v___x_1234_;
v___y_1195_ = v_a_1229_;
v_a_1196_ = v___x_1249_;
goto v___jp_1193_;
}
}
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_del_object(v___x_1182_);
v___x_1252_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1119_);
lean_inc_ref(v_a_1118_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
v___x_1253_ = lean_apply_8(v_run_x27_1180_, v_goal_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, lean_box(0));
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 1);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v___y_1213_ = v___x_1252_;
v___y_1214_ = v_a_1229_;
v_a_1215_ = v___x_1259_;
goto v___jp_1212_;
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v_a_1262_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1253_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1253_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set_tag(v___x_1264_, 0);
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v___y_1213_ = v___x_1252_;
v___y_1214_ = v_a_1229_;
v_a_1215_ = v___x_1267_;
goto v___jp_1212_;
}
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v___f_1189_);
lean_dec(v_a_1188_);
lean_del_object(v___x_1182_);
lean_dec_ref(v_run_x27_1180_);
lean_dec_ref(v_toMonadRef_1173_);
lean_dec_ref(v___x_1170_);
lean_dec(v_goal_1113_);
v_a_1270_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1228_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1228_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_del_object(v___x_1182_);
lean_dec_ref(v_run_x27_1180_);
lean_dec(v_name_1179_);
lean_dec_ref(v_toMonadRef_1173_);
lean_dec_ref(v___x_1170_);
lean_dec(v_goal_1113_);
v_a_1284_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1187_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1187_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___boxed(lean_object* v_pass_1305_, lean_object* v_goal_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run(v_pass_1305_, v_goal_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(lean_object* v_cls_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_options_1321_; uint8_t v_hasTrace_1322_; 
v_options_1321_ = lean_ctor_get(v___y_1319_, 2);
v_hasTrace_1322_ = lean_ctor_get_uint8(v_options_1321_, sizeof(void*)*1);
if (v_hasTrace_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_cls_1318_);
v___x_1323_ = lean_box(v_hasTrace_1322_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
else
{
lean_object* v_inheritedTraceOptions_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_inheritedTraceOptions_1325_ = lean_ctor_get(v___y_1319_, 13);
v___x_1326_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__1));
v___x_1327_ = l_Lean_Name_append(v___x_1326_, v_cls_1318_);
v___x_1328_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1325_, v_options_1321_, v___x_1327_);
lean_dec(v___x_1327_);
v___x_1329_ = lean_box(v___x_1328_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___boxed(lean_object* v_cls_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_1331_, v___y_1332_);
lean_dec_ref(v___y_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0(lean_object* v_cls_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_1335_, v___y_1340_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___boxed(lean_object* v_cls_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0(v_cls_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1352_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_unsigned_to_nat(32u);
v___x_1354_ = lean_mk_empty_array_with_capacity(v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1356_ = ((size_t)5ULL);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_unsigned_to_nat(32u);
v___x_1359_ = lean_mk_empty_array_with_capacity(v___x_1358_);
v___x_1360_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__0);
v___x_1361_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___x_1359_);
lean_ctor_set(v___x_1361_, 2, v___x_1357_);
lean_ctor_set(v___x_1361_, 3, v___x_1357_);
lean_ctor_set_usize(v___x_1361_, 4, v___x_1356_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v_traceState_1365_; lean_object* v_traces_1366_; lean_object* v___x_1367_; lean_object* v_traceState_1368_; lean_object* v_env_1369_; lean_object* v_nextMacroScope_1370_; lean_object* v_ngen_1371_; lean_object* v_auxDeclNGen_1372_; lean_object* v_cache_1373_; lean_object* v_messages_1374_; lean_object* v_infoState_1375_; lean_object* v_snapshotTasks_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1395_; 
v___x_1364_ = lean_st_ref_get(v___y_1362_);
v_traceState_1365_ = lean_ctor_get(v___x_1364_, 4);
lean_inc_ref(v_traceState_1365_);
lean_dec(v___x_1364_);
v_traces_1366_ = lean_ctor_get(v_traceState_1365_, 0);
lean_inc_ref(v_traces_1366_);
lean_dec_ref(v_traceState_1365_);
v___x_1367_ = lean_st_ref_take(v___y_1362_);
v_traceState_1368_ = lean_ctor_get(v___x_1367_, 4);
v_env_1369_ = lean_ctor_get(v___x_1367_, 0);
v_nextMacroScope_1370_ = lean_ctor_get(v___x_1367_, 1);
v_ngen_1371_ = lean_ctor_get(v___x_1367_, 2);
v_auxDeclNGen_1372_ = lean_ctor_get(v___x_1367_, 3);
v_cache_1373_ = lean_ctor_get(v___x_1367_, 5);
v_messages_1374_ = lean_ctor_get(v___x_1367_, 6);
v_infoState_1375_ = lean_ctor_get(v___x_1367_, 7);
v_snapshotTasks_1376_ = lean_ctor_get(v___x_1367_, 8);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1378_ = v___x_1367_;
v_isShared_1379_ = v_isSharedCheck_1395_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_snapshotTasks_1376_);
lean_inc(v_infoState_1375_);
lean_inc(v_messages_1374_);
lean_inc(v_cache_1373_);
lean_inc(v_traceState_1368_);
lean_inc(v_auxDeclNGen_1372_);
lean_inc(v_ngen_1371_);
lean_inc(v_nextMacroScope_1370_);
lean_inc(v_env_1369_);
lean_dec(v___x_1367_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1395_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint64_t v_tid_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1393_; 
v_tid_1380_ = lean_ctor_get_uint64(v_traceState_1368_, sizeof(void*)*1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_traceState_1368_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v_traceState_1368_, 0);
lean_dec(v_unused_1394_);
v___x_1382_ = v_traceState_1368_;
v_isShared_1383_ = v_isSharedCheck_1393_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v_traceState_1368_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1393_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___closed__1);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1384_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1384_);
lean_ctor_set_uint64(v_reuseFailAlloc_1392_, sizeof(void*)*1, v_tid_1380_);
v___x_1386_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 4, v___x_1386_);
v___x_1388_ = v___x_1378_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_env_1369_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_nextMacroScope_1370_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_ngen_1371_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_auxDeclNGen_1372_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1391_, 5, v_cache_1373_);
lean_ctor_set(v_reuseFailAlloc_1391_, 6, v_messages_1374_);
lean_ctor_set(v_reuseFailAlloc_1391_, 7, v_infoState_1375_);
lean_ctor_set(v_reuseFailAlloc_1391_, 8, v_snapshotTasks_1376_);
v___x_1388_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_st_ref_set(v___y_1362_, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_traces_1366_);
return v___x_1390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg___boxed(lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(v___y_1396_);
lean_dec(v___y_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(v___y_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___boxed(lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1414_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(lean_object* v_opts_1415_, lean_object* v_opt_1416_){
_start:
{
lean_object* v_name_1417_; lean_object* v_defValue_1418_; lean_object* v_map_1419_; lean_object* v___x_1420_; 
v_name_1417_ = lean_ctor_get(v_opt_1416_, 0);
v_defValue_1418_ = lean_ctor_get(v_opt_1416_, 1);
v_map_1419_ = lean_ctor_get(v_opts_1415_, 0);
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1419_, v_name_1417_);
if (lean_obj_tag(v___x_1420_) == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_unbox(v_defValue_1418_);
return v___x_1421_;
}
else
{
lean_object* v_val_1422_; 
v_val_1422_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_val_1422_);
lean_dec_ref(v___x_1420_);
if (lean_obj_tag(v_val_1422_) == 1)
{
uint8_t v_v_1423_; 
v_v_1423_ = lean_ctor_get_uint8(v_val_1422_, 0);
lean_dec_ref(v_val_1422_);
return v_v_1423_;
}
else
{
uint8_t v___x_1424_; 
lean_dec(v_val_1422_);
v___x_1424_ = lean_unbox(v_defValue_1418_);
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___boxed(lean_object* v_opts_1425_, lean_object* v_opt_1426_){
_start:
{
uint8_t v_res_1427_; lean_object* v_r_1428_; 
v_res_1427_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_opts_1425_, v_opt_1426_);
lean_dec_ref(v_opt_1426_);
lean_dec_ref(v_opts_1425_);
v_r_1428_ = lean_box(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(lean_object* v_x_1429_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v_x_1429_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v_x_1429_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v_x_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set_tag(v___x_1433_, 1);
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v_x_1429_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v_x_1429_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v_x_1429_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 0);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg___boxed(lean_object* v_x_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(v_x_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(lean_object* v_opts_1450_, lean_object* v_opt_1451_){
_start:
{
lean_object* v_name_1452_; lean_object* v_defValue_1453_; lean_object* v_map_1454_; lean_object* v___x_1455_; 
v_name_1452_ = lean_ctor_get(v_opt_1451_, 0);
v_defValue_1453_ = lean_ctor_get(v_opt_1451_, 1);
v_map_1454_ = lean_ctor_get(v_opts_1450_, 0);
v___x_1455_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1454_, v_name_1452_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_inc(v_defValue_1453_);
return v_defValue_1453_;
}
else
{
lean_object* v_val_1456_; 
v_val_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_val_1456_);
lean_dec_ref(v___x_1455_);
if (lean_obj_tag(v_val_1456_) == 3)
{
lean_object* v_v_1457_; 
v_v_1457_ = lean_ctor_get(v_val_1456_, 0);
lean_inc(v_v_1457_);
lean_dec_ref(v_val_1456_);
return v_v_1457_;
}
else
{
lean_dec(v_val_1456_);
lean_inc(v_defValue_1453_);
return v_defValue_1453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8___boxed(lean_object* v_opts_1458_, lean_object* v_opt_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(v_opts_1458_, v_opt_1459_);
lean_dec_ref(v_opt_1459_);
lean_dec_ref(v_opts_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5(lean_object* v_e_1461_){
_start:
{
if (lean_obj_tag(v_e_1461_) == 0)
{
uint8_t v___x_1462_; 
v___x_1462_ = 2;
return v___x_1462_;
}
else
{
lean_object* v_a_1463_; 
v_a_1463_ = lean_ctor_get(v_e_1461_, 0);
if (lean_obj_tag(v_a_1463_) == 0)
{
uint8_t v___x_1464_; 
v___x_1464_ = 1;
return v___x_1464_;
}
else
{
uint8_t v___x_1465_; 
v___x_1465_ = 0;
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5___boxed(lean_object* v_e_1466_){
_start:
{
uint8_t v_res_1467_; lean_object* v_r_1468_; 
v_res_1467_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5(v_e_1466_);
lean_dec_ref(v_e_1466_);
v_r_1468_ = lean_box(v_res_1467_);
return v_r_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7(size_t v_sz_1469_, size_t v_i_1470_, lean_object* v_bs_1471_){
_start:
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_usize_dec_lt(v_i_1470_, v_sz_1469_);
if (v___x_1472_ == 0)
{
return v_bs_1471_;
}
else
{
lean_object* v_v_1473_; lean_object* v_msg_1474_; lean_object* v___x_1475_; lean_object* v_bs_x27_1476_; size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v_v_1473_ = lean_array_uget_borrowed(v_bs_1471_, v_i_1470_);
v_msg_1474_ = lean_ctor_get(v_v_1473_, 1);
lean_inc_ref(v_msg_1474_);
v___x_1475_ = lean_unsigned_to_nat(0u);
v_bs_x27_1476_ = lean_array_uset(v_bs_1471_, v_i_1470_, v___x_1475_);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_add(v_i_1470_, v___x_1477_);
v___x_1479_ = lean_array_uset(v_bs_x27_1476_, v_i_1470_, v_msg_1474_);
v_i_1470_ = v___x_1478_;
v_bs_1471_ = v___x_1479_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7___boxed(lean_object* v_sz_1481_, lean_object* v_i_1482_, lean_object* v_bs_1483_){
_start:
{
size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1481_);
lean_dec(v_sz_1481_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1482_);
lean_dec(v_i_1482_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7(v_sz_boxed_1484_, v_i_boxed_1485_, v_bs_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(lean_object* v_msgData_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v_env_1494_; lean_object* v___x_1495_; lean_object* v_mctx_1496_; lean_object* v_lctx_1497_; lean_object* v_options_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1493_ = lean_st_ref_get(v___y_1491_);
v_env_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc_ref(v_env_1494_);
lean_dec(v___x_1493_);
v___x_1495_ = lean_st_ref_get(v___y_1489_);
v_mctx_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc_ref(v_mctx_1496_);
lean_dec(v___x_1495_);
v_lctx_1497_ = lean_ctor_get(v___y_1488_, 2);
v_options_1498_ = lean_ctor_get(v___y_1490_, 2);
lean_inc_ref(v_options_1498_);
lean_inc_ref(v_lctx_1497_);
v___x_1499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1499_, 0, v_env_1494_);
lean_ctor_set(v___x_1499_, 1, v_mctx_1496_);
lean_ctor_set(v___x_1499_, 2, v_lctx_1497_);
lean_ctor_set(v___x_1499_, 3, v_options_1498_);
v___x_1500_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v_msgData_1487_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1___boxed(lean_object* v_msgData_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(v_msgData_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(lean_object* v_oldTraces_1509_, lean_object* v_data_1510_, lean_object* v_ref_1511_, lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_fileName_1518_; lean_object* v_fileMap_1519_; lean_object* v_options_1520_; lean_object* v_currRecDepth_1521_; lean_object* v_maxRecDepth_1522_; lean_object* v_ref_1523_; lean_object* v_currNamespace_1524_; lean_object* v_openDecls_1525_; lean_object* v_initHeartbeats_1526_; lean_object* v_maxHeartbeats_1527_; lean_object* v_quotContext_1528_; lean_object* v_currMacroScope_1529_; uint8_t v_diag_1530_; lean_object* v_cancelTk_x3f_1531_; uint8_t v_suppressElabErrors_1532_; lean_object* v_inheritedTraceOptions_1533_; lean_object* v___x_1534_; lean_object* v_traceState_1535_; lean_object* v_traces_1536_; lean_object* v_ref_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; size_t v_sz_1540_; size_t v___x_1541_; lean_object* v___x_1542_; lean_object* v_msg_1543_; lean_object* v___x_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1582_; 
v_fileName_1518_ = lean_ctor_get(v___y_1515_, 0);
v_fileMap_1519_ = lean_ctor_get(v___y_1515_, 1);
v_options_1520_ = lean_ctor_get(v___y_1515_, 2);
v_currRecDepth_1521_ = lean_ctor_get(v___y_1515_, 3);
v_maxRecDepth_1522_ = lean_ctor_get(v___y_1515_, 4);
v_ref_1523_ = lean_ctor_get(v___y_1515_, 5);
v_currNamespace_1524_ = lean_ctor_get(v___y_1515_, 6);
v_openDecls_1525_ = lean_ctor_get(v___y_1515_, 7);
v_initHeartbeats_1526_ = lean_ctor_get(v___y_1515_, 8);
v_maxHeartbeats_1527_ = lean_ctor_get(v___y_1515_, 9);
v_quotContext_1528_ = lean_ctor_get(v___y_1515_, 10);
v_currMacroScope_1529_ = lean_ctor_get(v___y_1515_, 11);
v_diag_1530_ = lean_ctor_get_uint8(v___y_1515_, sizeof(void*)*14);
v_cancelTk_x3f_1531_ = lean_ctor_get(v___y_1515_, 12);
v_suppressElabErrors_1532_ = lean_ctor_get_uint8(v___y_1515_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1533_ = lean_ctor_get(v___y_1515_, 13);
v___x_1534_ = lean_st_ref_get(v___y_1516_);
v_traceState_1535_ = lean_ctor_get(v___x_1534_, 4);
lean_inc_ref(v_traceState_1535_);
lean_dec(v___x_1534_);
v_traces_1536_ = lean_ctor_get(v_traceState_1535_, 0);
lean_inc_ref(v_traces_1536_);
lean_dec_ref(v_traceState_1535_);
v_ref_1537_ = l_Lean_replaceRef(v_ref_1511_, v_ref_1523_);
lean_inc_ref(v_inheritedTraceOptions_1533_);
lean_inc(v_cancelTk_x3f_1531_);
lean_inc(v_currMacroScope_1529_);
lean_inc(v_quotContext_1528_);
lean_inc(v_maxHeartbeats_1527_);
lean_inc(v_initHeartbeats_1526_);
lean_inc(v_openDecls_1525_);
lean_inc(v_currNamespace_1524_);
lean_inc(v_maxRecDepth_1522_);
lean_inc(v_currRecDepth_1521_);
lean_inc_ref(v_options_1520_);
lean_inc_ref(v_fileMap_1519_);
lean_inc_ref(v_fileName_1518_);
v___x_1538_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1538_, 0, v_fileName_1518_);
lean_ctor_set(v___x_1538_, 1, v_fileMap_1519_);
lean_ctor_set(v___x_1538_, 2, v_options_1520_);
lean_ctor_set(v___x_1538_, 3, v_currRecDepth_1521_);
lean_ctor_set(v___x_1538_, 4, v_maxRecDepth_1522_);
lean_ctor_set(v___x_1538_, 5, v_ref_1537_);
lean_ctor_set(v___x_1538_, 6, v_currNamespace_1524_);
lean_ctor_set(v___x_1538_, 7, v_openDecls_1525_);
lean_ctor_set(v___x_1538_, 8, v_initHeartbeats_1526_);
lean_ctor_set(v___x_1538_, 9, v_maxHeartbeats_1527_);
lean_ctor_set(v___x_1538_, 10, v_quotContext_1528_);
lean_ctor_set(v___x_1538_, 11, v_currMacroScope_1529_);
lean_ctor_set(v___x_1538_, 12, v_cancelTk_x3f_1531_);
lean_ctor_set(v___x_1538_, 13, v_inheritedTraceOptions_1533_);
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*14, v_diag_1530_);
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*14 + 1, v_suppressElabErrors_1532_);
v___x_1539_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1536_);
lean_dec_ref(v_traces_1536_);
v_sz_1540_ = lean_array_size(v___x_1539_);
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6_spec__7(v_sz_1540_, v___x_1541_, v___x_1539_);
v_msg_1543_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1543_, 0, v_data_1510_);
lean_ctor_set(v_msg_1543_, 1, v_msg_1512_);
lean_ctor_set(v_msg_1543_, 2, v___x_1542_);
v___x_1544_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(v_msg_1543_, v___y_1513_, v___y_1514_, v___x_1538_, v___y_1516_);
lean_dec_ref(v___x_1538_);
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1582_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1582_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v_traceState_1550_; lean_object* v_env_1551_; lean_object* v_nextMacroScope_1552_; lean_object* v_ngen_1553_; lean_object* v_auxDeclNGen_1554_; lean_object* v_cache_1555_; lean_object* v_messages_1556_; lean_object* v_infoState_1557_; lean_object* v_snapshotTasks_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1581_; 
v___x_1549_ = lean_st_ref_take(v___y_1516_);
v_traceState_1550_ = lean_ctor_get(v___x_1549_, 4);
v_env_1551_ = lean_ctor_get(v___x_1549_, 0);
v_nextMacroScope_1552_ = lean_ctor_get(v___x_1549_, 1);
v_ngen_1553_ = lean_ctor_get(v___x_1549_, 2);
v_auxDeclNGen_1554_ = lean_ctor_get(v___x_1549_, 3);
v_cache_1555_ = lean_ctor_get(v___x_1549_, 5);
v_messages_1556_ = lean_ctor_get(v___x_1549_, 6);
v_infoState_1557_ = lean_ctor_get(v___x_1549_, 7);
v_snapshotTasks_1558_ = lean_ctor_get(v___x_1549_, 8);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1560_ = v___x_1549_;
v_isShared_1561_ = v_isSharedCheck_1581_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_snapshotTasks_1558_);
lean_inc(v_infoState_1557_);
lean_inc(v_messages_1556_);
lean_inc(v_cache_1555_);
lean_inc(v_traceState_1550_);
lean_inc(v_auxDeclNGen_1554_);
lean_inc(v_ngen_1553_);
lean_inc(v_nextMacroScope_1552_);
lean_inc(v_env_1551_);
lean_dec(v___x_1549_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1581_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
uint64_t v_tid_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1579_; 
v_tid_1562_ = lean_ctor_get_uint64(v_traceState_1550_, sizeof(void*)*1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_traceState_1550_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_traceState_1550_, 0);
lean_dec(v_unused_1580_);
v___x_1564_ = v_traceState_1550_;
v_isShared_1565_ = v_isSharedCheck_1579_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v_traceState_1550_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1579_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v_ref_1511_);
lean_ctor_set(v___x_1566_, 1, v_a_1545_);
v___x_1567_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1509_, v___x_1566_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1567_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1567_);
lean_ctor_set_uint64(v_reuseFailAlloc_1578_, sizeof(void*)*1, v_tid_1562_);
v___x_1569_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 4, v___x_1569_);
v___x_1571_ = v___x_1560_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_env_1551_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_nextMacroScope_1552_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_ngen_1553_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_auxDeclNGen_1554_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1577_, 5, v_cache_1555_);
lean_ctor_set(v_reuseFailAlloc_1577_, 6, v_messages_1556_);
lean_ctor_set(v_reuseFailAlloc_1577_, 7, v_infoState_1557_);
lean_ctor_set(v_reuseFailAlloc_1577_, 8, v_snapshotTasks_1558_);
v___x_1571_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1572_ = lean_st_ref_set(v___y_1516_, v___x_1571_);
v___x_1573_ = lean_box(0);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1573_);
v___x_1575_ = v___x_1547_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg___boxed(lean_object* v_oldTraces_1583_, lean_object* v_data_1584_, lean_object* v_ref_1585_, lean_object* v_msg_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(v_oldTraces_1583_, v_data_1584_, v_ref_1585_, v_msg_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1592_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__0));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1596_; double v___x_1597_; 
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = lean_float_of_nat(v___x_1596_);
return v___x_1597_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__3));
v___x_1600_ = l_Lean_stringToMessageData(v___x_1599_);
return v___x_1600_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1601_; double v___x_1602_; 
v___x_1601_ = lean_unsigned_to_nat(1000u);
v___x_1602_ = lean_float_of_nat(v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(lean_object* v_cls_1603_, uint8_t v_collapsed_1604_, lean_object* v_tag_1605_, lean_object* v_opts_1606_, uint8_t v_clsEnabled_1607_, lean_object* v_oldTraces_1608_, lean_object* v_msg_1609_, lean_object* v_resStartStop_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1717_; 
v_fst_1618_ = lean_ctor_get(v_resStartStop_1610_, 0);
v_snd_1619_ = lean_ctor_get(v_resStartStop_1610_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_resStartStop_1610_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1621_ = v_resStartStop_1610_;
v_isShared_1622_ = v_isSharedCheck_1717_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_snd_1619_);
lean_inc(v_fst_1618_);
lean_dec(v_resStartStop_1610_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1717_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v_data_1626_; lean_object* v_fst_1637_; lean_object* v_snd_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1716_; 
v_fst_1637_ = lean_ctor_get(v_snd_1619_, 0);
v_snd_1638_ = lean_ctor_get(v_snd_1619_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_snd_1619_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1640_ = v_snd_1619_;
v_isShared_1641_ = v_isSharedCheck_1716_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_snd_1638_);
lean_inc(v_fst_1637_);
lean_dec(v_snd_1619_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1716_;
goto v_resetjp_1639_;
}
v___jp_1623_:
{
lean_object* v___x_1627_; 
lean_inc(v___y_1625_);
v___x_1627_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(v_oldTraces_1608_, v_data_1626_, v___y_1625_, v___y_1624_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1628_; 
lean_dec_ref(v___x_1627_);
v___x_1628_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(v_fst_1618_);
return v___x_1628_;
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_fst_1618_);
v_a_1629_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1627_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1627_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___y_1645_; lean_object* v_a_1646_; uint8_t v___y_1670_; double v___y_1701_; 
v___x_1642_ = l_Lean_trace_profiler;
v___x_1643_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_opts_1606_, v___x_1642_);
if (v___x_1643_ == 0)
{
v___y_1670_ = v___x_1643_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1707_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_opts_1606_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; double v___x_1710_; double v___x_1711_; double v___x_1712_; 
v___x_1708_ = l_Lean_trace_profiler_threshold;
v___x_1709_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(v_opts_1606_, v___x_1708_);
v___x_1710_ = lean_float_of_nat(v___x_1709_);
v___x_1711_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__5);
v___x_1712_ = lean_float_div(v___x_1710_, v___x_1711_);
v___y_1701_ = v___x_1712_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; double v___x_1715_; 
v___x_1713_ = l_Lean_trace_profiler_threshold;
v___x_1714_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__8(v_opts_1606_, v___x_1713_);
v___x_1715_ = lean_float_of_nat(v___x_1714_);
v___y_1701_ = v___x_1715_;
goto v___jp_1700_;
}
}
v___jp_1644_:
{
uint8_t v_result_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v_result_1647_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__5(v_fst_1618_);
v___x_1648_ = l_Lean_TraceResult_toEmoji(v_result_1647_);
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
v___x_1650_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__1);
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 7);
lean_ctor_set(v___x_1640_, 1, v___x_1650_);
lean_ctor_set(v___x_1640_, 0, v___x_1649_);
v___x_1652_ = v___x_1640_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v_m_1654_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 7);
lean_ctor_set(v___x_1621_, 1, v_a_1646_);
lean_ctor_set(v___x_1621_, 0, v___x_1652_);
v_m_1654_ = v___x_1621_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_a_1646_);
v_m_1654_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; double v___x_1657_; lean_object* v_data_1658_; 
v___x_1655_ = lean_box(v_result_1647_);
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
v___x_1657_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2);
lean_inc_ref(v_tag_1605_);
lean_inc_ref(v___x_1656_);
lean_inc(v_cls_1603_);
v_data_1658_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1658_, 0, v_cls_1603_);
lean_ctor_set(v_data_1658_, 1, v___x_1656_);
lean_ctor_set(v_data_1658_, 2, v_tag_1605_);
lean_ctor_set_float(v_data_1658_, sizeof(void*)*3, v___x_1657_);
lean_ctor_set_float(v_data_1658_, sizeof(void*)*3 + 8, v___x_1657_);
lean_ctor_set_uint8(v_data_1658_, sizeof(void*)*3 + 16, v_collapsed_1604_);
if (v___x_1643_ == 0)
{
lean_dec_ref(v___x_1656_);
lean_dec(v_snd_1638_);
lean_dec(v_fst_1637_);
lean_dec_ref(v_tag_1605_);
lean_dec(v_cls_1603_);
v___y_1624_ = v_m_1654_;
v___y_1625_ = v___y_1645_;
v_data_1626_ = v_data_1658_;
goto v___jp_1623_;
}
else
{
lean_object* v_data_1659_; double v___x_1660_; double v___x_1661_; 
lean_dec_ref(v_data_1658_);
v_data_1659_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1659_, 0, v_cls_1603_);
lean_ctor_set(v_data_1659_, 1, v___x_1656_);
lean_ctor_set(v_data_1659_, 2, v_tag_1605_);
v___x_1660_ = lean_unbox_float(v_fst_1637_);
lean_dec(v_fst_1637_);
lean_ctor_set_float(v_data_1659_, sizeof(void*)*3, v___x_1660_);
v___x_1661_ = lean_unbox_float(v_snd_1638_);
lean_dec(v_snd_1638_);
lean_ctor_set_float(v_data_1659_, sizeof(void*)*3 + 8, v___x_1661_);
lean_ctor_set_uint8(v_data_1659_, sizeof(void*)*3 + 16, v_collapsed_1604_);
v___y_1624_ = v_m_1654_;
v___y_1625_ = v___y_1645_;
v_data_1626_ = v_data_1659_;
goto v___jp_1623_;
}
}
}
}
v___jp_1664_:
{
lean_object* v_ref_1665_; lean_object* v___x_1666_; 
v_ref_1665_ = lean_ctor_get(v___y_1615_, 5);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc(v_fst_1618_);
v___x_1666_ = lean_apply_8(v_msg_1609_, v_fst_1618_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, lean_box(0));
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v___x_1666_);
v___y_1645_ = v_ref_1665_;
v_a_1646_ = v_a_1667_;
goto v___jp_1644_;
}
else
{
lean_object* v___x_1668_; 
lean_dec_ref(v___x_1666_);
v___x_1668_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__4);
v___y_1645_ = v_ref_1665_;
v_a_1646_ = v___x_1668_;
goto v___jp_1644_;
}
}
v___jp_1669_:
{
if (v_clsEnabled_1607_ == 0)
{
if (v___y_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v_traceState_1672_; lean_object* v_env_1673_; lean_object* v_nextMacroScope_1674_; lean_object* v_ngen_1675_; lean_object* v_auxDeclNGen_1676_; lean_object* v_cache_1677_; lean_object* v_messages_1678_; lean_object* v_infoState_1679_; lean_object* v_snapshotTasks_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1699_; 
lean_del_object(v___x_1640_);
lean_dec(v_snd_1638_);
lean_dec(v_fst_1637_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_msg_1609_);
lean_dec_ref(v_tag_1605_);
lean_dec(v_cls_1603_);
v___x_1671_ = lean_st_ref_take(v___y_1616_);
v_traceState_1672_ = lean_ctor_get(v___x_1671_, 4);
v_env_1673_ = lean_ctor_get(v___x_1671_, 0);
v_nextMacroScope_1674_ = lean_ctor_get(v___x_1671_, 1);
v_ngen_1675_ = lean_ctor_get(v___x_1671_, 2);
v_auxDeclNGen_1676_ = lean_ctor_get(v___x_1671_, 3);
v_cache_1677_ = lean_ctor_get(v___x_1671_, 5);
v_messages_1678_ = lean_ctor_get(v___x_1671_, 6);
v_infoState_1679_ = lean_ctor_get(v___x_1671_, 7);
v_snapshotTasks_1680_ = lean_ctor_get(v___x_1671_, 8);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1682_ = v___x_1671_;
v_isShared_1683_ = v_isSharedCheck_1699_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_snapshotTasks_1680_);
lean_inc(v_infoState_1679_);
lean_inc(v_messages_1678_);
lean_inc(v_cache_1677_);
lean_inc(v_traceState_1672_);
lean_inc(v_auxDeclNGen_1676_);
lean_inc(v_ngen_1675_);
lean_inc(v_nextMacroScope_1674_);
lean_inc(v_env_1673_);
lean_dec(v___x_1671_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1699_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
uint64_t v_tid_1684_; lean_object* v_traces_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1698_; 
v_tid_1684_ = lean_ctor_get_uint64(v_traceState_1672_, sizeof(void*)*1);
v_traces_1685_ = lean_ctor_get(v_traceState_1672_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_traceState_1672_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1687_ = v_traceState_1672_;
v_isShared_1688_ = v_isSharedCheck_1698_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_traces_1685_);
lean_dec(v_traceState_1672_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1698_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1608_, v_traces_1685_);
lean_dec_ref(v_traces_1685_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1689_);
lean_ctor_set_uint64(v_reuseFailAlloc_1697_, sizeof(void*)*1, v_tid_1684_);
v___x_1691_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 4, v___x_1691_);
v___x_1693_ = v___x_1682_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_env_1673_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_nextMacroScope_1674_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_ngen_1675_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_auxDeclNGen_1676_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1696_, 5, v_cache_1677_);
lean_ctor_set(v_reuseFailAlloc_1696_, 6, v_messages_1678_);
lean_ctor_set(v_reuseFailAlloc_1696_, 7, v_infoState_1679_);
lean_ctor_set(v_reuseFailAlloc_1696_, 8, v_snapshotTasks_1680_);
v___x_1693_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_st_ref_set(v___y_1616_, v___x_1693_);
v___x_1695_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(v_fst_1618_);
return v___x_1695_;
}
}
}
}
}
else
{
goto v___jp_1664_;
}
}
else
{
goto v___jp_1664_;
}
}
v___jp_1700_:
{
double v___x_1702_; double v___x_1703_; double v___x_1704_; uint8_t v___x_1705_; 
v___x_1702_ = lean_unbox_float(v_snd_1638_);
v___x_1703_ = lean_unbox_float(v_fst_1637_);
v___x_1704_ = lean_float_sub(v___x_1702_, v___x_1703_);
v___x_1705_ = lean_float_decLt(v___y_1701_, v___x_1704_);
v___y_1670_ = v___x_1705_;
goto v___jp_1669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___boxed(lean_object* v_cls_1718_, lean_object* v_collapsed_1719_, lean_object* v_tag_1720_, lean_object* v_opts_1721_, lean_object* v_clsEnabled_1722_, lean_object* v_oldTraces_1723_, lean_object* v_msg_1724_, lean_object* v_resStartStop_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v_collapsed_boxed_1733_; uint8_t v_clsEnabled_boxed_1734_; lean_object* v_res_1735_; 
v_collapsed_boxed_1733_ = lean_unbox(v_collapsed_1719_);
v_clsEnabled_boxed_1734_ = lean_unbox(v_clsEnabled_1722_);
v_res_1735_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(v_cls_1718_, v_collapsed_boxed_1733_, v_tag_1720_, v_opts_1721_, v_clsEnabled_boxed_1734_, v_oldTraces_1723_, v_msg_1724_, v_resStartStop_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v_opts_1721_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(lean_object* v_cls_1738_, lean_object* v_msg_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_ref_1745_; lean_object* v___x_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1791_; 
v_ref_1745_ = lean_ctor_get(v___y_1742_, 5);
v___x_1746_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1_spec__1(v_msg_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1791_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1791_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v_traceState_1752_; lean_object* v_env_1753_; lean_object* v_nextMacroScope_1754_; lean_object* v_ngen_1755_; lean_object* v_auxDeclNGen_1756_; lean_object* v_cache_1757_; lean_object* v_messages_1758_; lean_object* v_infoState_1759_; lean_object* v_snapshotTasks_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1790_; 
v___x_1751_ = lean_st_ref_take(v___y_1743_);
v_traceState_1752_ = lean_ctor_get(v___x_1751_, 4);
v_env_1753_ = lean_ctor_get(v___x_1751_, 0);
v_nextMacroScope_1754_ = lean_ctor_get(v___x_1751_, 1);
v_ngen_1755_ = lean_ctor_get(v___x_1751_, 2);
v_auxDeclNGen_1756_ = lean_ctor_get(v___x_1751_, 3);
v_cache_1757_ = lean_ctor_get(v___x_1751_, 5);
v_messages_1758_ = lean_ctor_get(v___x_1751_, 6);
v_infoState_1759_ = lean_ctor_get(v___x_1751_, 7);
v_snapshotTasks_1760_ = lean_ctor_get(v___x_1751_, 8);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1762_ = v___x_1751_;
v_isShared_1763_ = v_isSharedCheck_1790_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_snapshotTasks_1760_);
lean_inc(v_infoState_1759_);
lean_inc(v_messages_1758_);
lean_inc(v_cache_1757_);
lean_inc(v_traceState_1752_);
lean_inc(v_auxDeclNGen_1756_);
lean_inc(v_ngen_1755_);
lean_inc(v_nextMacroScope_1754_);
lean_inc(v_env_1753_);
lean_dec(v___x_1751_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1790_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
uint64_t v_tid_1764_; lean_object* v_traces_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1789_; 
v_tid_1764_ = lean_ctor_get_uint64(v_traceState_1752_, sizeof(void*)*1);
v_traces_1765_ = lean_ctor_get(v_traceState_1752_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_traceState_1752_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1767_ = v_traceState_1752_;
v_isShared_1768_ = v_isSharedCheck_1789_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_traces_1765_);
lean_dec(v_traceState_1752_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1789_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; double v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___closed__2);
v___x_1771_ = 0;
v___x_1772_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31));
v___x_1773_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1773_, 0, v_cls_1738_);
lean_ctor_set(v___x_1773_, 1, v___x_1769_);
lean_ctor_set(v___x_1773_, 2, v___x_1772_);
lean_ctor_set_float(v___x_1773_, sizeof(void*)*3, v___x_1770_);
lean_ctor_set_float(v___x_1773_, sizeof(void*)*3 + 8, v___x_1770_);
lean_ctor_set_uint8(v___x_1773_, sizeof(void*)*3 + 16, v___x_1771_);
v___x_1774_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0));
v___x_1775_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v_a_1747_);
lean_ctor_set(v___x_1775_, 2, v___x_1774_);
lean_inc(v_ref_1745_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_ref_1745_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = l_Lean_PersistentArray_push___redArg(v_traces_1765_, v___x_1776_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1777_);
v___x_1779_ = v___x_1767_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1777_);
lean_ctor_set_uint64(v_reuseFailAlloc_1788_, sizeof(void*)*1, v_tid_1764_);
v___x_1779_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 4, v___x_1779_);
v___x_1781_ = v___x_1762_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_env_1753_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_nextMacroScope_1754_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_ngen_1755_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_auxDeclNGen_1756_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1787_, 5, v_cache_1757_);
lean_ctor_set(v_reuseFailAlloc_1787_, 6, v_messages_1758_);
lean_ctor_set(v_reuseFailAlloc_1787_, 7, v_infoState_1759_);
lean_ctor_set(v_reuseFailAlloc_1787_, 8, v_snapshotTasks_1760_);
v___x_1781_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_st_ref_set(v___y_1743_, v___x_1781_);
v___x_1783_ = lean_box(0);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1783_);
v___x_1785_ = v___x_1749_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(lean_object* v_cls_1792_, lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v_cls_1792_, v_msg_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0(lean_object* v_name_1800_, lean_object* v_snd_1801_, lean_object* v_x_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1810_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1);
v___x_1811_ = l_Lean_MessageData_ofName(v_name_1800_);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_snd_1801_);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0___boxed(lean_object* v_name_1818_, lean_object* v_snd_1819_, lean_object* v_x_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0(v_name_1818_, v_snd_1819_, v_x_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_x_1820_);
return v_res_1828_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__1));
v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(lean_object* v_as_x27_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
if (lean_obj_tag(v_as_x27_1834_) == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_b_1835_);
return v___x_1843_;
}
else
{
lean_object* v_head_1844_; lean_object* v_tail_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1982_; 
v_head_1844_ = lean_ctor_get(v_as_x27_1834_, 0);
v_tail_1845_ = lean_ctor_get(v_as_x27_1834_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_as_x27_1834_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1847_ = v_as_x27_1834_;
v_isShared_1848_ = v_isSharedCheck_1982_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_tail_1845_);
lean_inc(v_head_1844_);
lean_dec(v_as_x27_1834_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1982_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_snd_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1980_; 
v_snd_1849_ = lean_ctor_get(v_b_1835_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_b_1835_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v_b_1835_, 0);
lean_dec(v_unused_1981_);
v___x_1851_ = v_b_1835_;
v_isShared_1852_ = v_isSharedCheck_1980_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_snd_1849_);
lean_dec(v_b_1835_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1980_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_options_1859_; lean_object* v_name_1860_; lean_object* v_run_x27_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1979_; 
v_options_1859_ = lean_ctor_get(v___y_1840_, 2);
v_name_1860_ = lean_ctor_get(v_head_1844_, 0);
v_run_x27_1861_ = lean_ctor_get(v_head_1844_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_head_1844_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1863_ = v_head_1844_;
v_isShared_1864_ = v_isSharedCheck_1979_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_run_x27_1861_);
lean_inc(v_name_1860_);
lean_dec(v_head_1844_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1979_;
goto v_resetjp_1862_;
}
v___jp_1853_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__0));
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1854_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_snd_1849_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
v_resetjp_1862_:
{
uint8_t v_hasTrace_1865_; lean_object* v___x_1866_; lean_object* v___y_1868_; 
v_hasTrace_1865_ = lean_ctor_get_uint8(v_options_1859_, sizeof(void*)*1);
v___x_1866_ = lean_box(0);
if (v_hasTrace_1865_ == 0)
{
lean_object* v___x_1897_; 
lean_dec(v_name_1860_);
lean_del_object(v___x_1847_);
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v_snd_1849_);
v___x_1897_ = lean_apply_8(v_run_x27_1861_, v_snd_1849_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, lean_box(0));
v___y_1868_ = v___x_1897_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_a_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v_a_1906_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v_a_1924_; uint8_t v___x_1975_; 
v___x_1898_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27));
v___x_1899_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1898_, v___y_1840_);
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
lean_inc(v_snd_1849_);
v___f_1901_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1901_, 0, v_name_1860_);
lean_closure_set(v___f_1901_, 1, v_snd_1849_);
v___x_1902_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__31));
v___x_1975_ = lean_unbox(v_a_1900_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = l_Lean_trace_profiler;
v___x_1977_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_options_1859_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref(v___f_1901_);
lean_dec(v_a_1900_);
lean_del_object(v___x_1847_);
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v_snd_1849_);
v___x_1978_ = lean_apply_8(v_run_x27_1861_, v_snd_1849_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, lean_box(0));
v___y_1868_ = v___x_1978_;
goto v___jp_1867_;
}
else
{
goto v___jp_1934_;
}
}
else
{
goto v___jp_1934_;
}
v___jp_1903_:
{
lean_object* v___x_1907_; double v___x_1908_; double v___x_1909_; double v___x_1910_; double v___x_1911_; double v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1907_ = lean_io_mono_nanos_now();
v___x_1908_ = lean_float_of_nat(v___y_1904_);
v___x_1909_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__32);
v___x_1910_ = lean_float_div(v___x_1908_, v___x_1909_);
v___x_1911_ = lean_float_of_nat(v___x_1907_);
v___x_1912_ = lean_float_div(v___x_1911_, v___x_1909_);
v___x_1913_ = lean_box_float(v___x_1910_);
v___x_1914_ = lean_box_float(v___x_1912_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 0);
lean_ctor_set(v___x_1847_, 1, v___x_1914_);
lean_ctor_set(v___x_1847_, 0, v___x_1913_);
v___x_1916_ = v___x_1847_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_a_1906_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_unbox(v_a_1900_);
lean_dec(v_a_1900_);
v___x_1919_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(v___x_1898_, v_hasTrace_1865_, v___x_1902_, v_options_1859_, v___x_1918_, v___y_1905_, v___f_1901_, v___x_1917_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
v___y_1868_ = v___x_1919_;
goto v___jp_1867_;
}
}
v___jp_1921_:
{
lean_object* v___x_1925_; double v___x_1926_; double v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1925_ = lean_io_get_num_heartbeats();
v___x_1926_ = lean_float_of_nat(v___y_1922_);
v___x_1927_ = lean_float_of_nat(v___x_1925_);
v___x_1928_ = lean_box_float(v___x_1926_);
v___x_1929_ = lean_box_float(v___x_1927_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v_a_1924_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_unbox(v_a_1900_);
lean_dec(v_a_1900_);
v___x_1933_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(v___x_1898_, v_hasTrace_1865_, v___x_1902_, v_options_1859_, v___x_1932_, v___y_1923_, v___f_1901_, v___x_1931_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
v___y_1868_ = v___x_1933_;
goto v___jp_1867_;
}
v___jp_1934_:
{
lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1935_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___redArg(v___y_1841_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1938_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_options_1859_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_io_mono_nanos_now();
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v_snd_1849_);
v___x_1940_ = lean_apply_8(v_run_x27_1861_, v_snd_1849_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, lean_box(0));
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set_tag(v___x_1943_, 1);
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
v___y_1904_ = v___x_1939_;
v___y_1905_ = v_a_1936_;
v_a_1906_ = v___x_1946_;
goto v___jp_1903_;
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_a_1949_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1940_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1940_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 0);
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
v___y_1904_ = v___x_1939_;
v___y_1905_ = v_a_1936_;
v_a_1906_ = v___x_1954_;
goto v___jp_1903_;
}
}
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_del_object(v___x_1847_);
v___x_1957_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v_snd_1849_);
v___x_1958_ = lean_apply_8(v_run_x27_1861_, v_snd_1849_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, lean_box(0));
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 1);
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
v___y_1922_ = v___x_1957_;
v___y_1923_ = v_a_1936_;
v_a_1924_ = v___x_1964_;
goto v___jp_1921_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1958_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1958_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 0);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v___y_1922_ = v___x_1957_;
v___y_1923_ = v_a_1936_;
v_a_1924_ = v___x_1972_;
goto v___jp_1921_;
}
}
}
}
}
}
v___jp_1867_:
{
if (lean_obj_tag(v___y_1868_) == 0)
{
lean_object* v_a_1869_; 
v_a_1869_ = lean_ctor_get(v___y_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___y_1868_);
if (lean_obj_tag(v_a_1869_) == 1)
{
lean_object* v_val_1870_; lean_object* v___x_1872_; 
lean_del_object(v___x_1851_);
lean_dec(v_snd_1849_);
v_val_1870_ = lean_ctor_get(v_a_1869_, 0);
lean_inc(v_val_1870_);
lean_dec_ref(v_a_1869_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v_val_1870_);
lean_ctor_set(v___x_1863_, 0, v___x_1866_);
v___x_1872_ = v___x_1863_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_val_1870_);
v___x_1872_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
v_as_x27_1834_ = v_tail_1845_;
v_b_1835_ = v___x_1872_;
goto _start;
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v_a_1877_; uint8_t v___x_1878_; 
lean_dec(v_a_1869_);
lean_del_object(v___x_1863_);
lean_dec(v_tail_1845_);
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27));
v___x_1876_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1875_, v___y_1840_);
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = lean_unbox(v_a_1877_);
lean_dec(v_a_1877_);
if (v___x_1878_ == 0)
{
goto v___jp_1853_;
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___closed__2);
v___x_1880_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___x_1875_, v___x_1879_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_dec_ref(v___x_1880_);
goto v___jp_1853_;
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_del_object(v___x_1851_);
lean_dec(v_snd_1849_);
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_del_object(v___x_1863_);
lean_del_object(v___x_1851_);
lean_dec(v_snd_1849_);
lean_dec(v_tail_1845_);
v_a_1889_ = lean_ctor_get(v___y_1868_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___y_1868_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___y_1868_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___y_1868_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg___boxed(lean_object* v_as_x27_1983_, lean_object* v_b_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(v_as_x27_1983_, v_b_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1992_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0));
v___x_1995_ = l_Lean_stringToMessageData(v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(lean_object* v_passes_1999_, lean_object* v_goal_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2008_ = lean_box(0);
lean_inc(v_goal_2000_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v_goal_2000_);
lean_inc(v_passes_1999_);
v___x_2010_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(v_passes_1999_, v___x_2009_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2085_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2085_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2085_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_fst_2015_; lean_object* v_snd_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2084_; 
v_fst_2015_ = lean_ctor_get(v_a_2011_, 0);
v_snd_2016_ = lean_ctor_get(v_a_2011_, 1);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_a_2011_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2018_ = v_a_2011_;
v_isShared_2019_ = v_isSharedCheck_2084_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2016_);
lean_inc(v_fst_2015_);
lean_dec(v_a_2011_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2084_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
if (lean_obj_tag(v_fst_2015_) == 0)
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Lean_instBEqMVarId_beq(v_goal_2000_, v_snd_2016_);
lean_dec(v_goal_2000_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_del_object(v___x_2013_);
v___x_2026_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27));
v___x_2027_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_2026_, v_a_2005_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; uint8_t v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = lean_unbox(v_a_2028_);
lean_dec(v_a_2028_);
if (v___x_2029_ == 0)
{
lean_del_object(v___x_2018_);
v_goal_2000_ = v_snd_2016_;
goto _start;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2031_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1);
lean_inc(v_snd_2016_);
v___x_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2032_, 0, v_snd_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 7);
lean_ctor_set(v___x_2018_, 1, v___x_2032_);
lean_ctor_set(v___x_2018_, 0, v___x_2031_);
v___x_2034_ = v___x_2018_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___x_2026_, v___x_2034_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_dec_ref(v___x_2035_);
v_goal_2000_ = v_snd_2016_;
goto _start;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_snd_2016_);
lean_dec(v_passes_1999_);
v_a_2037_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2035_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2035_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_del_object(v___x_2018_);
lean_dec(v_snd_2016_);
lean_dec(v_passes_1999_);
v_a_2046_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2027_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2027_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_del_object(v___x_2018_);
lean_dec(v_passes_1999_);
v___x_2054_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27));
v___x_2055_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_2054_, v_a_2005_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; uint8_t v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = lean_unbox(v_a_2056_);
lean_dec(v_a_2056_);
if (v___x_2057_ == 0)
{
goto v___jp_2020_;
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3);
v___x_2059_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___x_2054_, v___x_2058_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_dec_ref(v___x_2059_);
goto v___jp_2020_;
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_snd_2016_);
lean_del_object(v___x_2013_);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_snd_2016_);
lean_del_object(v___x_2013_);
v_a_2068_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2055_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2055_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
else
{
lean_object* v_val_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_del_object(v___x_2018_);
lean_dec(v_snd_2016_);
lean_del_object(v___x_2013_);
lean_dec(v_goal_2000_);
lean_dec(v_passes_1999_);
v_val_2076_ = lean_ctor_get(v_fst_2015_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_fst_2015_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v_fst_2015_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_val_2076_);
lean_dec(v_fst_2015_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 0);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_val_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
v___jp_2020_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_snd_2016_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2021_);
v___x_2023_ = v___x_2013_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_goal_2000_);
lean_dec(v_passes_1999_);
v_a_2086_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2010_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2010_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_2094_, lean_object* v_goal_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(v_passes_2094_, v_goal_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1(lean_object* v_cls_2104_, lean_object* v_msg_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v_cls_2104_, v_msg_2105_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___boxed(lean_object* v_cls_2114_, lean_object* v_msg_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1(v_cls_2114_, v_msg_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7(lean_object* v_00_u03b1_2124_, lean_object* v_x_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___redArg(v_x_2125_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2134_, lean_object* v_x_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__7(v_00_u03b1_2134_, v_x_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(lean_object* v_as_2144_, lean_object* v_as_x27_2145_, lean_object* v_b_2146_, lean_object* v_a_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___redArg(v_as_x27_2145_, v_b_2146_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5___boxed(lean_object* v_as_2156_, lean_object* v_as_x27_2157_, lean_object* v_b_2158_, lean_object* v_a_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(v_as_2156_, v_as_x27_2157_, v_b_2158_, v_a_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v_as_2156_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6(lean_object* v_oldTraces_2168_, lean_object* v_data_2169_, lean_object* v_ref_2170_, lean_object* v_msg_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___redArg(v_oldTraces_2168_, v_data_2169_, v_ref_2170_, v_msg_2171_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6___boxed(lean_object* v_oldTraces_2180_, lean_object* v_data_2181_, lean_object* v_ref_2182_, lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4_spec__6(v_oldTraces_2180_, v_data_2181_, v_ref_2182_, v_msg_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2191_;
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
