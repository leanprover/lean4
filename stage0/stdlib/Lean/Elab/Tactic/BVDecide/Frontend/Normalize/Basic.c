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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
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
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultOption___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__22_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__23_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__24_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__27_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Fixpoint iteration solved the goal"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Rerunning pipeline on:\n"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pipeline reached a fixpoint"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_742_; lean_object* v_toApplicative_743_; lean_object* v_toFunctor_744_; lean_object* v_toSeq_745_; lean_object* v_toSeqLeft_746_; lean_object* v_toSeqRight_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_toApplicative_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_837_; 
v___x_742_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_743_ = lean_ctor_get(v___x_742_, 0);
v_toFunctor_744_ = lean_ctor_get(v_toApplicative_743_, 0);
v_toSeq_745_ = lean_ctor_get(v_toApplicative_743_, 2);
v_toSeqLeft_746_ = lean_ctor_get(v_toApplicative_743_, 3);
v_toSeqRight_747_ = lean_ctor_get(v_toApplicative_743_, 4);
v___f_748_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2));
v___f_749_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_744_, 2);
v___f_750_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_750_, 0, v_toFunctor_744_);
v___f_751_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_751_, 0, v_toFunctor_744_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___f_750_);
lean_ctor_set(v___x_752_, 1, v___f_751_);
lean_inc(v_toSeqRight_747_);
v___f_753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_753_, 0, v_toSeqRight_747_);
lean_inc(v_toSeqLeft_746_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_754_, 0, v_toSeqLeft_746_);
lean_inc(v_toSeq_745_);
v___f_755_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_755_, 0, v_toSeq_745_);
v___x_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_756_, 0, v___x_752_);
lean_ctor_set(v___x_756_, 1, v___f_748_);
lean_ctor_set(v___x_756_, 2, v___f_755_);
lean_ctor_set(v___x_756_, 3, v___f_754_);
lean_ctor_set(v___x_756_, 4, v___f_753_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___f_749_);
v___x_758_ = l_StateRefT_x27_instMonad___redArg(v___x_757_);
v_toApplicative_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v___x_758_, 1);
lean_dec(v_unused_838_);
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_837_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_toApplicative_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_837_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_toFunctor_763_; lean_object* v_toSeq_764_; lean_object* v_toSeqLeft_765_; lean_object* v_toSeqRight_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_835_; 
v_toFunctor_763_ = lean_ctor_get(v_toApplicative_759_, 0);
v_toSeq_764_ = lean_ctor_get(v_toApplicative_759_, 2);
v_toSeqLeft_765_ = lean_ctor_get(v_toApplicative_759_, 3);
v_toSeqRight_766_ = lean_ctor_get(v_toApplicative_759_, 4);
v_isSharedCheck_835_ = !lean_is_exclusive(v_toApplicative_759_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v_toApplicative_759_, 1);
lean_dec(v_unused_836_);
v___x_768_ = v_toApplicative_759_;
v_isShared_769_ = v_isSharedCheck_835_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_toSeqRight_766_);
lean_inc(v_toSeqLeft_765_);
lean_inc(v_toSeq_764_);
lean_inc(v_toFunctor_763_);
lean_dec(v_toApplicative_759_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_835_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___x_779_; 
v___f_770_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4));
v___f_771_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5));
lean_inc_ref(v_toFunctor_763_);
v___f_772_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_772_, 0, v_toFunctor_763_);
v___f_773_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_773_, 0, v_toFunctor_763_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___f_772_);
lean_ctor_set(v___x_774_, 1, v___f_773_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_775_, 0, v_toSeqRight_766_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_776_, 0, v_toSeqLeft_765_);
v___f_777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_777_, 0, v_toSeq_764_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 4, v___f_775_);
lean_ctor_set(v___x_768_, 3, v___f_776_);
lean_ctor_set(v___x_768_, 2, v___f_777_);
lean_ctor_set(v___x_768_, 1, v___f_770_);
lean_ctor_set(v___x_768_, 0, v___x_774_);
v___x_779_ = v___x_768_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___f_770_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v___f_777_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v___f_776_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v___f_775_);
v___x_779_ = v_reuseFailAlloc_834_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___f_771_);
lean_ctor_set(v___x_761_, 0, v___x_779_);
v___x_781_ = v___x_761_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___f_771_);
v___x_781_ = v_reuseFailAlloc_833_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v_toApplicative_782_; lean_object* v_toFunctor_783_; lean_object* v_toSeq_784_; lean_object* v_toSeqLeft_785_; lean_object* v_toSeqRight_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_664__overap_799_; lean_object* v___x_800_; 
v_toApplicative_782_ = lean_ctor_get(v___x_742_, 0);
v_toFunctor_783_ = lean_ctor_get(v_toApplicative_782_, 0);
v_toSeq_784_ = lean_ctor_get(v_toApplicative_782_, 2);
v_toSeqLeft_785_ = lean_ctor_get(v_toApplicative_782_, 3);
v_toSeqRight_786_ = lean_ctor_get(v_toApplicative_782_, 4);
lean_inc_ref_n(v_toFunctor_783_, 2);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_787_, 0, v_toFunctor_783_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_788_, 0, v_toFunctor_783_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___f_787_);
lean_ctor_set(v___x_789_, 1, v___f_788_);
lean_inc(v_toSeqRight_786_);
v___f_790_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_790_, 0, v_toSeqRight_786_);
lean_inc(v_toSeqLeft_785_);
v___f_791_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_791_, 0, v_toSeqLeft_785_);
lean_inc(v_toSeq_784_);
v___f_792_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_792_, 0, v_toSeq_784_);
v___x_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_793_, 0, v___x_789_);
lean_ctor_set(v___x_793_, 1, v___f_748_);
lean_ctor_set(v___x_793_, 2, v___f_792_);
lean_ctor_set(v___x_793_, 3, v___f_791_);
lean_ctor_set(v___x_793_, 4, v___f_790_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___f_749_);
v___x_795_ = l_StateRefT_x27_instMonad___redArg(v___x_794_);
v___x_796_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_796_, 0, lean_box(0));
lean_closure_set(v___x_796_, 1, lean_box(0));
lean_closure_set(v___x_796_, 2, v___x_795_);
v___x_797_ = l_instMonadControlTOfPure___redArg(v___x_796_);
v___x_798_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6));
v___x_664__overap_799_ = l_Lean_MVarId_withContext___redArg(v___x_797_, v___x_781_, v_goal_735_, v___x_798_);
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
v___x_800_ = lean_apply_5(v___x_664__overap_799_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, lean_box(0));
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v___x_800_);
v___x_802_ = lean_array_get_size(v_a_801_);
lean_dec(v_a_801_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_unsigned_to_nat(4u);
v___x_805_ = lean_nat_mul(v___x_802_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(3u);
v___x_807_ = lean_nat_div(v___x_805_, v___x_806_);
lean_dec(v___x_805_);
v___x_808_ = l_Nat_nextPowerOfTwo(v___x_807_);
lean_dec(v___x_807_);
v___x_809_ = lean_box(0);
v___x_810_ = lean_mk_array(v___x_808_, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_803_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9);
lean_inc_ref(v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
v___x_814_ = lean_st_mk_ref(v___x_813_);
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
lean_inc(v___x_814_);
v___x_815_ = lean_apply_7(v_x_736_, v_cfg_734_, v___x_814_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, lean_box(0));
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_st_ref_get(v___x_814_);
lean_dec(v___x_814_);
lean_dec(v___x_820_);
if (v_isShared_819_ == 0)
{
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_816_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
else
{
lean_dec(v___x_814_);
return v___x_815_;
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v_x_736_);
lean_dec_ref(v_cfg_734_);
v_a_825_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_800_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_800_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_cfg_839_, lean_object* v_goal_840_, lean_object* v_x_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg(v_cfg_839_, v_goal_840_, v_x_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run(lean_object* v_00_u03b1_848_, lean_object* v_cfg_849_, lean_object* v_goal_850_, lean_object* v_x_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; lean_object* v_toApplicative_858_; lean_object* v_toFunctor_859_; lean_object* v_toSeq_860_; lean_object* v_toSeqLeft_861_; lean_object* v_toSeqRight_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_toApplicative_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_952_; 
v___x_857_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_858_ = lean_ctor_get(v___x_857_, 0);
v_toFunctor_859_ = lean_ctor_get(v_toApplicative_858_, 0);
v_toSeq_860_ = lean_ctor_get(v_toApplicative_858_, 2);
v_toSeqLeft_861_ = lean_ctor_get(v_toApplicative_858_, 3);
v_toSeqRight_862_ = lean_ctor_get(v_toApplicative_858_, 4);
v___f_863_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2));
v___f_864_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_859_, 2);
v___f_865_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_865_, 0, v_toFunctor_859_);
v___f_866_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_866_, 0, v_toFunctor_859_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___f_865_);
lean_ctor_set(v___x_867_, 1, v___f_866_);
lean_inc(v_toSeqRight_862_);
v___f_868_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_868_, 0, v_toSeqRight_862_);
lean_inc(v_toSeqLeft_861_);
v___f_869_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_869_, 0, v_toSeqLeft_861_);
lean_inc(v_toSeq_860_);
v___f_870_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_870_, 0, v_toSeq_860_);
v___x_871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_871_, 0, v___x_867_);
lean_ctor_set(v___x_871_, 1, v___f_863_);
lean_ctor_set(v___x_871_, 2, v___f_870_);
lean_ctor_set(v___x_871_, 3, v___f_869_);
lean_ctor_set(v___x_871_, 4, v___f_868_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___f_864_);
v___x_873_ = l_StateRefT_x27_instMonad___redArg(v___x_872_);
v_toApplicative_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v___x_873_, 1);
lean_dec(v_unused_953_);
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_952_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_toApplicative_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_952_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_toFunctor_878_; lean_object* v_toSeq_879_; lean_object* v_toSeqLeft_880_; lean_object* v_toSeqRight_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_950_; 
v_toFunctor_878_ = lean_ctor_get(v_toApplicative_874_, 0);
v_toSeq_879_ = lean_ctor_get(v_toApplicative_874_, 2);
v_toSeqLeft_880_ = lean_ctor_get(v_toApplicative_874_, 3);
v_toSeqRight_881_ = lean_ctor_get(v_toApplicative_874_, 4);
v_isSharedCheck_950_ = !lean_is_exclusive(v_toApplicative_874_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_toApplicative_874_, 1);
lean_dec(v_unused_951_);
v___x_883_ = v_toApplicative_874_;
v_isShared_884_ = v_isSharedCheck_950_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_toSeqRight_881_);
lean_inc(v_toSeqLeft_880_);
lean_inc(v_toSeq_879_);
lean_inc(v_toFunctor_878_);
lean_dec(v_toApplicative_874_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_950_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___x_894_; 
v___f_885_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4));
v___f_886_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5));
lean_inc_ref(v_toFunctor_878_);
v___f_887_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_887_, 0, v_toFunctor_878_);
v___f_888_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_888_, 0, v_toFunctor_878_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___f_887_);
lean_ctor_set(v___x_889_, 1, v___f_888_);
v___f_890_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_890_, 0, v_toSeqRight_881_);
v___f_891_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_891_, 0, v_toSeqLeft_880_);
v___f_892_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_892_, 0, v_toSeq_879_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 4, v___f_890_);
lean_ctor_set(v___x_883_, 3, v___f_891_);
lean_ctor_set(v___x_883_, 2, v___f_892_);
lean_ctor_set(v___x_883_, 1, v___f_885_);
lean_ctor_set(v___x_883_, 0, v___x_889_);
v___x_894_ = v___x_883_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___f_885_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v___f_892_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v___f_891_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v___f_890_);
v___x_894_ = v_reuseFailAlloc_949_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___f_886_);
lean_ctor_set(v___x_876_, 0, v___x_894_);
v___x_896_ = v___x_876_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___f_886_);
v___x_896_ = v_reuseFailAlloc_948_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v_toApplicative_897_; lean_object* v_toFunctor_898_; lean_object* v_toSeq_899_; lean_object* v_toSeqLeft_900_; lean_object* v_toSeqRight_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___f_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_887__overap_914_; lean_object* v___x_915_; 
v_toApplicative_897_ = lean_ctor_get(v___x_857_, 0);
v_toFunctor_898_ = lean_ctor_get(v_toApplicative_897_, 0);
v_toSeq_899_ = lean_ctor_get(v_toApplicative_897_, 2);
v_toSeqLeft_900_ = lean_ctor_get(v_toApplicative_897_, 3);
v_toSeqRight_901_ = lean_ctor_get(v_toApplicative_897_, 4);
lean_inc_ref_n(v_toFunctor_898_, 2);
v___f_902_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_902_, 0, v_toFunctor_898_);
v___f_903_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_903_, 0, v_toFunctor_898_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___f_902_);
lean_ctor_set(v___x_904_, 1, v___f_903_);
lean_inc(v_toSeqRight_901_);
v___f_905_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_905_, 0, v_toSeqRight_901_);
lean_inc(v_toSeqLeft_900_);
v___f_906_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_906_, 0, v_toSeqLeft_900_);
lean_inc(v_toSeq_899_);
v___f_907_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_907_, 0, v_toSeq_899_);
v___x_908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_908_, 0, v___x_904_);
lean_ctor_set(v___x_908_, 1, v___f_863_);
lean_ctor_set(v___x_908_, 2, v___f_907_);
lean_ctor_set(v___x_908_, 3, v___f_906_);
lean_ctor_set(v___x_908_, 4, v___f_905_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___f_864_);
v___x_910_ = l_StateRefT_x27_instMonad___redArg(v___x_909_);
v___x_911_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_911_, 0, lean_box(0));
lean_closure_set(v___x_911_, 1, lean_box(0));
lean_closure_set(v___x_911_, 2, v___x_910_);
v___x_912_ = l_instMonadControlTOfPure___redArg(v___x_911_);
v___x_913_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__6));
v___x_887__overap_914_ = l_Lean_MVarId_withContext___redArg(v___x_912_, v___x_896_, v_goal_850_, v___x_913_);
lean_inc(v_a_855_);
lean_inc_ref(v_a_854_);
lean_inc(v_a_853_);
lean_inc_ref(v_a_852_);
v___x_915_ = lean_apply_5(v___x_887__overap_914_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, lean_box(0));
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref(v___x_915_);
v___x_917_ = lean_array_get_size(v_a_916_);
lean_dec(v_a_916_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = lean_nat_mul(v___x_917_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(3u);
v___x_922_ = lean_nat_div(v___x_920_, v___x_921_);
lean_dec(v___x_920_);
v___x_923_ = l_Nat_nextPowerOfTwo(v___x_922_);
lean_dec(v___x_922_);
v___x_924_ = lean_box(0);
v___x_925_ = lean_mk_array(v___x_923_, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_918_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__9);
lean_inc_ref(v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_926_);
lean_ctor_set(v___x_928_, 2, v___x_927_);
v___x_929_ = lean_st_mk_ref(v___x_928_);
lean_inc(v_a_855_);
lean_inc_ref(v_a_854_);
lean_inc(v_a_853_);
lean_inc_ref(v_a_852_);
lean_inc(v___x_929_);
v___x_930_ = lean_apply_7(v_x_851_, v_cfg_849_, v___x_929_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, lean_box(0));
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_st_ref_get(v___x_929_);
lean_dec(v___x_929_);
lean_dec(v___x_935_);
if (v_isShared_934_ == 0)
{
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_931_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
lean_dec(v___x_929_);
return v___x_930_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_x_851_);
lean_dec_ref(v_cfg_849_);
v_a_940_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_915_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_915_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_954_, lean_object* v_cfg_955_, lean_object* v_goal_956_, lean_object* v_x_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run(v_00_u03b1_954_, v_cfg_955_, v_goal_956_, v_x_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_963_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__0));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__2));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0(lean_object* v_name_970_, lean_object* v_goal_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_980_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1);
v___x_981_ = l_Lean_MessageData_ofName(v_name_970_);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_goal_971_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_988_, lean_object* v_goal_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0(v_name_988_, v_goal_989_, v_x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v_x_990_);
return v_res_998_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1003_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__2);
v___f_1005_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___x_1006_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1005_, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__3);
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1009_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1008_, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__4);
v___f_1011_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___x_1012_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7));
v___x_1018_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1017_, v___x_1016_, v___x_1015_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___x_1022_; 
v___x_1019_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__8);
v___f_1020_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1021_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6));
v___x_1022_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1021_, v___f_1020_, v___x_1019_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1023_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__9);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__7));
v___x_1026_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1025_, v___x_1024_, v___x_1023_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; 
v___x_1027_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__10);
v___f_1028_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1029_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__6));
v___x_1030_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1029_, v___f_1028_, v___x_1027_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12(void){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__12);
v___x_1033_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__13);
v___x_1035_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__14);
v___x_1037_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__15);
v___x_1039_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__16);
v___x_1041_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__17);
v___x_1043_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___f_1046_; 
v___x_1044_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__1));
v___x_1045_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1046_, 0, v___x_1045_);
lean_closure_set(v___f_1046_, 1, v___x_1044_);
return v___f_1046_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20(void){
_start:
{
lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; 
v___f_1047_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__0));
v___f_1048_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__19);
v___f_1049_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1049_, 0, v___f_1048_);
lean_closure_set(v___f_1049_, 1, v___f_1047_);
return v___f_1049_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25));
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__28));
v___x_1064_ = l_Lean_Name_append(v___x_1063_, v___x_1062_);
return v___x_1064_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30(void){
_start:
{
lean_object* v___x_1065_; double v___x_1066_; 
v___x_1065_ = lean_unsigned_to_nat(1000000000u);
v___x_1066_ = lean_float_of_nat(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run(lean_object* v_pass_1067_, lean_object* v_goal_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; lean_object* v_toApplicative_1077_; lean_object* v_toFunctor_1078_; lean_object* v_toSeq_1079_; lean_object* v_toSeqLeft_1080_; lean_object* v_toSeqRight_1081_; lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_toApplicative_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1232_; 
v___x_1076_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_1077_ = lean_ctor_get(v___x_1076_, 0);
v_toFunctor_1078_ = lean_ctor_get(v_toApplicative_1077_, 0);
v_toSeq_1079_ = lean_ctor_get(v_toApplicative_1077_, 2);
v_toSeqLeft_1080_ = lean_ctor_get(v_toApplicative_1077_, 3);
v_toSeqRight_1081_ = lean_ctor_get(v_toApplicative_1077_, 4);
v___f_1082_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__2));
v___f_1083_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1078_, 2);
v___f_1084_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1084_, 0, v_toFunctor_1078_);
v___f_1085_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1085_, 0, v_toFunctor_1078_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___f_1084_);
lean_ctor_set(v___x_1086_, 1, v___f_1085_);
lean_inc(v_toSeqRight_1081_);
v___f_1087_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1087_, 0, v_toSeqRight_1081_);
lean_inc(v_toSeqLeft_1080_);
v___f_1088_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1088_, 0, v_toSeqLeft_1080_);
lean_inc(v_toSeq_1079_);
v___f_1089_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1089_, 0, v_toSeq_1079_);
v___x_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1086_);
lean_ctor_set(v___x_1090_, 1, v___f_1082_);
lean_ctor_set(v___x_1090_, 2, v___f_1089_);
lean_ctor_set(v___x_1090_, 3, v___f_1088_);
lean_ctor_set(v___x_1090_, 4, v___f_1087_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___f_1083_);
v___x_1092_ = l_StateRefT_x27_instMonad___redArg(v___x_1091_);
v_toApplicative_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v___x_1092_, 1);
lean_dec(v_unused_1233_);
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1232_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_toApplicative_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1232_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_toFunctor_1097_; lean_object* v_toSeq_1098_; lean_object* v_toSeqLeft_1099_; lean_object* v_toSeqRight_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1230_; 
v_toFunctor_1097_ = lean_ctor_get(v_toApplicative_1093_, 0);
v_toSeq_1098_ = lean_ctor_get(v_toApplicative_1093_, 2);
v_toSeqLeft_1099_ = lean_ctor_get(v_toApplicative_1093_, 3);
v_toSeqRight_1100_ = lean_ctor_get(v_toApplicative_1093_, 4);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_toApplicative_1093_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_toApplicative_1093_, 1);
lean_dec(v_unused_1231_);
v___x_1102_ = v_toApplicative_1093_;
v_isShared_1103_ = v_isSharedCheck_1230_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_toSeqRight_1100_);
lean_inc(v_toSeqLeft_1099_);
lean_inc(v_toSeq_1098_);
lean_inc(v_toFunctor_1097_);
lean_dec(v_toApplicative_1093_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1230_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1113_; 
v___f_1104_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__4));
v___f_1105_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_PreProcessM_run___redArg___closed__5));
lean_inc_ref(v_toFunctor_1097_);
v___f_1106_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1106_, 0, v_toFunctor_1097_);
v___f_1107_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1107_, 0, v_toFunctor_1097_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___f_1106_);
lean_ctor_set(v___x_1108_, 1, v___f_1107_);
v___f_1109_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1109_, 0, v_toSeqRight_1100_);
v___f_1110_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1110_, 0, v_toSeqLeft_1099_);
v___f_1111_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1111_, 0, v_toSeq_1098_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v___f_1109_);
lean_ctor_set(v___x_1102_, 3, v___f_1110_);
lean_ctor_set(v___x_1102_, 2, v___f_1111_);
lean_ctor_set(v___x_1102_, 1, v___f_1104_);
lean_ctor_set(v___x_1102_, 0, v___x_1108_);
v___x_1113_ = v___x_1102_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___f_1104_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v___f_1111_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v___f_1110_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v___f_1109_);
v___x_1113_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v___f_1105_);
lean_ctor_set(v___x_1095_, 0, v___x_1113_);
v___x_1115_ = v___x_1095_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___f_1105_);
v___x_1115_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_toMonadRef_1120_; lean_object* v___x_1121_; lean_object* v_options_1122_; uint8_t v_hasTrace_1123_; 
v___x_1116_ = l_StateRefT_x27_instMonad___redArg(v___x_1115_);
v___x_1117_ = l_ReaderT_instMonad___redArg(v___x_1116_);
v___x_1118_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__5);
v___x_1119_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__11);
v_toMonadRef_1120_ = lean_ctor_get(v___x_1119_, 0);
v___x_1121_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__18);
v_options_1122_ = lean_ctor_get(v_a_1073_, 2);
v_hasTrace_1123_ = lean_ctor_get_uint8(v_options_1122_, sizeof(void*)*1);
if (v_hasTrace_1123_ == 0)
{
lean_object* v_run_x27_1124_; lean_object* v___x_1125_; 
lean_dec_ref(v___x_1117_);
v_run_x27_1124_ = lean_ctor_get(v_pass_1067_, 1);
lean_inc_ref(v_run_x27_1124_);
lean_dec_ref(v_pass_1067_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1125_ = lean_apply_8(v_run_x27_1124_, v_goal_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
return v___x_1125_;
}
else
{
lean_object* v_name_1126_; lean_object* v_run_x27_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1227_; 
v_name_1126_ = lean_ctor_get(v_pass_1067_, 0);
v_run_x27_1127_ = lean_ctor_get(v_pass_1067_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_pass_1067_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1129_ = v_pass_1067_;
v_isShared_1130_ = v_isSharedCheck_1227_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_run_x27_1127_);
lean_inc(v_name_1126_);
lean_dec(v_pass_1067_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1227_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_inheritedTraceOptions_1131_; lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v_a_1142_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v_a_1160_; 
v_inheritedTraceOptions_1131_ = lean_ctor_get(v_a_1073_, 13);
lean_inc(v_goal_1068_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1132_, 0, v_name_1126_);
lean_closure_set(v___f_1132_, 1, v_goal_1068_);
v___f_1133_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__20);
v___f_1134_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__21));
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25));
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26));
v___x_1137_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29);
v___x_1138_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1131_, v_options_1122_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1222_ = l_Lean_KVMap_instValueBool;
v___x_1223_ = l_Lean_trace_profiler;
v___x_1224_ = l_Lean_Option_get___redArg(v___x_1222_, v_options_1122_, v___x_1223_);
v___x_1225_ = lean_unbox(v___x_1224_);
lean_dec(v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v___f_1132_);
lean_del_object(v___x_1129_);
lean_dec_ref(v___x_1117_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1226_ = lean_apply_8(v_run_x27_1127_, v_goal_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
return v___x_1226_;
}
else
{
goto v___jp_1170_;
}
}
else
{
goto v___jp_1170_;
}
v___jp_1139_:
{
lean_object* v___x_1143_; double v___x_1144_; double v___x_1145_; double v___x_1146_; double v___x_1147_; double v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1143_ = lean_io_mono_nanos_now();
v___x_1144_ = lean_float_of_nat(v___y_1140_);
v___x_1145_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30);
v___x_1146_ = lean_float_div(v___x_1144_, v___x_1145_);
v___x_1147_ = lean_float_of_nat(v___x_1143_);
v___x_1148_ = lean_float_div(v___x_1147_, v___x_1145_);
v___x_1149_ = lean_box_float(v___x_1146_);
v___x_1150_ = lean_box_float(v___x_1148_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 1, v___x_1150_);
lean_ctor_set(v___x_1129_, 0, v___x_1149_);
v___x_1152_ = v___x_1129_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_9547__overap_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_a_1142_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
lean_inc_ref(v_toMonadRef_1120_);
v___x_9547__overap_1154_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_1117_, v___x_1118_, v_toMonadRef_1120_, v___f_1133_, lean_box(0), v___x_1121_, v___f_1134_, v___x_1135_, v_hasTrace_1123_, v___x_1136_, v_options_1122_, v___x_1138_, v___y_1141_, v___f_1132_, v___x_1153_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1155_ = lean_apply_7(v___x_9547__overap_1154_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
return v___x_1155_;
}
}
v___jp_1157_:
{
lean_object* v___x_1161_; double v___x_1162_; double v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_9568__overap_1168_; lean_object* v___x_1169_; 
v___x_1161_ = lean_io_get_num_heartbeats();
v___x_1162_ = lean_float_of_nat(v___y_1159_);
v___x_1163_ = lean_float_of_nat(v___x_1161_);
v___x_1164_ = lean_box_float(v___x_1162_);
v___x_1165_ = lean_box_float(v___x_1163_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1160_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
lean_inc_ref(v_toMonadRef_1120_);
v___x_9568__overap_1168_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_1117_, v___x_1118_, v_toMonadRef_1120_, v___f_1133_, lean_box(0), v___x_1121_, v___f_1134_, v___x_1135_, v_hasTrace_1123_, v___x_1136_, v_options_1122_, v___x_1138_, v___y_1158_, v___f_1132_, v___x_1167_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1169_ = lean_apply_7(v___x_9568__overap_1168_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
return v___x_1169_;
}
v___jp_1170_:
{
lean_object* v___x_9524__overap_1171_; lean_object* v___x_1172_; 
lean_inc_ref(v___x_1117_);
v___x_9524__overap_1171_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_1117_, v___x_1118_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1172_ = lean_apply_7(v___x_9524__overap_1171_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = l_Lean_KVMap_instValueBool;
v___x_1175_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1176_ = l_Lean_Option_get___redArg(v___x_1174_, v_options_1122_, v___x_1175_);
v___x_1177_ = lean_unbox(v___x_1176_);
lean_dec(v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_io_mono_nanos_now();
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1179_ = lean_apply_8(v_run_x27_1127_, v_goal_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 1);
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
v___y_1140_ = v___x_1178_;
v___y_1141_ = v_a_1173_;
v_a_1142_ = v___x_1185_;
goto v___jp_1139_;
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
v_a_1188_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1179_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1179_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set_tag(v___x_1190_, 0);
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
v___y_1140_ = v___x_1178_;
v___y_1141_ = v_a_1173_;
v_a_1142_ = v___x_1193_;
goto v___jp_1139_;
}
}
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_del_object(v___x_1129_);
v___x_1196_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1197_ = lean_apply_8(v_run_x27_1127_, v_goal_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 1);
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
v___y_1158_ = v_a_1173_;
v___y_1159_ = v___x_1196_;
v_a_1160_ = v___x_1203_;
goto v___jp_1157_;
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1206_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1197_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 0);
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
v___y_1158_ = v_a_1173_;
v___y_1159_ = v___x_1196_;
v_a_1160_ = v___x_1211_;
goto v___jp_1157_;
}
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v___f_1132_);
lean_del_object(v___x_1129_);
lean_dec_ref(v_run_x27_1127_);
lean_dec_ref(v___x_1117_);
lean_dec(v_goal_1068_);
v_a_1214_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1172_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1172_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___boxed(lean_object* v_pass_1234_, lean_object* v_goal_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run(v_pass_1234_, v_goal_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1243_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(32u);
v___x_1245_ = lean_mk_empty_array_with_capacity(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1247_ = ((size_t)5ULL);
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = lean_unsigned_to_nat(32u);
v___x_1250_ = lean_mk_empty_array_with_capacity(v___x_1249_);
v___x_1251_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0);
v___x_1252_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1250_);
lean_ctor_set(v___x_1252_, 2, v___x_1248_);
lean_ctor_set(v___x_1252_, 3, v___x_1248_);
lean_ctor_set_usize(v___x_1252_, 4, v___x_1247_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v_traceState_1256_; lean_object* v_traces_1257_; lean_object* v___x_1258_; lean_object* v_traceState_1259_; lean_object* v_env_1260_; lean_object* v_nextMacroScope_1261_; lean_object* v_ngen_1262_; lean_object* v_auxDeclNGen_1263_; lean_object* v_cache_1264_; lean_object* v_messages_1265_; lean_object* v_infoState_1266_; lean_object* v_snapshotTasks_1267_; lean_object* v_newDecls_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1287_; 
v___x_1255_ = lean_st_ref_get(v___y_1253_);
v_traceState_1256_ = lean_ctor_get(v___x_1255_, 4);
lean_inc_ref(v_traceState_1256_);
lean_dec(v___x_1255_);
v_traces_1257_ = lean_ctor_get(v_traceState_1256_, 0);
lean_inc_ref(v_traces_1257_);
lean_dec_ref(v_traceState_1256_);
v___x_1258_ = lean_st_ref_take(v___y_1253_);
v_traceState_1259_ = lean_ctor_get(v___x_1258_, 4);
v_env_1260_ = lean_ctor_get(v___x_1258_, 0);
v_nextMacroScope_1261_ = lean_ctor_get(v___x_1258_, 1);
v_ngen_1262_ = lean_ctor_get(v___x_1258_, 2);
v_auxDeclNGen_1263_ = lean_ctor_get(v___x_1258_, 3);
v_cache_1264_ = lean_ctor_get(v___x_1258_, 5);
v_messages_1265_ = lean_ctor_get(v___x_1258_, 6);
v_infoState_1266_ = lean_ctor_get(v___x_1258_, 7);
v_snapshotTasks_1267_ = lean_ctor_get(v___x_1258_, 8);
v_newDecls_1268_ = lean_ctor_get(v___x_1258_, 9);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1270_ = v___x_1258_;
v_isShared_1271_ = v_isSharedCheck_1287_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_newDecls_1268_);
lean_inc(v_snapshotTasks_1267_);
lean_inc(v_infoState_1266_);
lean_inc(v_messages_1265_);
lean_inc(v_cache_1264_);
lean_inc(v_traceState_1259_);
lean_inc(v_auxDeclNGen_1263_);
lean_inc(v_ngen_1262_);
lean_inc(v_nextMacroScope_1261_);
lean_inc(v_env_1260_);
lean_dec(v___x_1258_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1287_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
uint64_t v_tid_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1285_; 
v_tid_1272_ = lean_ctor_get_uint64(v_traceState_1259_, sizeof(void*)*1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_traceState_1259_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v_traceState_1259_, 0);
lean_dec(v_unused_1286_);
v___x_1274_ = v_traceState_1259_;
v_isShared_1275_ = v_isSharedCheck_1285_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v_traceState_1259_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1285_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1276_);
lean_ctor_set_uint64(v_reuseFailAlloc_1284_, sizeof(void*)*1, v_tid_1272_);
v___x_1278_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 4, v___x_1278_);
v___x_1280_ = v___x_1270_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_env_1260_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_nextMacroScope_1261_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_ngen_1262_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_auxDeclNGen_1263_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1283_, 5, v_cache_1264_);
lean_ctor_set(v_reuseFailAlloc_1283_, 6, v_messages_1265_);
lean_ctor_set(v_reuseFailAlloc_1283_, 7, v_infoState_1266_);
lean_ctor_set(v_reuseFailAlloc_1283_, 8, v_snapshotTasks_1267_);
lean_ctor_set(v_reuseFailAlloc_1283_, 9, v_newDecls_1268_);
v___x_1280_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_st_ref_set(v___y_1253_, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_traces_1257_);
return v___x_1282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_1288_);
lean_dec(v___y_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1(lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___boxed(lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1(v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1306_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(lean_object* v_opts_1307_, lean_object* v_opt_1308_){
_start:
{
lean_object* v_name_1309_; lean_object* v_defValue_1310_; lean_object* v_map_1311_; lean_object* v___x_1312_; 
v_name_1309_ = lean_ctor_get(v_opt_1308_, 0);
v_defValue_1310_ = lean_ctor_get(v_opt_1308_, 1);
v_map_1311_ = lean_ctor_get(v_opts_1307_, 0);
v___x_1312_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1311_, v_name_1309_);
if (lean_obj_tag(v___x_1312_) == 0)
{
uint8_t v___x_1313_; 
v___x_1313_ = lean_unbox(v_defValue_1310_);
return v___x_1313_;
}
else
{
lean_object* v_val_1314_; 
v_val_1314_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1314_);
lean_dec_ref(v___x_1312_);
if (lean_obj_tag(v_val_1314_) == 1)
{
uint8_t v_v_1315_; 
v_v_1315_ = lean_ctor_get_uint8(v_val_1314_, 0);
lean_dec_ref(v_val_1314_);
return v_v_1315_;
}
else
{
uint8_t v___x_1316_; 
lean_dec(v_val_1314_);
v___x_1316_ = lean_unbox(v_defValue_1310_);
return v___x_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2___boxed(lean_object* v_opts_1317_, lean_object* v_opt_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(v_opts_1317_, v_opt_1318_);
lean_dec_ref(v_opt_1318_);
lean_dec_ref(v_opts_1317_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__4(lean_object* v_e_1321_){
_start:
{
if (lean_obj_tag(v_e_1321_) == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = 2;
return v___x_1322_;
}
else
{
lean_object* v_a_1323_; 
v_a_1323_ = lean_ctor_get(v_e_1321_, 0);
if (lean_obj_tag(v_a_1323_) == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = 1;
return v___x_1324_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = 0;
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__4___boxed(lean_object* v_e_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__4(v_e_1326_);
lean_dec_ref(v_e_1326_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(size_t v_sz_1329_, size_t v_i_1330_, lean_object* v_bs_1331_){
_start:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_usize_dec_lt(v_i_1330_, v_sz_1329_);
if (v___x_1332_ == 0)
{
return v_bs_1331_;
}
else
{
lean_object* v_v_1333_; lean_object* v_msg_1334_; lean_object* v___x_1335_; lean_object* v_bs_x27_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v_v_1333_ = lean_array_uget_borrowed(v_bs_1331_, v_i_1330_);
v_msg_1334_ = lean_ctor_get(v_v_1333_, 1);
lean_inc_ref(v_msg_1334_);
v___x_1335_ = lean_unsigned_to_nat(0u);
v_bs_x27_1336_ = lean_array_uset(v_bs_1331_, v_i_1330_, v___x_1335_);
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1330_, v___x_1337_);
v___x_1339_ = lean_array_uset(v_bs_x27_1336_, v_i_1330_, v_msg_1334_);
v_i_1330_ = v___x_1338_;
v_bs_1331_ = v___x_1339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6___boxed(lean_object* v_sz_1341_, lean_object* v_i_1342_, lean_object* v_bs_1343_){
_start:
{
size_t v_sz_boxed_1344_; size_t v_i_boxed_1345_; lean_object* v_res_1346_; 
v_sz_boxed_1344_ = lean_unbox_usize(v_sz_1341_);
lean_dec(v_sz_1341_);
v_i_boxed_1345_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(v_sz_boxed_1344_, v_i_boxed_1345_, v_bs_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0(lean_object* v_msgData_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v_env_1354_; lean_object* v___x_1355_; lean_object* v_mctx_1356_; lean_object* v_lctx_1357_; lean_object* v_options_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1353_ = lean_st_ref_get(v___y_1351_);
v_env_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc_ref(v_env_1354_);
lean_dec(v___x_1353_);
v___x_1355_ = lean_st_ref_get(v___y_1349_);
v_mctx_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_ref(v_mctx_1356_);
lean_dec(v___x_1355_);
v_lctx_1357_ = lean_ctor_get(v___y_1348_, 2);
v_options_1358_ = lean_ctor_get(v___y_1350_, 2);
lean_inc_ref(v_options_1358_);
lean_inc_ref(v_lctx_1357_);
v___x_1359_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1359_, 0, v_env_1354_);
lean_ctor_set(v___x_1359_, 1, v_mctx_1356_);
lean_ctor_set(v___x_1359_, 2, v_lctx_1357_);
lean_ctor_set(v___x_1359_, 3, v_options_1358_);
v___x_1360_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v_msgData_1347_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___boxed(lean_object* v_msgData_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msgData_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(lean_object* v_oldTraces_1369_, lean_object* v_data_1370_, lean_object* v_ref_1371_, lean_object* v_msg_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_fileName_1378_; lean_object* v_fileMap_1379_; lean_object* v_options_1380_; lean_object* v_currRecDepth_1381_; lean_object* v_maxRecDepth_1382_; lean_object* v_ref_1383_; lean_object* v_currNamespace_1384_; lean_object* v_openDecls_1385_; lean_object* v_initHeartbeats_1386_; lean_object* v_maxHeartbeats_1387_; lean_object* v_quotContext_1388_; lean_object* v_currMacroScope_1389_; uint8_t v_diag_1390_; lean_object* v_cancelTk_x3f_1391_; uint8_t v_suppressElabErrors_1392_; lean_object* v_inheritedTraceOptions_1393_; lean_object* v___x_1394_; lean_object* v_traceState_1395_; lean_object* v_traces_1396_; lean_object* v_ref_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; size_t v_sz_1400_; size_t v___x_1401_; lean_object* v___x_1402_; lean_object* v_msg_1403_; lean_object* v___x_1404_; lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1443_; 
v_fileName_1378_ = lean_ctor_get(v___y_1375_, 0);
v_fileMap_1379_ = lean_ctor_get(v___y_1375_, 1);
v_options_1380_ = lean_ctor_get(v___y_1375_, 2);
v_currRecDepth_1381_ = lean_ctor_get(v___y_1375_, 3);
v_maxRecDepth_1382_ = lean_ctor_get(v___y_1375_, 4);
v_ref_1383_ = lean_ctor_get(v___y_1375_, 5);
v_currNamespace_1384_ = lean_ctor_get(v___y_1375_, 6);
v_openDecls_1385_ = lean_ctor_get(v___y_1375_, 7);
v_initHeartbeats_1386_ = lean_ctor_get(v___y_1375_, 8);
v_maxHeartbeats_1387_ = lean_ctor_get(v___y_1375_, 9);
v_quotContext_1388_ = lean_ctor_get(v___y_1375_, 10);
v_currMacroScope_1389_ = lean_ctor_get(v___y_1375_, 11);
v_diag_1390_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*14);
v_cancelTk_x3f_1391_ = lean_ctor_get(v___y_1375_, 12);
v_suppressElabErrors_1392_ = lean_ctor_get_uint8(v___y_1375_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1393_ = lean_ctor_get(v___y_1375_, 13);
v___x_1394_ = lean_st_ref_get(v___y_1376_);
v_traceState_1395_ = lean_ctor_get(v___x_1394_, 4);
lean_inc_ref(v_traceState_1395_);
lean_dec(v___x_1394_);
v_traces_1396_ = lean_ctor_get(v_traceState_1395_, 0);
lean_inc_ref(v_traces_1396_);
lean_dec_ref(v_traceState_1395_);
v_ref_1397_ = l_Lean_replaceRef(v_ref_1371_, v_ref_1383_);
lean_inc_ref(v_inheritedTraceOptions_1393_);
lean_inc(v_cancelTk_x3f_1391_);
lean_inc(v_currMacroScope_1389_);
lean_inc(v_quotContext_1388_);
lean_inc(v_maxHeartbeats_1387_);
lean_inc(v_initHeartbeats_1386_);
lean_inc(v_openDecls_1385_);
lean_inc(v_currNamespace_1384_);
lean_inc(v_maxRecDepth_1382_);
lean_inc(v_currRecDepth_1381_);
lean_inc_ref(v_options_1380_);
lean_inc_ref(v_fileMap_1379_);
lean_inc_ref(v_fileName_1378_);
v___x_1398_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1398_, 0, v_fileName_1378_);
lean_ctor_set(v___x_1398_, 1, v_fileMap_1379_);
lean_ctor_set(v___x_1398_, 2, v_options_1380_);
lean_ctor_set(v___x_1398_, 3, v_currRecDepth_1381_);
lean_ctor_set(v___x_1398_, 4, v_maxRecDepth_1382_);
lean_ctor_set(v___x_1398_, 5, v_ref_1397_);
lean_ctor_set(v___x_1398_, 6, v_currNamespace_1384_);
lean_ctor_set(v___x_1398_, 7, v_openDecls_1385_);
lean_ctor_set(v___x_1398_, 8, v_initHeartbeats_1386_);
lean_ctor_set(v___x_1398_, 9, v_maxHeartbeats_1387_);
lean_ctor_set(v___x_1398_, 10, v_quotContext_1388_);
lean_ctor_set(v___x_1398_, 11, v_currMacroScope_1389_);
lean_ctor_set(v___x_1398_, 12, v_cancelTk_x3f_1391_);
lean_ctor_set(v___x_1398_, 13, v_inheritedTraceOptions_1393_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*14, v_diag_1390_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*14 + 1, v_suppressElabErrors_1392_);
v___x_1399_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1396_);
lean_dec_ref(v_traces_1396_);
v_sz_1400_ = lean_array_size(v___x_1399_);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(v_sz_1400_, v___x_1401_, v___x_1399_);
v_msg_1403_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1403_, 0, v_data_1370_);
lean_ctor_set(v_msg_1403_, 1, v_msg_1372_);
lean_ctor_set(v_msg_1403_, 2, v___x_1402_);
v___x_1404_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msg_1403_, v___y_1373_, v___y_1374_, v___x_1398_, v___y_1376_);
lean_dec_ref(v___x_1398_);
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1443_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1443_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v_traceState_1410_; lean_object* v_env_1411_; lean_object* v_nextMacroScope_1412_; lean_object* v_ngen_1413_; lean_object* v_auxDeclNGen_1414_; lean_object* v_cache_1415_; lean_object* v_messages_1416_; lean_object* v_infoState_1417_; lean_object* v_snapshotTasks_1418_; lean_object* v_newDecls_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1442_; 
v___x_1409_ = lean_st_ref_take(v___y_1376_);
v_traceState_1410_ = lean_ctor_get(v___x_1409_, 4);
v_env_1411_ = lean_ctor_get(v___x_1409_, 0);
v_nextMacroScope_1412_ = lean_ctor_get(v___x_1409_, 1);
v_ngen_1413_ = lean_ctor_get(v___x_1409_, 2);
v_auxDeclNGen_1414_ = lean_ctor_get(v___x_1409_, 3);
v_cache_1415_ = lean_ctor_get(v___x_1409_, 5);
v_messages_1416_ = lean_ctor_get(v___x_1409_, 6);
v_infoState_1417_ = lean_ctor_get(v___x_1409_, 7);
v_snapshotTasks_1418_ = lean_ctor_get(v___x_1409_, 8);
v_newDecls_1419_ = lean_ctor_get(v___x_1409_, 9);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1421_ = v___x_1409_;
v_isShared_1422_ = v_isSharedCheck_1442_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_newDecls_1419_);
lean_inc(v_snapshotTasks_1418_);
lean_inc(v_infoState_1417_);
lean_inc(v_messages_1416_);
lean_inc(v_cache_1415_);
lean_inc(v_traceState_1410_);
lean_inc(v_auxDeclNGen_1414_);
lean_inc(v_ngen_1413_);
lean_inc(v_nextMacroScope_1412_);
lean_inc(v_env_1411_);
lean_dec(v___x_1409_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1442_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
uint64_t v_tid_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1440_; 
v_tid_1423_ = lean_ctor_get_uint64(v_traceState_1410_, sizeof(void*)*1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_traceState_1410_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_traceState_1410_, 0);
lean_dec(v_unused_1441_);
v___x_1425_ = v_traceState_1410_;
v_isShared_1426_ = v_isSharedCheck_1440_;
goto v_resetjp_1424_;
}
else
{
lean_dec(v_traceState_1410_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1440_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_ref_1371_);
lean_ctor_set(v___x_1427_, 1, v_a_1405_);
v___x_1428_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1369_, v___x_1427_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1428_);
v___x_1430_ = v___x_1425_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1428_);
lean_ctor_set_uint64(v_reuseFailAlloc_1439_, sizeof(void*)*1, v_tid_1423_);
v___x_1430_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1432_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 4, v___x_1430_);
v___x_1432_ = v___x_1421_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_env_1411_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_nextMacroScope_1412_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_ngen_1413_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_auxDeclNGen_1414_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1438_, 5, v_cache_1415_);
lean_ctor_set(v_reuseFailAlloc_1438_, 6, v_messages_1416_);
lean_ctor_set(v_reuseFailAlloc_1438_, 7, v_infoState_1417_);
lean_ctor_set(v_reuseFailAlloc_1438_, 8, v_snapshotTasks_1418_);
lean_ctor_set(v_reuseFailAlloc_1438_, 9, v_newDecls_1419_);
v___x_1432_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1433_ = lean_st_ref_set(v___y_1376_, v___x_1432_);
v___x_1434_ = lean_box(0);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1434_);
v___x_1436_ = v___x_1407_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg___boxed(lean_object* v_oldTraces_1444_, lean_object* v_data_1445_, lean_object* v_ref_1446_, lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_1444_, v_data_1445_, v_ref_1446_, v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(lean_object* v_x_1454_){
_start:
{
if (lean_obj_tag(v_x_1454_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_a_1456_ = lean_ctor_get(v_x_1454_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1454_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v_x_1454_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v_x_1454_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 1);
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1464_ = lean_ctor_get(v_x_1454_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_x_1454_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v_x_1454_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v_x_1454_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 0);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg___boxed(lean_object* v_x_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_x_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__7(lean_object* v_opts_1475_, lean_object* v_opt_1476_){
_start:
{
lean_object* v_name_1477_; lean_object* v_defValue_1478_; lean_object* v_map_1479_; lean_object* v___x_1480_; 
v_name_1477_ = lean_ctor_get(v_opt_1476_, 0);
v_defValue_1478_ = lean_ctor_get(v_opt_1476_, 1);
v_map_1479_ = lean_ctor_get(v_opts_1475_, 0);
v___x_1480_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1479_, v_name_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_inc(v_defValue_1478_);
return v_defValue_1478_;
}
else
{
lean_object* v_val_1481_; 
v_val_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_val_1481_);
lean_dec_ref(v___x_1480_);
if (lean_obj_tag(v_val_1481_) == 3)
{
lean_object* v_v_1482_; 
v_v_1482_ = lean_ctor_get(v_val_1481_, 0);
lean_inc(v_v_1482_);
lean_dec_ref(v_val_1481_);
return v_v_1482_;
}
else
{
lean_dec(v_val_1481_);
lean_inc(v_defValue_1478_);
return v_defValue_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__7___boxed(lean_object* v_opts_1483_, lean_object* v_opt_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_1483_, v_opt_1484_);
lean_dec_ref(v_opt_1484_);
lean_dec_ref(v_opts_1483_);
return v_res_1485_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__0));
v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
return v___x_1488_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1489_; double v___x_1490_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_float_of_nat(v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__3));
v___x_1493_ = l_Lean_stringToMessageData(v___x_1492_);
return v___x_1493_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__5(void){
_start:
{
lean_object* v___x_1494_; double v___x_1495_; 
v___x_1494_ = lean_unsigned_to_nat(1000u);
v___x_1495_ = lean_float_of_nat(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(lean_object* v_cls_1496_, uint8_t v_collapsed_1497_, lean_object* v_tag_1498_, lean_object* v_opts_1499_, uint8_t v_clsEnabled_1500_, lean_object* v_oldTraces_1501_, lean_object* v_msg_1502_, lean_object* v_resStartStop_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1611_; 
v_fst_1511_ = lean_ctor_get(v_resStartStop_1503_, 0);
v_snd_1512_ = lean_ctor_get(v_resStartStop_1503_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_resStartStop_1503_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1514_ = v_resStartStop_1503_;
v_isShared_1515_ = v_isSharedCheck_1611_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_inc(v_fst_1511_);
lean_dec(v_resStartStop_1503_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1611_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v_data_1519_; lean_object* v_fst_1530_; lean_object* v_snd_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1610_; 
v_fst_1530_ = lean_ctor_get(v_snd_1512_, 0);
v_snd_1531_ = lean_ctor_get(v_snd_1512_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_snd_1512_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1533_ = v_snd_1512_;
v_isShared_1534_ = v_isSharedCheck_1610_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_snd_1531_);
lean_inc(v_fst_1530_);
lean_dec(v_snd_1512_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1610_;
goto v_resetjp_1532_;
}
v___jp_1516_:
{
lean_object* v___x_1520_; 
lean_inc(v___y_1517_);
v___x_1520_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_1501_, v_data_1519_, v___y_1517_, v___y_1518_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1521_; 
lean_dec_ref(v___x_1520_);
v___x_1521_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_fst_1511_);
return v___x_1521_;
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v_fst_1511_);
v_a_1522_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1520_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1520_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___y_1538_; lean_object* v_a_1539_; uint8_t v___y_1563_; double v___y_1595_; 
v___x_1535_ = l_Lean_trace_profiler;
v___x_1536_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(v_opts_1499_, v___x_1535_);
if (v___x_1536_ == 0)
{
v___y_1563_ = v___x_1536_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1601_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(v_opts_1499_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; double v___x_1604_; double v___x_1605_; double v___x_1606_; 
v___x_1602_ = l_Lean_trace_profiler_threshold;
v___x_1603_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_1499_, v___x_1602_);
v___x_1604_ = lean_float_of_nat(v___x_1603_);
v___x_1605_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__5);
v___x_1606_ = lean_float_div(v___x_1604_, v___x_1605_);
v___y_1595_ = v___x_1606_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; double v___x_1609_; 
v___x_1607_ = l_Lean_trace_profiler_threshold;
v___x_1608_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_1499_, v___x_1607_);
v___x_1609_ = lean_float_of_nat(v___x_1608_);
v___y_1595_ = v___x_1609_;
goto v___jp_1594_;
}
}
v___jp_1537_:
{
uint8_t v_result_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v_result_1540_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__4(v_fst_1511_);
v___x_1541_ = l_Lean_TraceResult_toEmoji(v_result_1540_);
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
v___x_1543_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__1);
if (v_isShared_1534_ == 0)
{
lean_ctor_set_tag(v___x_1533_, 7);
lean_ctor_set(v___x_1533_, 1, v___x_1543_);
lean_ctor_set(v___x_1533_, 0, v___x_1542_);
v___x_1545_ = v___x_1533_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v_m_1547_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 7);
lean_ctor_set(v___x_1514_, 1, v_a_1539_);
lean_ctor_set(v___x_1514_, 0, v___x_1545_);
v_m_1547_ = v___x_1514_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_a_1539_);
v_m_1547_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; double v___x_1550_; lean_object* v_data_1551_; 
v___x_1548_ = lean_box(v_result_1540_);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
v___x_1550_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2);
lean_inc_ref(v_tag_1498_);
lean_inc_ref(v___x_1549_);
lean_inc(v_cls_1496_);
v_data_1551_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1551_, 0, v_cls_1496_);
lean_ctor_set(v_data_1551_, 1, v___x_1549_);
lean_ctor_set(v_data_1551_, 2, v_tag_1498_);
lean_ctor_set_float(v_data_1551_, sizeof(void*)*3, v___x_1550_);
lean_ctor_set_float(v_data_1551_, sizeof(void*)*3 + 8, v___x_1550_);
lean_ctor_set_uint8(v_data_1551_, sizeof(void*)*3 + 16, v_collapsed_1497_);
if (v___x_1536_ == 0)
{
lean_dec_ref(v___x_1549_);
lean_dec(v_snd_1531_);
lean_dec(v_fst_1530_);
lean_dec_ref(v_tag_1498_);
lean_dec(v_cls_1496_);
v___y_1517_ = v___y_1538_;
v___y_1518_ = v_m_1547_;
v_data_1519_ = v_data_1551_;
goto v___jp_1516_;
}
else
{
lean_object* v_data_1552_; double v___x_1553_; double v___x_1554_; 
lean_dec_ref(v_data_1551_);
v_data_1552_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1552_, 0, v_cls_1496_);
lean_ctor_set(v_data_1552_, 1, v___x_1549_);
lean_ctor_set(v_data_1552_, 2, v_tag_1498_);
v___x_1553_ = lean_unbox_float(v_fst_1530_);
lean_dec(v_fst_1530_);
lean_ctor_set_float(v_data_1552_, sizeof(void*)*3, v___x_1553_);
v___x_1554_ = lean_unbox_float(v_snd_1531_);
lean_dec(v_snd_1531_);
lean_ctor_set_float(v_data_1552_, sizeof(void*)*3 + 8, v___x_1554_);
lean_ctor_set_uint8(v_data_1552_, sizeof(void*)*3 + 16, v_collapsed_1497_);
v___y_1517_ = v___y_1538_;
v___y_1518_ = v_m_1547_;
v_data_1519_ = v_data_1552_;
goto v___jp_1516_;
}
}
}
}
v___jp_1557_:
{
lean_object* v_ref_1558_; lean_object* v___x_1559_; 
v_ref_1558_ = lean_ctor_get(v___y_1508_, 5);
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v_fst_1511_);
v___x_1559_ = lean_apply_8(v_msg_1502_, v_fst_1511_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, lean_box(0));
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1559_);
v___y_1538_ = v_ref_1558_;
v_a_1539_ = v_a_1560_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1561_; 
lean_dec_ref(v___x_1559_);
v___x_1561_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__4);
v___y_1538_ = v_ref_1558_;
v_a_1539_ = v___x_1561_;
goto v___jp_1537_;
}
}
v___jp_1562_:
{
if (v_clsEnabled_1500_ == 0)
{
if (v___y_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v_traceState_1565_; lean_object* v_env_1566_; lean_object* v_nextMacroScope_1567_; lean_object* v_ngen_1568_; lean_object* v_auxDeclNGen_1569_; lean_object* v_cache_1570_; lean_object* v_messages_1571_; lean_object* v_infoState_1572_; lean_object* v_snapshotTasks_1573_; lean_object* v_newDecls_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1593_; 
lean_del_object(v___x_1533_);
lean_dec(v_snd_1531_);
lean_dec(v_fst_1530_);
lean_del_object(v___x_1514_);
lean_dec_ref(v_msg_1502_);
lean_dec_ref(v_tag_1498_);
lean_dec(v_cls_1496_);
v___x_1564_ = lean_st_ref_take(v___y_1509_);
v_traceState_1565_ = lean_ctor_get(v___x_1564_, 4);
v_env_1566_ = lean_ctor_get(v___x_1564_, 0);
v_nextMacroScope_1567_ = lean_ctor_get(v___x_1564_, 1);
v_ngen_1568_ = lean_ctor_get(v___x_1564_, 2);
v_auxDeclNGen_1569_ = lean_ctor_get(v___x_1564_, 3);
v_cache_1570_ = lean_ctor_get(v___x_1564_, 5);
v_messages_1571_ = lean_ctor_get(v___x_1564_, 6);
v_infoState_1572_ = lean_ctor_get(v___x_1564_, 7);
v_snapshotTasks_1573_ = lean_ctor_get(v___x_1564_, 8);
v_newDecls_1574_ = lean_ctor_get(v___x_1564_, 9);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1576_ = v___x_1564_;
v_isShared_1577_ = v_isSharedCheck_1593_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_newDecls_1574_);
lean_inc(v_snapshotTasks_1573_);
lean_inc(v_infoState_1572_);
lean_inc(v_messages_1571_);
lean_inc(v_cache_1570_);
lean_inc(v_traceState_1565_);
lean_inc(v_auxDeclNGen_1569_);
lean_inc(v_ngen_1568_);
lean_inc(v_nextMacroScope_1567_);
lean_inc(v_env_1566_);
lean_dec(v___x_1564_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1593_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
uint64_t v_tid_1578_; lean_object* v_traces_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1592_; 
v_tid_1578_ = lean_ctor_get_uint64(v_traceState_1565_, sizeof(void*)*1);
v_traces_1579_ = lean_ctor_get(v_traceState_1565_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_traceState_1565_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1581_ = v_traceState_1565_;
v_isShared_1582_ = v_isSharedCheck_1592_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_traces_1579_);
lean_dec(v_traceState_1565_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1592_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1501_, v_traces_1579_);
lean_dec_ref(v_traces_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1583_);
lean_ctor_set_uint64(v_reuseFailAlloc_1591_, sizeof(void*)*1, v_tid_1578_);
v___x_1585_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 4, v___x_1585_);
v___x_1587_ = v___x_1576_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_env_1566_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_nextMacroScope_1567_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_ngen_1568_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_auxDeclNGen_1569_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1590_, 5, v_cache_1570_);
lean_ctor_set(v_reuseFailAlloc_1590_, 6, v_messages_1571_);
lean_ctor_set(v_reuseFailAlloc_1590_, 7, v_infoState_1572_);
lean_ctor_set(v_reuseFailAlloc_1590_, 8, v_snapshotTasks_1573_);
lean_ctor_set(v_reuseFailAlloc_1590_, 9, v_newDecls_1574_);
v___x_1587_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_st_ref_set(v___y_1509_, v___x_1587_);
v___x_1589_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_fst_1511_);
return v___x_1589_;
}
}
}
}
}
else
{
goto v___jp_1557_;
}
}
else
{
goto v___jp_1557_;
}
}
v___jp_1594_:
{
double v___x_1596_; double v___x_1597_; double v___x_1598_; uint8_t v___x_1599_; 
v___x_1596_ = lean_unbox_float(v_snd_1531_);
v___x_1597_ = lean_unbox_float(v_fst_1530_);
v___x_1598_ = lean_float_sub(v___x_1596_, v___x_1597_);
v___x_1599_ = lean_float_decLt(v___y_1595_, v___x_1598_);
v___y_1563_ = v___x_1599_;
goto v___jp_1562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___boxed(lean_object* v_cls_1612_, lean_object* v_collapsed_1613_, lean_object* v_tag_1614_, lean_object* v_opts_1615_, lean_object* v_clsEnabled_1616_, lean_object* v_oldTraces_1617_, lean_object* v_msg_1618_, lean_object* v_resStartStop_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v_collapsed_boxed_1627_; uint8_t v_clsEnabled_boxed_1628_; lean_object* v_res_1629_; 
v_collapsed_boxed_1627_ = lean_unbox(v_collapsed_1613_);
v_clsEnabled_boxed_1628_ = lean_unbox(v_clsEnabled_1616_);
v_res_1629_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v_cls_1612_, v_collapsed_boxed_1627_, v_tag_1614_, v_opts_1615_, v_clsEnabled_boxed_1628_, v_oldTraces_1617_, v_msg_1618_, v_resStartStop_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_opts_1615_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(lean_object* v_name_1630_, lean_object* v_snd_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__1);
v___x_1641_ = l_Lean_MessageData_ofName(v_name_1630_);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___lam__0___closed__3);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_snd_1631_);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed(lean_object* v_name_1648_, lean_object* v_snd_1649_, lean_object* v_x_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(v_name_1648_, v_snd_1649_, v_x_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_x_1650_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(lean_object* v_cls_1661_, lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_ref_1668_; lean_object* v___x_1669_; lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1715_; 
v_ref_1668_ = lean_ctor_get(v___y_1665_, 5);
v___x_1669_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msg_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1715_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1715_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v_traceState_1675_; lean_object* v_env_1676_; lean_object* v_nextMacroScope_1677_; lean_object* v_ngen_1678_; lean_object* v_auxDeclNGen_1679_; lean_object* v_cache_1680_; lean_object* v_messages_1681_; lean_object* v_infoState_1682_; lean_object* v_snapshotTasks_1683_; lean_object* v_newDecls_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1714_; 
v___x_1674_ = lean_st_ref_take(v___y_1666_);
v_traceState_1675_ = lean_ctor_get(v___x_1674_, 4);
v_env_1676_ = lean_ctor_get(v___x_1674_, 0);
v_nextMacroScope_1677_ = lean_ctor_get(v___x_1674_, 1);
v_ngen_1678_ = lean_ctor_get(v___x_1674_, 2);
v_auxDeclNGen_1679_ = lean_ctor_get(v___x_1674_, 3);
v_cache_1680_ = lean_ctor_get(v___x_1674_, 5);
v_messages_1681_ = lean_ctor_get(v___x_1674_, 6);
v_infoState_1682_ = lean_ctor_get(v___x_1674_, 7);
v_snapshotTasks_1683_ = lean_ctor_get(v___x_1674_, 8);
v_newDecls_1684_ = lean_ctor_get(v___x_1674_, 9);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1686_ = v___x_1674_;
v_isShared_1687_ = v_isSharedCheck_1714_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_newDecls_1684_);
lean_inc(v_snapshotTasks_1683_);
lean_inc(v_infoState_1682_);
lean_inc(v_messages_1681_);
lean_inc(v_cache_1680_);
lean_inc(v_traceState_1675_);
lean_inc(v_auxDeclNGen_1679_);
lean_inc(v_ngen_1678_);
lean_inc(v_nextMacroScope_1677_);
lean_inc(v_env_1676_);
lean_dec(v___x_1674_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1714_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
uint64_t v_tid_1688_; lean_object* v_traces_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1713_; 
v_tid_1688_ = lean_ctor_get_uint64(v_traceState_1675_, sizeof(void*)*1);
v_traces_1689_ = lean_ctor_get(v_traceState_1675_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_traceState_1675_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1691_ = v_traceState_1675_;
v_isShared_1692_ = v_isSharedCheck_1713_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_traces_1689_);
lean_dec(v_traceState_1675_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1713_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; double v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1693_ = lean_box(0);
v___x_1694_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3___closed__2);
v___x_1695_ = 0;
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26));
v___x_1697_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1697_, 0, v_cls_1661_);
lean_ctor_set(v___x_1697_, 1, v___x_1693_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
lean_ctor_set_float(v___x_1697_, sizeof(void*)*3, v___x_1694_);
lean_ctor_set_float(v___x_1697_, sizeof(void*)*3 + 8, v___x_1694_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*3 + 16, v___x_1695_);
v___x_1698_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0));
v___x_1699_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v_a_1670_);
lean_ctor_set(v___x_1699_, 2, v___x_1698_);
lean_inc(v_ref_1668_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_ref_1668_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = l_Lean_PersistentArray_push___redArg(v_traces_1689_, v___x_1700_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1701_);
v___x_1703_ = v___x_1691_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1701_);
lean_ctor_set_uint64(v_reuseFailAlloc_1712_, sizeof(void*)*1, v_tid_1688_);
v___x_1703_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1705_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 4, v___x_1703_);
v___x_1705_ = v___x_1686_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_env_1676_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_nextMacroScope_1677_);
lean_ctor_set(v_reuseFailAlloc_1711_, 2, v_ngen_1678_);
lean_ctor_set(v_reuseFailAlloc_1711_, 3, v_auxDeclNGen_1679_);
lean_ctor_set(v_reuseFailAlloc_1711_, 4, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1711_, 5, v_cache_1680_);
lean_ctor_set(v_reuseFailAlloc_1711_, 6, v_messages_1681_);
lean_ctor_set(v_reuseFailAlloc_1711_, 7, v_infoState_1682_);
lean_ctor_set(v_reuseFailAlloc_1711_, 8, v_snapshotTasks_1683_);
lean_ctor_set(v_reuseFailAlloc_1711_, 9, v_newDecls_1684_);
v___x_1705_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1706_ = lean_st_ref_set(v___y_1666_, v___x_1705_);
v___x_1707_ = lean_box(0);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1707_);
v___x_1709_ = v___x_1672_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg___boxed(lean_object* v_cls_1716_, lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_1716_, v_msg_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1723_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1));
v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg(lean_object* v_as_x27_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
if (lean_obj_tag(v_as_x27_1729_) == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_b_1730_);
return v___x_1738_;
}
else
{
lean_object* v_head_1739_; lean_object* v_tail_1740_; lean_object* v_snd_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1861_; 
v_head_1739_ = lean_ctor_get(v_as_x27_1729_, 0);
v_tail_1740_ = lean_ctor_get(v_as_x27_1729_, 1);
v_snd_1741_ = lean_ctor_get(v_b_1730_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_b_1730_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v_b_1730_, 0);
lean_dec(v_unused_1862_);
v___x_1743_ = v_b_1730_;
v_isShared_1744_ = v_isSharedCheck_1861_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snd_1741_);
lean_dec(v_b_1730_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1861_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_options_1751_; lean_object* v_name_1752_; lean_object* v_run_x27_1753_; lean_object* v_inheritedTraceOptions_1754_; uint8_t v_hasTrace_1755_; lean_object* v___x_1756_; lean_object* v___y_1758_; 
v_options_1751_ = lean_ctor_get(v___y_1735_, 2);
v_name_1752_ = lean_ctor_get(v_head_1739_, 0);
v_run_x27_1753_ = lean_ctor_get(v_head_1739_, 1);
v_inheritedTraceOptions_1754_ = lean_ctor_get(v___y_1735_, 13);
v_hasTrace_1755_ = lean_ctor_get_uint8(v_options_1751_, sizeof(void*)*1);
v___x_1756_ = lean_box(0);
if (v_hasTrace_1755_ == 0)
{
lean_object* v___x_1784_; 
lean_inc_ref(v_run_x27_1753_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v_snd_1741_);
v___x_1784_ = lean_apply_8(v_run_x27_1753_, v_snd_1741_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, lean_box(0));
v___y_1758_ = v___x_1784_;
goto v___jp_1757_;
}
else
{
lean_object* v___f_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v_a_1793_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v_a_1808_; 
lean_inc(v_snd_1741_);
lean_inc(v_name_1752_);
v___f_1785_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1785_, 0, v_name_1752_);
lean_closure_set(v___f_1785_, 1, v_snd_1741_);
v___x_1786_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25));
v___x_1787_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__26));
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29);
v___x_1789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1754_, v_options_1751_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = l_Lean_trace_profiler;
v___x_1859_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(v_options_1751_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v___f_1785_);
lean_inc_ref(v_run_x27_1753_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v_snd_1741_);
v___x_1860_ = lean_apply_8(v_run_x27_1753_, v_snd_1741_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, lean_box(0));
v___y_1758_ = v___x_1860_;
goto v___jp_1757_;
}
else
{
goto v___jp_1817_;
}
}
else
{
goto v___jp_1817_;
}
v___jp_1790_:
{
lean_object* v___x_1794_; double v___x_1795_; double v___x_1796_; double v___x_1797_; double v___x_1798_; double v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1794_ = lean_io_mono_nanos_now();
v___x_1795_ = lean_float_of_nat(v___y_1792_);
v___x_1796_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__30);
v___x_1797_ = lean_float_div(v___x_1795_, v___x_1796_);
v___x_1798_ = lean_float_of_nat(v___x_1794_);
v___x_1799_ = lean_float_div(v___x_1798_, v___x_1796_);
v___x_1800_ = lean_box_float(v___x_1797_);
v___x_1801_ = lean_box_float(v___x_1799_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_a_1793_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v___x_1786_, v_hasTrace_1755_, v___x_1787_, v_options_1751_, v___x_1789_, v___y_1791_, v___f_1785_, v___x_1803_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
v___y_1758_ = v___x_1804_;
goto v___jp_1757_;
}
v___jp_1805_:
{
lean_object* v___x_1809_; double v___x_1810_; double v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1809_ = lean_io_get_num_heartbeats();
v___x_1810_ = lean_float_of_nat(v___y_1807_);
v___x_1811_ = lean_float_of_nat(v___x_1809_);
v___x_1812_ = lean_box_float(v___x_1810_);
v___x_1813_ = lean_box_float(v___x_1811_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_a_1808_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3(v___x_1786_, v_hasTrace_1755_, v___x_1787_, v_options_1751_, v___x_1789_, v___y_1806_, v___f_1785_, v___x_1815_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
v___y_1758_ = v___x_1816_;
goto v___jp_1757_;
}
v___jp_1817_:
{
lean_object* v___x_1818_; lean_object* v_a_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1818_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_1736_);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1818_);
v___x_1820_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1821_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__2(v_options_1751_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_1753_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v_snd_1741_);
v___x_1823_ = lean_apply_8(v_run_x27_1753_, v_snd_1741_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, lean_box(0));
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 1);
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
v___y_1791_ = v_a_1819_;
v___y_1792_ = v___x_1822_;
v_a_1793_ = v___x_1829_;
goto v___jp_1790_;
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_a_1832_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1823_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1823_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 0);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
v___y_1791_ = v_a_1819_;
v___y_1792_ = v___x_1822_;
v_a_1793_ = v___x_1837_;
goto v___jp_1790_;
}
}
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_1753_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v_snd_1741_);
v___x_1841_ = lean_apply_8(v_run_x27_1753_, v_snd_1741_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, lean_box(0));
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 1);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
v___y_1806_ = v_a_1819_;
v___y_1807_ = v___x_1840_;
v_a_1808_ = v___x_1847_;
goto v___jp_1805_;
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1841_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1841_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 0);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
v___y_1806_ = v_a_1819_;
v___y_1807_ = v___x_1840_;
v_a_1808_ = v___x_1855_;
goto v___jp_1805_;
}
}
}
}
}
}
v___jp_1745_:
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0));
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1746_);
v___x_1748_ = v___x_1743_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_snd_1741_);
v___x_1748_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
v___jp_1757_:
{
if (lean_obj_tag(v___y_1758_) == 0)
{
lean_object* v_a_1759_; 
v_a_1759_ = lean_ctor_get(v___y_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref(v___y_1758_);
if (lean_obj_tag(v_a_1759_) == 1)
{
lean_object* v_val_1760_; lean_object* v___x_1761_; 
lean_del_object(v___x_1743_);
lean_dec(v_snd_1741_);
v_val_1760_ = lean_ctor_get(v_a_1759_, 0);
lean_inc(v_val_1760_);
lean_dec_ref(v_a_1759_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1756_);
lean_ctor_set(v___x_1761_, 1, v_val_1760_);
v_as_x27_1729_ = v_tail_1740_;
v_b_1730_ = v___x_1761_;
goto _start;
}
else
{
lean_dec(v_a_1759_);
if (v_hasTrace_1755_ == 0)
{
goto v___jp_1745_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1763_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25));
v___x_1764_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29);
v___x_1765_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1754_, v_options_1751_, v___x_1764_);
if (v___x_1765_ == 0)
{
goto v___jp_1745_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2);
v___x_1767_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1763_, v___x_1766_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_dec_ref(v___x_1767_);
goto v___jp_1745_;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_del_object(v___x_1743_);
lean_dec(v_snd_1741_);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_del_object(v___x_1743_);
lean_dec(v_snd_1741_);
v_a_1776_ = lean_ctor_get(v___y_1758_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___y_1758_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___y_1758_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___y_1758_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg___boxed(lean_object* v_as_x27_1863_, lean_object* v_b_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_as_x27_1863_, v_b_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v_as_x27_1863_);
return v_res_1872_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__1));
v___x_1876_ = l_Lean_stringToMessageData(v___x_1875_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__4(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__3));
v___x_1879_ = l_Lean_stringToMessageData(v___x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(lean_object* v_passes_1880_, lean_object* v_goal_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__0));
v___x_1890_ = l_Lean_Core_checkSystem(v___x_1889_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1965_; 
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1890_, 0);
lean_dec(v_unused_1966_);
v___x_1892_ = v___x_1890_;
v_isShared_1893_ = v_isSharedCheck_1965_;
goto v_resetjp_1891_;
}
else
{
lean_dec(v___x_1890_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1965_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(0);
lean_inc(v_goal_1881_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v_goal_1881_);
v___x_1896_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_passes_1880_, v___x_1895_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1956_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1956_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1956_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_fst_1901_; lean_object* v_snd_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1955_; 
v_fst_1901_ = lean_ctor_get(v_a_1897_, 0);
v_snd_1902_ = lean_ctor_get(v_a_1897_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_a_1897_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1904_ = v_a_1897_;
v_isShared_1905_ = v_isSharedCheck_1955_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_snd_1902_);
lean_inc(v_fst_1901_);
lean_dec(v_a_1897_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1955_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
if (lean_obj_tag(v_fst_1901_) == 0)
{
uint8_t v___x_1911_; 
lean_del_object(v___x_1892_);
v___x_1911_ = l_Lean_instBEqMVarId_beq(v_goal_1881_, v_snd_1902_);
lean_dec(v_goal_1881_);
if (v___x_1911_ == 0)
{
lean_object* v_options_1912_; uint8_t v_hasTrace_1913_; 
lean_del_object(v___x_1899_);
v_options_1912_ = lean_ctor_get(v_a_1886_, 2);
v_hasTrace_1913_ = lean_ctor_get_uint8(v_options_1912_, sizeof(void*)*1);
if (v_hasTrace_1913_ == 0)
{
lean_del_object(v___x_1904_);
v_goal_1881_ = v_snd_1902_;
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_inheritedTraceOptions_1915_ = lean_ctor_get(v_a_1886_, 13);
v___x_1916_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25));
v___x_1917_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29);
v___x_1918_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1915_, v_options_1912_, v___x_1917_);
if (v___x_1918_ == 0)
{
lean_del_object(v___x_1904_);
v_goal_1881_ = v_snd_1902_;
goto _start;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1920_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__2);
lean_inc(v_snd_1902_);
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_snd_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 7);
lean_ctor_set(v___x_1904_, 1, v___x_1921_);
lean_ctor_set(v___x_1904_, 0, v___x_1920_);
v___x_1923_ = v___x_1904_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1916_, v___x_1923_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_dec_ref(v___x_1924_);
v_goal_1881_ = v_snd_1902_;
goto _start;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_snd_1902_);
v_a_1926_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1924_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1924_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_1935_; uint8_t v_hasTrace_1936_; 
lean_del_object(v___x_1904_);
v_options_1935_ = lean_ctor_get(v_a_1886_, 2);
v_hasTrace_1936_ = lean_ctor_get_uint8(v_options_1935_, sizeof(void*)*1);
if (v_hasTrace_1936_ == 0)
{
goto v___jp_1906_;
}
else
{
lean_object* v_inheritedTraceOptions_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v_inheritedTraceOptions_1937_ = lean_ctor_get(v_a_1886_, 13);
v___x_1938_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__25));
v___x_1939_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_run___closed__29);
v___x_1940_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1937_, v_options_1935_, v___x_1939_);
if (v___x_1940_ == 0)
{
goto v___jp_1906_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___closed__4);
v___x_1942_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1938_, v___x_1941_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_dec_ref(v___x_1942_);
goto v___jp_1906_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_snd_1902_);
lean_del_object(v___x_1899_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_1951_; lean_object* v___x_1953_; 
lean_del_object(v___x_1904_);
lean_dec(v_snd_1902_);
lean_del_object(v___x_1899_);
lean_dec(v_goal_1881_);
v_val_1951_ = lean_ctor_get(v_fst_1901_, 0);
lean_inc(v_val_1951_);
lean_dec_ref(v_fst_1901_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v_val_1951_);
v___x_1953_ = v___x_1892_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_val_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
v___jp_1906_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_snd_1902_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1907_);
v___x_1909_ = v___x_1899_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_del_object(v___x_1892_);
lean_dec(v_goal_1881_);
v_a_1957_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1896_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1896_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_goal_1881_);
v_a_1967_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1890_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1890_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_1975_, lean_object* v_goal_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline(v_passes_1975_, v_goal_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_passes_1975_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0(lean_object* v_cls_1985_, lean_object* v_msg_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_1985_, v_msg_1986_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0___boxed(lean_object* v_cls_1995_, lean_object* v_msg_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0(v_cls_1995_, v_msg_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6(lean_object* v_00_u03b1_2005_, lean_object* v_x_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_x_2006_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2015_, lean_object* v_x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__6(v_00_u03b1_2015_, v_x_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(lean_object* v_as_2025_, lean_object* v_as_x27_2026_, lean_object* v_b_2027_, lean_object* v_a_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_as_x27_2026_, v_b_2027_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4___boxed(lean_object* v_as_2037_, lean_object* v_as_x27_2038_, lean_object* v_b_2039_, lean_object* v_a_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__4(v_as_2037_, v_as_x27_2038_, v_b_2039_, v_a_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_as_x27_2038_);
lean_dec(v_as_2037_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5(lean_object* v_oldTraces_2049_, lean_object* v_data_2050_, lean_object* v_ref_2051_, lean_object* v_msg_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_2049_, v_data_2050_, v_ref_2051_, v_msg_2052_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5___boxed(lean_object* v_oldTraces_2061_, lean_object* v_data_2062_, lean_object* v_ref_2063_, lean_object* v_msg_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__3_spec__5(v_oldTraces_2061_, v_data_2062_, v_ref_2063_, v_msg_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
return v_res_2072_;
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
