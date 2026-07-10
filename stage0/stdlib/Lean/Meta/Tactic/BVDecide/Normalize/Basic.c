// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Attr public import Std.Tactic.BVDecide.Syntax
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getPropHyps___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " on\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultOption___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Fixpoint iteration solved the goal"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pipeline reached a fixpoint"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Rerunning pipeline on:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object* v_t_23_, lean_object* v_simpleEnum_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_23_, v_simpleEnum_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_simpleEnum_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_27_, v_simpleEnum_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object* v_t_31_, lean_object* v_enumWithDefault_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_31_, v_enumWithDefault_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_enumWithDefault_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_35_, v_enumWithDefault_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
lean_inc_ref(v_a_39_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v_a_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_42_);
lean_dec_ref(v_a_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
lean_inc_ref(v_a_45_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_a_45_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg(lean_object* v_fvar_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; lean_object* v_rewriteCache_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_66_ = lean_st_ref_get(v_a_64_);
v_rewriteCache_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_rewriteCache_67_);
lean_dec(v___x_66_);
v___x_68_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_69_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_70_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_68_, v___x_69_, v_rewriteCache_67_, v_fvar_63_);
lean_dec_ref(v_rewriteCache_67_);
v___x_71_ = lean_box(v___x_70_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___boxed(lean_object* v_fvar_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg(v_fvar_73_, v_a_74_);
lean_dec(v_a_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten(lean_object* v_fvar_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; lean_object* v_rewriteCache_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_85_ = lean_st_ref_get(v_a_79_);
v_rewriteCache_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_rewriteCache_86_);
lean_dec(v___x_85_);
v___x_87_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_88_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_89_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_87_, v___x_88_, v_rewriteCache_86_, v_fvar_77_);
lean_dec_ref(v_rewriteCache_86_);
v___x_90_ = lean_box(v___x_89_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___boxed(lean_object* v_fvar_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten(v_fvar_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg(lean_object* v_fvar_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; lean_object* v_acNfCache_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_104_ = lean_st_ref_get(v_a_102_);
v_acNfCache_105_ = lean_ctor_get(v___x_104_, 1);
lean_inc_ref(v_acNfCache_105_);
lean_dec(v___x_104_);
v___x_106_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_107_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_106_, v___x_107_, v_acNfCache_105_, v_fvar_101_);
lean_dec_ref(v_acNfCache_105_);
v___x_109_ = lean_box(v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg___boxed(lean_object* v_fvar_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg(v_fvar_111_, v_a_112_);
lean_dec(v_a_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf(lean_object* v_fvar_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; lean_object* v_acNfCache_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_123_ = lean_st_ref_get(v_a_117_);
v_acNfCache_124_ = lean_ctor_get(v___x_123_, 1);
lean_inc_ref(v_acNfCache_124_);
lean_dec(v___x_123_);
v___x_125_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_126_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_125_, v___x_126_, v_acNfCache_124_, v_fvar_115_);
lean_dec_ref(v_acNfCache_124_);
v___x_128_ = lean_box(v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___boxed(lean_object* v_fvar_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf(v_fvar_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg(lean_object* v_fvar_139_, lean_object* v_a_140_){
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
v___x_149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_150_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg___boxed(lean_object* v_fvar_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg(v_fvar_159_, v_a_160_);
lean_dec(v_a_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished(lean_object* v_fvar_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
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
v___x_178_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_179_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___boxed(lean_object* v_fvar_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished(v_fvar_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg(lean_object* v_fvar_197_, lean_object* v_a_198_){
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
v___x_207_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_208_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg___boxed(lean_object* v_fvar_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg(v_fvar_217_, v_a_218_);
lean_dec(v_a_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished(lean_object* v_fvar_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
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
v___x_236_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0));
v___x_237_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___boxed(lean_object* v_fvar_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished(v_fvar_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_255_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_260_);
lean_dec(v_a_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_286_, lean_object* v_a_287_){
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
v___x_293_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_294_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
v___x_302_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_304_, v_a_305_);
lean_dec(v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
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
v___x_320_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_321_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
v___x_329_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_340_, lean_object* v_a_341_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_358_, v_a_359_);
lean_dec(v_a_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_394_, lean_object* v_a_395_){
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
v___x_411_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_412_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_425_, v_a_426_);
lean_dec(v_a_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
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
v___x_451_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_452_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_474_, lean_object* v_a_475_){
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
v___x_491_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_492_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_505_, v_a_506_);
lean_dec(v_a_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
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
v___x_531_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_532_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_554_, lean_object* v_k_555_, lean_object* v_a_556_){
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
v___x_572_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_573_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_586_, lean_object* v_k_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_586_, v_k_587_, v_a_588_);
lean_dec(v_a_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_591_, lean_object* v_k_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
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
v___x_614_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_615_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_628_, lean_object* v_k_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_628_, v_k_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_638_, lean_object* v_a_639_){
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
v___x_655_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_656_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_669_, v_a_670_);
lean_dec(v_a_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
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
v___x_695_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_696_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_717_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_instMonadEIO(lean_box(0));
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_720_ = l_StateRefT_x27_instMonad___redArg(v___x_719_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_box(0);
v___x_727_ = lean_unsigned_to_nat(16u);
v___x_728_ = lean_mk_array(v___x_727_, v___x_726_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7);
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8);
v___x_733_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
lean_ctor_set(v___x_733_, 3, v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_cfg_734_, lean_object* v_goal_735_, lean_object* v_x_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_toApplicative_743_; lean_object* v_toFunctor_744_; lean_object* v_toSeq_745_; lean_object* v_toSeqLeft_746_; lean_object* v_toSeqRight_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_toApplicative_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_837_; 
v___x_742_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_743_ = lean_ctor_get(v___x_742_, 0);
v_toFunctor_744_ = lean_ctor_get(v_toApplicative_743_, 0);
v_toSeq_745_ = lean_ctor_get(v_toApplicative_743_, 2);
v_toSeqLeft_746_ = lean_ctor_get(v_toApplicative_743_, 3);
v_toSeqRight_747_ = lean_ctor_get(v_toApplicative_743_, 4);
v___f_748_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2));
v___f_749_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
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
v___f_770_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4));
v___f_771_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5));
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
v___x_798_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6));
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
lean_dec_ref_known(v___x_800_, 1);
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
v___x_812_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_cfg_839_, lean_object* v_goal_840_, lean_object* v_x_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_cfg_839_, v_goal_840_, v_x_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_848_, lean_object* v_cfg_849_, lean_object* v_goal_850_, lean_object* v_x_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; lean_object* v_toApplicative_858_; lean_object* v_toFunctor_859_; lean_object* v_toSeq_860_; lean_object* v_toSeqLeft_861_; lean_object* v_toSeqRight_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_toApplicative_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_952_; 
v___x_857_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_858_ = lean_ctor_get(v___x_857_, 0);
v_toFunctor_859_ = lean_ctor_get(v_toApplicative_858_, 0);
v_toSeq_860_ = lean_ctor_get(v_toApplicative_858_, 2);
v_toSeqLeft_861_ = lean_ctor_get(v_toApplicative_858_, 3);
v_toSeqRight_862_ = lean_ctor_get(v_toApplicative_858_, 4);
v___f_863_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2));
v___f_864_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
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
v___f_885_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4));
v___f_886_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5));
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
v___x_913_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6));
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
lean_dec_ref_known(v___x_915_, 1);
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
v___x_927_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_954_, lean_object* v_cfg_955_, lean_object* v_goal_956_, lean_object* v_x_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_954_, v_cfg_955_, v_goal_956_, v_x_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_963_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_970_, lean_object* v_goal_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_980_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_981_ = l_Lean_MessageData_ofName(v_name_970_);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_988_, lean_object* v_goal_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_988_, v_goal_989_, v_x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1002_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1));
v___x_1003_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___f_1005_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0));
v___x_1006_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1005_, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_1008_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1));
v___x_1009_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1008_, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___f_1011_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0));
v___x_1012_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1016_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1));
v___x_1017_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7));
v___x_1018_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1017_, v___x_1016_, v___x_1015_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___x_1022_; 
v___x_1019_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___f_1020_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0));
v___f_1021_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6));
v___x_1022_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1021_, v___f_1020_, v___x_1019_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1023_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_1024_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1));
v___x_1025_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7));
v___x_1026_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1025_, v___x_1024_, v___x_1023_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; 
v___x_1027_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___f_1028_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0));
v___f_1029_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6));
v___x_1030_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1029_, v___f_1028_, v___x_1027_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12(void){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12);
v___x_1033_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_1035_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14);
v___x_1037_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15);
v___x_1039_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16);
v___x_1041_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17);
v___x_1043_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___f_1046_; 
v___x_1044_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1));
v___x_1045_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1046_, 0, v___x_1045_);
lean_closure_set(v___f_1046_, 1, v___x_1044_);
return v___f_1046_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20(void){
_start:
{
lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; 
v___f_1047_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0));
v___f_1048_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19);
v___f_1049_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1049_, 0, v___f_1048_);
lean_closure_set(v___f_1049_, 1, v___f_1047_);
return v___f_1049_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27(void){
_start:
{
lean_object* v___x_1059_; double v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(1000000000u);
v___x_1060_ = lean_float_of_nat(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25));
v___x_1065_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29));
v___x_1066_ = l_Lean_Name_append(v___x_1065_, v___x_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_1067_, lean_object* v_goal_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; lean_object* v_toApplicative_1077_; lean_object* v_toFunctor_1078_; lean_object* v_toSeq_1079_; lean_object* v_toSeqLeft_1080_; lean_object* v_toSeqRight_1081_; lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_toApplicative_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1238_; 
v___x_1076_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v_toApplicative_1077_ = lean_ctor_get(v___x_1076_, 0);
v_toFunctor_1078_ = lean_ctor_get(v_toApplicative_1077_, 0);
v_toSeq_1079_ = lean_ctor_get(v_toApplicative_1077_, 2);
v_toSeqLeft_1080_ = lean_ctor_get(v_toApplicative_1077_, 3);
v_toSeqRight_1081_ = lean_ctor_get(v_toApplicative_1077_, 4);
v___f_1082_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2));
v___f_1083_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
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
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v___x_1092_, 1);
lean_dec(v_unused_1239_);
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1238_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_toApplicative_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1238_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_toFunctor_1097_; lean_object* v_toSeq_1098_; lean_object* v_toSeqLeft_1099_; lean_object* v_toSeqRight_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1236_; 
v_toFunctor_1097_ = lean_ctor_get(v_toApplicative_1093_, 0);
v_toSeq_1098_ = lean_ctor_get(v_toApplicative_1093_, 2);
v_toSeqLeft_1099_ = lean_ctor_get(v_toApplicative_1093_, 3);
v_toSeqRight_1100_ = lean_ctor_get(v_toApplicative_1093_, 4);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_toApplicative_1093_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v_toApplicative_1093_, 1);
lean_dec(v_unused_1237_);
v___x_1102_ = v_toApplicative_1093_;
v_isShared_1103_ = v_isSharedCheck_1236_;
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
v_isShared_1103_ = v_isSharedCheck_1236_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1113_; 
v___f_1104_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4));
v___f_1105_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5));
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
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___f_1104_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v___f_1111_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v___f_1110_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v___f_1109_);
v___x_1113_ = v_reuseFailAlloc_1235_;
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
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___f_1105_);
v___x_1115_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_toMonadRef_1120_; lean_object* v___x_1121_; lean_object* v_options_1122_; lean_object* v_name_1123_; lean_object* v_run_x27_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1233_; 
v___x_1116_ = l_StateRefT_x27_instMonad___redArg(v___x_1115_);
v___x_1117_ = l_ReaderT_instMonad___redArg(v___x_1116_);
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_1119_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_toMonadRef_1120_ = lean_ctor_get(v___x_1119_, 0);
v___x_1121_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18);
v_options_1122_ = lean_ctor_get(v_a_1073_, 2);
v_name_1123_ = lean_ctor_get(v_pass_1067_, 0);
v_run_x27_1124_ = lean_ctor_get(v_pass_1067_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_pass_1067_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1126_ = v_pass_1067_;
v_isShared_1127_ = v_isSharedCheck_1233_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_run_x27_1124_);
lean_inc(v_name_1123_);
lean_dec(v_pass_1067_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1233_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_inheritedTraceOptions_1128_; uint8_t v_hasTrace_1129_; uint8_t v___x_1130_; 
v_inheritedTraceOptions_1128_ = lean_ctor_get(v_a_1073_, 13);
v_hasTrace_1129_ = lean_ctor_get_uint8(v_options_1122_, sizeof(void*)*1);
v___x_1130_ = lean_bool_not(v_hasTrace_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; lean_object* v_a_1141_; lean_object* v___y_1157_; lean_object* v___y_1158_; uint8_t v___y_1159_; lean_object* v_a_1160_; uint8_t v___y_1171_; uint8_t v_a_1224_; 
lean_inc(v_goal_1068_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1131_, 0, v_name_1123_);
lean_closure_set(v___f_1131_, 1, v_goal_1068_);
v___f_1132_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20);
v___f_1133_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21));
v___x_1134_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25));
v___x_1135_ = 1;
v___x_1136_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26));
if (v_hasTrace_1129_ == 0)
{
v_a_1224_ = v_hasTrace_1129_;
goto v___jp_1223_;
}
else
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30);
v___x_1231_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1128_, v_options_1122_, v___x_1230_);
if (v___x_1231_ == 0)
{
v_a_1224_ = v___x_1231_;
goto v___jp_1223_;
}
else
{
v___y_1171_ = v___x_1231_;
goto v___jp_1170_;
}
}
v___jp_1137_:
{
lean_object* v___x_1142_; double v___x_1143_; double v___x_1144_; double v___x_1145_; double v___x_1146_; double v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1142_ = lean_io_mono_nanos_now();
v___x_1143_ = lean_float_of_nat(v___y_1138_);
v___x_1144_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27);
v___x_1145_ = lean_float_div(v___x_1143_, v___x_1144_);
v___x_1146_ = lean_float_of_nat(v___x_1142_);
v___x_1147_ = lean_float_div(v___x_1146_, v___x_1144_);
v___x_1148_ = lean_box_float(v___x_1145_);
v___x_1149_ = lean_box_float(v___x_1147_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v___x_1149_);
lean_ctor_set(v___x_1126_, 0, v___x_1148_);
v___x_1151_ = v___x_1126_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_9448__overap_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_a_1141_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
lean_inc_ref(v_toMonadRef_1120_);
v___x_9448__overap_1153_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_1117_, v___x_1118_, v_toMonadRef_1120_, v___f_1132_, lean_box(0), v___x_1121_, v___f_1133_, v___x_1134_, v___x_1135_, v___x_1136_, v_options_1122_, v___y_1140_, v___y_1139_, v___f_1131_, v___x_1152_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1154_ = lean_apply_7(v___x_9448__overap_1153_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
return v___x_1154_;
}
}
v___jp_1156_:
{
lean_object* v___x_1161_; double v___x_1162_; double v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_9452__overap_1168_; lean_object* v___x_1169_; 
v___x_1161_ = lean_io_get_num_heartbeats();
v___x_1162_ = lean_float_of_nat(v___y_1158_);
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
v___x_9452__overap_1168_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_1117_, v___x_1118_, v_toMonadRef_1120_, v___f_1132_, lean_box(0), v___x_1121_, v___f_1133_, v___x_1134_, v___x_1135_, v___x_1136_, v_options_1122_, v___y_1159_, v___y_1157_, v___f_1131_, v___x_1167_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1169_ = lean_apply_7(v___x_9452__overap_1168_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
return v___x_1169_;
}
v___jp_1170_:
{
lean_object* v___x_9245__overap_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v___x_1117_);
v___x_9245__overap_1172_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_1117_, v___x_1118_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1173_ = lean_apply_7(v___x_9245__overap_1172_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1175_ = l_Lean_KVMap_instValueBool;
v___x_1176_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1177_ = l_Lean_Option_get___redArg(v___x_1175_, v_options_1122_, v___x_1176_);
v___x_1178_ = lean_unbox(v___x_1177_);
lean_dec(v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_io_mono_nanos_now();
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1180_ = lean_apply_8(v_run_x27_1124_, v_goal_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 1);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
v___y_1138_ = v___x_1179_;
v___y_1139_ = v_a_1174_;
v___y_1140_ = v___y_1171_;
v_a_1141_ = v___x_1186_;
goto v___jp_1137_;
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
v_a_1189_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1180_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1180_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set_tag(v___x_1191_, 0);
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
v___y_1138_ = v___x_1179_;
v___y_1139_ = v_a_1174_;
v___y_1140_ = v___y_1171_;
v_a_1141_ = v___x_1194_;
goto v___jp_1137_;
}
}
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_del_object(v___x_1126_);
v___x_1197_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1198_ = lean_apply_8(v_run_x27_1124_, v_goal_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set_tag(v___x_1201_, 1);
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
v___y_1157_ = v_a_1174_;
v___y_1158_ = v___x_1197_;
v___y_1159_ = v___y_1171_;
v_a_1160_ = v___x_1204_;
goto v___jp_1156_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1198_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1198_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 0);
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
v___y_1157_ = v_a_1174_;
v___y_1158_ = v___x_1197_;
v___y_1159_ = v___y_1171_;
v_a_1160_ = v___x_1212_;
goto v___jp_1156_;
}
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec_ref(v___f_1131_);
lean_del_object(v___x_1126_);
lean_dec_ref(v_run_x27_1124_);
lean_dec_ref(v___x_1117_);
lean_dec(v_goal_1068_);
v_a_1215_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1173_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1173_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
v___jp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1225_ = l_Lean_KVMap_instValueBool;
v___x_1226_ = l_Lean_trace_profiler;
v___x_1227_ = l_Lean_Option_get___redArg(v___x_1225_, v_options_1122_, v___x_1226_);
v___x_1228_ = lean_unbox(v___x_1227_);
lean_dec(v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref(v___f_1131_);
lean_del_object(v___x_1126_);
lean_dec_ref(v___x_1117_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1229_ = lean_apply_8(v_run_x27_1124_, v_goal_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
return v___x_1229_;
}
else
{
v___y_1171_ = v_a_1224_;
goto v___jp_1170_;
}
}
}
else
{
lean_object* v___x_1232_; 
lean_del_object(v___x_1126_);
lean_dec(v_name_1123_);
lean_dec_ref(v___x_1117_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
v___x_1232_ = lean_apply_8(v_run_x27_1124_, v_goal_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, lean_box(0));
return v___x_1232_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_1240_, lean_object* v_goal_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_1240_, v_goal_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1249_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_unsigned_to_nat(32u);
v___x_1251_ = lean_mk_empty_array_with_capacity(v___x_1250_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1253_ = ((size_t)5ULL);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_unsigned_to_nat(32u);
v___x_1256_ = lean_mk_empty_array_with_capacity(v___x_1255_);
v___x_1257_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0);
v___x_1258_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1256_);
lean_ctor_set(v___x_1258_, 2, v___x_1254_);
lean_ctor_set(v___x_1258_, 3, v___x_1254_);
lean_ctor_set_usize(v___x_1258_, 4, v___x_1253_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; lean_object* v_traceState_1262_; lean_object* v_traces_1263_; lean_object* v___x_1264_; lean_object* v_traceState_1265_; lean_object* v_env_1266_; lean_object* v_nextMacroScope_1267_; lean_object* v_ngen_1268_; lean_object* v_auxDeclNGen_1269_; lean_object* v_cache_1270_; lean_object* v_messages_1271_; lean_object* v_infoState_1272_; lean_object* v_snapshotTasks_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1292_; 
v___x_1261_ = lean_st_ref_get(v___y_1259_);
v_traceState_1262_ = lean_ctor_get(v___x_1261_, 4);
lean_inc_ref(v_traceState_1262_);
lean_dec(v___x_1261_);
v_traces_1263_ = lean_ctor_get(v_traceState_1262_, 0);
lean_inc_ref(v_traces_1263_);
lean_dec_ref(v_traceState_1262_);
v___x_1264_ = lean_st_ref_take(v___y_1259_);
v_traceState_1265_ = lean_ctor_get(v___x_1264_, 4);
v_env_1266_ = lean_ctor_get(v___x_1264_, 0);
v_nextMacroScope_1267_ = lean_ctor_get(v___x_1264_, 1);
v_ngen_1268_ = lean_ctor_get(v___x_1264_, 2);
v_auxDeclNGen_1269_ = lean_ctor_get(v___x_1264_, 3);
v_cache_1270_ = lean_ctor_get(v___x_1264_, 5);
v_messages_1271_ = lean_ctor_get(v___x_1264_, 6);
v_infoState_1272_ = lean_ctor_get(v___x_1264_, 7);
v_snapshotTasks_1273_ = lean_ctor_get(v___x_1264_, 8);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1275_ = v___x_1264_;
v_isShared_1276_ = v_isSharedCheck_1292_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_snapshotTasks_1273_);
lean_inc(v_infoState_1272_);
lean_inc(v_messages_1271_);
lean_inc(v_cache_1270_);
lean_inc(v_traceState_1265_);
lean_inc(v_auxDeclNGen_1269_);
lean_inc(v_ngen_1268_);
lean_inc(v_nextMacroScope_1267_);
lean_inc(v_env_1266_);
lean_dec(v___x_1264_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1292_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
uint64_t v_tid_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1290_; 
v_tid_1277_ = lean_ctor_get_uint64(v_traceState_1265_, sizeof(void*)*1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_traceState_1265_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v_traceState_1265_, 0);
lean_dec(v_unused_1291_);
v___x_1279_ = v_traceState_1265_;
v_isShared_1280_ = v_isSharedCheck_1290_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v_traceState_1265_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1290_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1281_);
lean_ctor_set_uint64(v_reuseFailAlloc_1289_, sizeof(void*)*1, v_tid_1277_);
v___x_1283_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 4, v___x_1283_);
v___x_1285_ = v___x_1275_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_env_1266_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_nextMacroScope_1267_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_ngen_1268_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_auxDeclNGen_1269_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1288_, 5, v_cache_1270_);
lean_ctor_set(v_reuseFailAlloc_1288_, 6, v_messages_1271_);
lean_ctor_set(v_reuseFailAlloc_1288_, 7, v_infoState_1272_);
lean_ctor_set(v_reuseFailAlloc_1288_, 8, v_snapshotTasks_1273_);
v___x_1285_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_st_ref_set(v___y_1259_, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_traces_1263_);
return v___x_1287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_1293_);
lean_dec(v___y_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1(lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___boxed(lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1(v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1311_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(lean_object* v_opts_1312_, lean_object* v_opt_1313_){
_start:
{
lean_object* v_name_1314_; lean_object* v_defValue_1315_; lean_object* v_map_1316_; lean_object* v___x_1317_; 
v_name_1314_ = lean_ctor_get(v_opt_1313_, 0);
v_defValue_1315_ = lean_ctor_get(v_opt_1313_, 1);
v_map_1316_ = lean_ctor_get(v_opts_1312_, 0);
v___x_1317_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1316_, v_name_1314_);
if (lean_obj_tag(v___x_1317_) == 0)
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_unbox(v_defValue_1315_);
return v___x_1318_;
}
else
{
lean_object* v_val_1319_; 
v_val_1319_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v___x_1317_, 1);
if (lean_obj_tag(v_val_1319_) == 1)
{
uint8_t v_v_1320_; 
v_v_1320_ = lean_ctor_get_uint8(v_val_1319_, 0);
lean_dec_ref_known(v_val_1319_, 0);
return v_v_1320_;
}
else
{
uint8_t v___x_1321_; 
lean_dec(v_val_1319_);
v___x_1321_ = lean_unbox(v_defValue_1315_);
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2___boxed(lean_object* v_opts_1322_, lean_object* v_opt_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_opts_1322_, v_opt_1323_);
lean_dec_ref(v_opt_1323_);
lean_dec_ref(v_opts_1322_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(lean_object* v_name_1326_, lean_object* v_snd_1327_, lean_object* v_x_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1336_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_1337_ = l_Lean_MessageData_ofName(v_name_1326_);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_snd_1327_);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed(lean_object* v_name_1344_, lean_object* v_snd_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(v_name_1344_, v_snd_1345_, v_x_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v_x_1346_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(lean_object* v_msgData_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v_env_1362_; lean_object* v___x_1363_; lean_object* v_mctx_1364_; lean_object* v_lctx_1365_; lean_object* v_options_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1361_ = lean_st_ref_get(v___y_1359_);
v_env_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_ref(v_env_1362_);
lean_dec(v___x_1361_);
v___x_1363_ = lean_st_ref_get(v___y_1357_);
v_mctx_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc_ref(v_mctx_1364_);
lean_dec(v___x_1363_);
v_lctx_1365_ = lean_ctor_get(v___y_1356_, 2);
v_options_1366_ = lean_ctor_get(v___y_1358_, 2);
lean_inc_ref(v_options_1366_);
lean_inc_ref(v_lctx_1365_);
v___x_1367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1367_, 0, v_env_1362_);
lean_ctor_set(v___x_1367_, 1, v_mctx_1364_);
lean_ctor_set(v___x_1367_, 2, v_lctx_1365_);
lean_ctor_set(v___x_1367_, 3, v_options_1366_);
v___x_1368_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v_msgData_1355_);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0___boxed(lean_object* v_msgData_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msgData_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4_spec__5(size_t v_sz_1377_, size_t v_i_1378_, lean_object* v_bs_1379_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_usize_dec_lt(v_i_1378_, v_sz_1377_);
if (v___x_1380_ == 0)
{
return v_bs_1379_;
}
else
{
lean_object* v_v_1381_; lean_object* v_msg_1382_; lean_object* v___x_1383_; lean_object* v_bs_x27_1384_; size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v_v_1381_ = lean_array_uget_borrowed(v_bs_1379_, v_i_1378_);
v_msg_1382_ = lean_ctor_get(v_v_1381_, 1);
lean_inc_ref(v_msg_1382_);
v___x_1383_ = lean_unsigned_to_nat(0u);
v_bs_x27_1384_ = lean_array_uset(v_bs_1379_, v_i_1378_, v___x_1383_);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_add(v_i_1378_, v___x_1385_);
v___x_1387_ = lean_array_uset(v_bs_x27_1384_, v_i_1378_, v_msg_1382_);
v_i_1378_ = v___x_1386_;
v_bs_1379_ = v___x_1387_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_1389_, lean_object* v_i_1390_, lean_object* v_bs_1391_){
_start:
{
size_t v_sz_boxed_1392_; size_t v_i_boxed_1393_; lean_object* v_res_1394_; 
v_sz_boxed_1392_ = lean_unbox_usize(v_sz_1389_);
lean_dec(v_sz_1389_);
v_i_boxed_1393_ = lean_unbox_usize(v_i_1390_);
lean_dec(v_i_1390_);
v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4_spec__5(v_sz_boxed_1392_, v_i_boxed_1393_, v_bs_1391_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___redArg(lean_object* v_oldTraces_1395_, lean_object* v_data_1396_, lean_object* v_ref_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_fileName_1404_; lean_object* v_fileMap_1405_; lean_object* v_options_1406_; lean_object* v_currRecDepth_1407_; lean_object* v_maxRecDepth_1408_; lean_object* v_ref_1409_; lean_object* v_currNamespace_1410_; lean_object* v_openDecls_1411_; lean_object* v_initHeartbeats_1412_; lean_object* v_maxHeartbeats_1413_; lean_object* v_quotContext_1414_; lean_object* v_currMacroScope_1415_; uint8_t v_diag_1416_; lean_object* v_cancelTk_x3f_1417_; uint8_t v_suppressElabErrors_1418_; lean_object* v_inheritedTraceOptions_1419_; lean_object* v___x_1420_; lean_object* v_traceState_1421_; lean_object* v_traces_1422_; lean_object* v_ref_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; size_t v_sz_1426_; size_t v___x_1427_; lean_object* v___x_1428_; lean_object* v_msg_1429_; lean_object* v___x_1430_; lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1468_; 
v_fileName_1404_ = lean_ctor_get(v___y_1401_, 0);
v_fileMap_1405_ = lean_ctor_get(v___y_1401_, 1);
v_options_1406_ = lean_ctor_get(v___y_1401_, 2);
v_currRecDepth_1407_ = lean_ctor_get(v___y_1401_, 3);
v_maxRecDepth_1408_ = lean_ctor_get(v___y_1401_, 4);
v_ref_1409_ = lean_ctor_get(v___y_1401_, 5);
v_currNamespace_1410_ = lean_ctor_get(v___y_1401_, 6);
v_openDecls_1411_ = lean_ctor_get(v___y_1401_, 7);
v_initHeartbeats_1412_ = lean_ctor_get(v___y_1401_, 8);
v_maxHeartbeats_1413_ = lean_ctor_get(v___y_1401_, 9);
v_quotContext_1414_ = lean_ctor_get(v___y_1401_, 10);
v_currMacroScope_1415_ = lean_ctor_get(v___y_1401_, 11);
v_diag_1416_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*14);
v_cancelTk_x3f_1417_ = lean_ctor_get(v___y_1401_, 12);
v_suppressElabErrors_1418_ = lean_ctor_get_uint8(v___y_1401_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1419_ = lean_ctor_get(v___y_1401_, 13);
v___x_1420_ = lean_st_ref_get(v___y_1402_);
v_traceState_1421_ = lean_ctor_get(v___x_1420_, 4);
lean_inc_ref(v_traceState_1421_);
lean_dec(v___x_1420_);
v_traces_1422_ = lean_ctor_get(v_traceState_1421_, 0);
lean_inc_ref(v_traces_1422_);
lean_dec_ref(v_traceState_1421_);
v_ref_1423_ = l_Lean_replaceRef(v_ref_1397_, v_ref_1409_);
lean_inc_ref(v_inheritedTraceOptions_1419_);
lean_inc(v_cancelTk_x3f_1417_);
lean_inc(v_currMacroScope_1415_);
lean_inc(v_quotContext_1414_);
lean_inc(v_maxHeartbeats_1413_);
lean_inc(v_initHeartbeats_1412_);
lean_inc(v_openDecls_1411_);
lean_inc(v_currNamespace_1410_);
lean_inc(v_maxRecDepth_1408_);
lean_inc(v_currRecDepth_1407_);
lean_inc_ref(v_options_1406_);
lean_inc_ref(v_fileMap_1405_);
lean_inc_ref(v_fileName_1404_);
v___x_1424_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1424_, 0, v_fileName_1404_);
lean_ctor_set(v___x_1424_, 1, v_fileMap_1405_);
lean_ctor_set(v___x_1424_, 2, v_options_1406_);
lean_ctor_set(v___x_1424_, 3, v_currRecDepth_1407_);
lean_ctor_set(v___x_1424_, 4, v_maxRecDepth_1408_);
lean_ctor_set(v___x_1424_, 5, v_ref_1423_);
lean_ctor_set(v___x_1424_, 6, v_currNamespace_1410_);
lean_ctor_set(v___x_1424_, 7, v_openDecls_1411_);
lean_ctor_set(v___x_1424_, 8, v_initHeartbeats_1412_);
lean_ctor_set(v___x_1424_, 9, v_maxHeartbeats_1413_);
lean_ctor_set(v___x_1424_, 10, v_quotContext_1414_);
lean_ctor_set(v___x_1424_, 11, v_currMacroScope_1415_);
lean_ctor_set(v___x_1424_, 12, v_cancelTk_x3f_1417_);
lean_ctor_set(v___x_1424_, 13, v_inheritedTraceOptions_1419_);
lean_ctor_set_uint8(v___x_1424_, sizeof(void*)*14, v_diag_1416_);
lean_ctor_set_uint8(v___x_1424_, sizeof(void*)*14 + 1, v_suppressElabErrors_1418_);
v___x_1425_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1422_);
lean_dec_ref(v_traces_1422_);
v_sz_1426_ = lean_array_size(v___x_1425_);
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4_spec__5(v_sz_1426_, v___x_1427_, v___x_1425_);
v_msg_1429_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1429_, 0, v_data_1396_);
lean_ctor_set(v_msg_1429_, 1, v_msg_1398_);
lean_ctor_set(v_msg_1429_, 2, v___x_1428_);
v___x_1430_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msg_1429_, v___y_1399_, v___y_1400_, v___x_1424_, v___y_1402_);
lean_dec_ref_known(v___x_1424_, 14);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1468_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1468_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v_traceState_1436_; lean_object* v_env_1437_; lean_object* v_nextMacroScope_1438_; lean_object* v_ngen_1439_; lean_object* v_auxDeclNGen_1440_; lean_object* v_cache_1441_; lean_object* v_messages_1442_; lean_object* v_infoState_1443_; lean_object* v_snapshotTasks_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1467_; 
v___x_1435_ = lean_st_ref_take(v___y_1402_);
v_traceState_1436_ = lean_ctor_get(v___x_1435_, 4);
v_env_1437_ = lean_ctor_get(v___x_1435_, 0);
v_nextMacroScope_1438_ = lean_ctor_get(v___x_1435_, 1);
v_ngen_1439_ = lean_ctor_get(v___x_1435_, 2);
v_auxDeclNGen_1440_ = lean_ctor_get(v___x_1435_, 3);
v_cache_1441_ = lean_ctor_get(v___x_1435_, 5);
v_messages_1442_ = lean_ctor_get(v___x_1435_, 6);
v_infoState_1443_ = lean_ctor_get(v___x_1435_, 7);
v_snapshotTasks_1444_ = lean_ctor_get(v___x_1435_, 8);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1446_ = v___x_1435_;
v_isShared_1447_ = v_isSharedCheck_1467_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_snapshotTasks_1444_);
lean_inc(v_infoState_1443_);
lean_inc(v_messages_1442_);
lean_inc(v_cache_1441_);
lean_inc(v_traceState_1436_);
lean_inc(v_auxDeclNGen_1440_);
lean_inc(v_ngen_1439_);
lean_inc(v_nextMacroScope_1438_);
lean_inc(v_env_1437_);
lean_dec(v___x_1435_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1467_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
uint64_t v_tid_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1465_; 
v_tid_1448_ = lean_ctor_get_uint64(v_traceState_1436_, sizeof(void*)*1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_traceState_1436_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_traceState_1436_, 0);
lean_dec(v_unused_1466_);
v___x_1450_ = v_traceState_1436_;
v_isShared_1451_ = v_isSharedCheck_1465_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v_traceState_1436_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1465_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_ref_1397_);
lean_ctor_set(v___x_1452_, 1, v_a_1431_);
v___x_1453_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1395_, v___x_1452_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1453_);
v___x_1455_ = v___x_1450_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1453_);
lean_ctor_set_uint64(v_reuseFailAlloc_1464_, sizeof(void*)*1, v_tid_1448_);
v___x_1455_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 4, v___x_1455_);
v___x_1457_ = v___x_1446_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_env_1437_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_nextMacroScope_1438_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_ngen_1439_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_auxDeclNGen_1440_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1463_, 5, v_cache_1441_);
lean_ctor_set(v_reuseFailAlloc_1463_, 6, v_messages_1442_);
lean_ctor_set(v_reuseFailAlloc_1463_, 7, v_infoState_1443_);
lean_ctor_set(v_reuseFailAlloc_1463_, 8, v_snapshotTasks_1444_);
v___x_1457_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_st_ref_set(v___y_1402_, v___x_1457_);
v___x_1459_ = lean_box(0);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1459_);
v___x_1461_ = v___x_1433_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_1469_, lean_object* v_data_1470_, lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___redArg(v_oldTraces_1469_, v_data_1470_, v_ref_1471_, v_msg_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1478_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6(lean_object* v_e_1479_){
_start:
{
if (lean_obj_tag(v_e_1479_) == 0)
{
uint8_t v___x_1480_; 
v___x_1480_ = 2;
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; 
v_a_1481_ = lean_ctor_get(v_e_1479_, 0);
if (lean_obj_tag(v_a_1481_) == 0)
{
uint8_t v___x_1482_; 
v___x_1482_ = 1;
return v___x_1482_;
}
else
{
uint8_t v___x_1483_; 
v___x_1483_ = 0;
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___boxed(lean_object* v_e_1484_){
_start:
{
uint8_t v_res_1485_; lean_object* v_r_1486_; 
v_res_1485_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6(v_e_1484_);
lean_dec_ref(v_e_1484_);
v_r_1486_ = lean_box(v_res_1485_);
return v_r_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(lean_object* v_opts_1487_, lean_object* v_opt_1488_){
_start:
{
lean_object* v_name_1489_; lean_object* v_defValue_1490_; lean_object* v_map_1491_; lean_object* v___x_1492_; 
v_name_1489_ = lean_ctor_get(v_opt_1488_, 0);
v_defValue_1490_ = lean_ctor_get(v_opt_1488_, 1);
v_map_1491_ = lean_ctor_get(v_opts_1487_, 0);
v___x_1492_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1491_, v_name_1489_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_inc(v_defValue_1490_);
return v_defValue_1490_;
}
else
{
lean_object* v_val_1493_; 
v_val_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_val_1493_);
lean_dec_ref_known(v___x_1492_, 1);
if (lean_obj_tag(v_val_1493_) == 3)
{
lean_object* v_v_1494_; 
v_v_1494_ = lean_ctor_get(v_val_1493_, 0);
lean_inc(v_v_1494_);
lean_dec_ref_known(v_val_1493_, 1);
return v_v_1494_;
}
else
{
lean_dec(v_val_1493_);
lean_inc(v_defValue_1490_);
return v_defValue_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7___boxed(lean_object* v_opts_1495_, lean_object* v_opt_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_1495_, v_opt_1496_);
lean_dec_ref(v_opt_1496_);
lean_dec_ref(v_opts_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(lean_object* v_x_1498_){
_start:
{
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v_x_1498_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_x_1498_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v_x_1498_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v_x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 1);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_a_1508_ = lean_ctor_get(v_x_1498_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_x_1498_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v_x_1498_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v_x_1498_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 0);
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg___boxed(lean_object* v_x_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_x_1516_);
return v_res_1518_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1519_; double v___x_1520_; 
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = lean_float_of_nat(v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1));
v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
return v___x_1523_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1524_; double v___x_1525_; 
v___x_1524_ = lean_unsigned_to_nat(1000u);
v___x_1525_ = lean_float_of_nat(v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(lean_object* v_cls_1526_, uint8_t v_collapsed_1527_, lean_object* v_tag_1528_, lean_object* v_opts_1529_, uint8_t v_clsEnabled_1530_, lean_object* v_oldTraces_1531_, lean_object* v_msg_1532_, lean_object* v_resStartStop_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_fst_1541_; lean_object* v_snd_1542_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v_data_1546_; lean_object* v_fst_1557_; lean_object* v_snd_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; lean_object* v___y_1562_; lean_object* v_a_1563_; uint8_t v___y_1578_; double v___y_1609_; 
v_fst_1541_ = lean_ctor_get(v_resStartStop_1533_, 0);
lean_inc(v_fst_1541_);
v_snd_1542_ = lean_ctor_get(v_resStartStop_1533_, 1);
lean_inc(v_snd_1542_);
lean_dec_ref(v_resStartStop_1533_);
v_fst_1557_ = lean_ctor_get(v_snd_1542_, 0);
lean_inc(v_fst_1557_);
v_snd_1558_ = lean_ctor_get(v_snd_1542_, 1);
lean_inc(v_snd_1558_);
lean_dec(v_snd_1542_);
v___x_1559_ = l_Lean_trace_profiler;
v___x_1560_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_opts_1529_, v___x_1559_);
if (v___x_1560_ == 0)
{
v___y_1578_ = v___x_1560_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1615_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_opts_1529_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; double v___x_1618_; double v___x_1619_; double v___x_1620_; 
v___x_1616_ = l_Lean_trace_profiler_threshold;
v___x_1617_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_1529_, v___x_1616_);
v___x_1618_ = lean_float_of_nat(v___x_1617_);
v___x_1619_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3);
v___x_1620_ = lean_float_div(v___x_1618_, v___x_1619_);
v___y_1609_ = v___x_1620_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; double v___x_1623_; 
v___x_1621_ = l_Lean_trace_profiler_threshold;
v___x_1622_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_1529_, v___x_1621_);
v___x_1623_ = lean_float_of_nat(v___x_1622_);
v___y_1609_ = v___x_1623_;
goto v___jp_1608_;
}
}
v___jp_1543_:
{
lean_object* v___x_1547_; 
lean_inc(v___y_1545_);
v___x_1547_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___redArg(v_oldTraces_1531_, v_data_1546_, v___y_1545_, v___y_1544_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
lean_dec_ref_known(v___x_1547_, 1);
v___x_1548_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_fst_1541_);
return v___x_1548_;
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_fst_1541_);
v_a_1549_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1547_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
v___jp_1561_:
{
uint8_t v_result_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; double v___x_1567_; lean_object* v_data_1568_; 
v_result_1564_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6(v_fst_1541_);
v___x_1565_ = lean_box(v_result_1564_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
v___x_1567_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0);
lean_inc_ref(v_tag_1528_);
lean_inc_ref(v___x_1566_);
lean_inc(v_cls_1526_);
v_data_1568_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1568_, 0, v_cls_1526_);
lean_ctor_set(v_data_1568_, 1, v___x_1566_);
lean_ctor_set(v_data_1568_, 2, v_tag_1528_);
lean_ctor_set_float(v_data_1568_, sizeof(void*)*3, v___x_1567_);
lean_ctor_set_float(v_data_1568_, sizeof(void*)*3 + 8, v___x_1567_);
lean_ctor_set_uint8(v_data_1568_, sizeof(void*)*3 + 16, v_collapsed_1527_);
if (v___x_1560_ == 0)
{
lean_dec_ref_known(v___x_1566_, 1);
lean_dec(v_snd_1558_);
lean_dec(v_fst_1557_);
lean_dec_ref(v_tag_1528_);
lean_dec(v_cls_1526_);
v___y_1544_ = v_a_1563_;
v___y_1545_ = v___y_1562_;
v_data_1546_ = v_data_1568_;
goto v___jp_1543_;
}
else
{
lean_object* v_data_1569_; double v___x_1570_; double v___x_1571_; 
lean_dec_ref_known(v_data_1568_, 3);
v_data_1569_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1569_, 0, v_cls_1526_);
lean_ctor_set(v_data_1569_, 1, v___x_1566_);
lean_ctor_set(v_data_1569_, 2, v_tag_1528_);
v___x_1570_ = lean_unbox_float(v_fst_1557_);
lean_dec(v_fst_1557_);
lean_ctor_set_float(v_data_1569_, sizeof(void*)*3, v___x_1570_);
v___x_1571_ = lean_unbox_float(v_snd_1558_);
lean_dec(v_snd_1558_);
lean_ctor_set_float(v_data_1569_, sizeof(void*)*3 + 8, v___x_1571_);
lean_ctor_set_uint8(v_data_1569_, sizeof(void*)*3 + 16, v_collapsed_1527_);
v___y_1544_ = v_a_1563_;
v___y_1545_ = v___y_1562_;
v_data_1546_ = v_data_1569_;
goto v___jp_1543_;
}
}
v___jp_1572_:
{
lean_object* v_ref_1573_; lean_object* v___x_1574_; 
v_ref_1573_ = lean_ctor_get(v___y_1538_, 5);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v_fst_1541_);
v___x_1574_ = lean_apply_8(v_msg_1532_, v_fst_1541_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, lean_box(0));
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v___y_1562_ = v_ref_1573_;
v_a_1563_ = v_a_1575_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1576_; 
lean_dec_ref_known(v___x_1574_, 1);
v___x_1576_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2);
v___y_1562_ = v_ref_1573_;
v_a_1563_ = v___x_1576_;
goto v___jp_1561_;
}
}
v___jp_1577_:
{
if (v_clsEnabled_1530_ == 0)
{
if (v___y_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v_traceState_1580_; lean_object* v_env_1581_; lean_object* v_nextMacroScope_1582_; lean_object* v_ngen_1583_; lean_object* v_auxDeclNGen_1584_; lean_object* v_cache_1585_; lean_object* v_messages_1586_; lean_object* v_infoState_1587_; lean_object* v_snapshotTasks_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_snd_1558_);
lean_dec(v_fst_1557_);
lean_dec_ref(v_msg_1532_);
lean_dec_ref(v_tag_1528_);
lean_dec(v_cls_1526_);
v___x_1579_ = lean_st_ref_take(v___y_1539_);
v_traceState_1580_ = lean_ctor_get(v___x_1579_, 4);
v_env_1581_ = lean_ctor_get(v___x_1579_, 0);
v_nextMacroScope_1582_ = lean_ctor_get(v___x_1579_, 1);
v_ngen_1583_ = lean_ctor_get(v___x_1579_, 2);
v_auxDeclNGen_1584_ = lean_ctor_get(v___x_1579_, 3);
v_cache_1585_ = lean_ctor_get(v___x_1579_, 5);
v_messages_1586_ = lean_ctor_get(v___x_1579_, 6);
v_infoState_1587_ = lean_ctor_get(v___x_1579_, 7);
v_snapshotTasks_1588_ = lean_ctor_get(v___x_1579_, 8);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1590_ = v___x_1579_;
v_isShared_1591_ = v_isSharedCheck_1607_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_snapshotTasks_1588_);
lean_inc(v_infoState_1587_);
lean_inc(v_messages_1586_);
lean_inc(v_cache_1585_);
lean_inc(v_traceState_1580_);
lean_inc(v_auxDeclNGen_1584_);
lean_inc(v_ngen_1583_);
lean_inc(v_nextMacroScope_1582_);
lean_inc(v_env_1581_);
lean_dec(v___x_1579_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1607_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
uint64_t v_tid_1592_; lean_object* v_traces_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1606_; 
v_tid_1592_ = lean_ctor_get_uint64(v_traceState_1580_, sizeof(void*)*1);
v_traces_1593_ = lean_ctor_get(v_traceState_1580_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_traceState_1580_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1595_ = v_traceState_1580_;
v_isShared_1596_ = v_isSharedCheck_1606_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_traces_1593_);
lean_dec(v_traceState_1580_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1606_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1531_, v_traces_1593_);
lean_dec_ref(v_traces_1593_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1597_);
v___x_1599_ = v___x_1595_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1597_);
lean_ctor_set_uint64(v_reuseFailAlloc_1605_, sizeof(void*)*1, v_tid_1592_);
v___x_1599_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 4, v___x_1599_);
v___x_1601_ = v___x_1590_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_env_1581_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_nextMacroScope_1582_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_ngen_1583_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_auxDeclNGen_1584_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1604_, 5, v_cache_1585_);
lean_ctor_set(v_reuseFailAlloc_1604_, 6, v_messages_1586_);
lean_ctor_set(v_reuseFailAlloc_1604_, 7, v_infoState_1587_);
lean_ctor_set(v_reuseFailAlloc_1604_, 8, v_snapshotTasks_1588_);
v___x_1601_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_st_ref_set(v___y_1539_, v___x_1601_);
v___x_1603_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_fst_1541_);
return v___x_1603_;
}
}
}
}
}
else
{
goto v___jp_1572_;
}
}
else
{
goto v___jp_1572_;
}
}
v___jp_1608_:
{
double v___x_1610_; double v___x_1611_; double v___x_1612_; uint8_t v___x_1613_; 
v___x_1610_ = lean_unbox_float(v_snd_1558_);
v___x_1611_ = lean_unbox_float(v_fst_1557_);
v___x_1612_ = lean_float_sub(v___x_1610_, v___x_1611_);
v___x_1613_ = lean_float_decLt(v___y_1609_, v___x_1612_);
v___y_1578_ = v___x_1613_;
goto v___jp_1577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___boxed(lean_object* v_cls_1624_, lean_object* v_collapsed_1625_, lean_object* v_tag_1626_, lean_object* v_opts_1627_, lean_object* v_clsEnabled_1628_, lean_object* v_oldTraces_1629_, lean_object* v_msg_1630_, lean_object* v_resStartStop_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v_collapsed_boxed_1639_; uint8_t v_clsEnabled_boxed_1640_; lean_object* v_res_1641_; 
v_collapsed_boxed_1639_ = lean_unbox(v_collapsed_1625_);
v_clsEnabled_boxed_1640_ = lean_unbox(v_clsEnabled_1628_);
v_res_1641_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v_cls_1624_, v_collapsed_boxed_1639_, v_tag_1626_, v_opts_1627_, v_clsEnabled_boxed_1640_, v_oldTraces_1629_, v_msg_1630_, v_resStartStop_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec_ref(v_opts_1627_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(lean_object* v_cls_1644_, lean_object* v_msg_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_ref_1651_; lean_object* v___x_1652_; lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1697_; 
v_ref_1651_ = lean_ctor_get(v___y_1648_, 5);
v___x_1652_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msg_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1697_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1697_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v_traceState_1658_; lean_object* v_env_1659_; lean_object* v_nextMacroScope_1660_; lean_object* v_ngen_1661_; lean_object* v_auxDeclNGen_1662_; lean_object* v_cache_1663_; lean_object* v_messages_1664_; lean_object* v_infoState_1665_; lean_object* v_snapshotTasks_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1696_; 
v___x_1657_ = lean_st_ref_take(v___y_1649_);
v_traceState_1658_ = lean_ctor_get(v___x_1657_, 4);
v_env_1659_ = lean_ctor_get(v___x_1657_, 0);
v_nextMacroScope_1660_ = lean_ctor_get(v___x_1657_, 1);
v_ngen_1661_ = lean_ctor_get(v___x_1657_, 2);
v_auxDeclNGen_1662_ = lean_ctor_get(v___x_1657_, 3);
v_cache_1663_ = lean_ctor_get(v___x_1657_, 5);
v_messages_1664_ = lean_ctor_get(v___x_1657_, 6);
v_infoState_1665_ = lean_ctor_get(v___x_1657_, 7);
v_snapshotTasks_1666_ = lean_ctor_get(v___x_1657_, 8);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1668_ = v___x_1657_;
v_isShared_1669_ = v_isSharedCheck_1696_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_snapshotTasks_1666_);
lean_inc(v_infoState_1665_);
lean_inc(v_messages_1664_);
lean_inc(v_cache_1663_);
lean_inc(v_traceState_1658_);
lean_inc(v_auxDeclNGen_1662_);
lean_inc(v_ngen_1661_);
lean_inc(v_nextMacroScope_1660_);
lean_inc(v_env_1659_);
lean_dec(v___x_1657_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1696_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint64_t v_tid_1670_; lean_object* v_traces_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1695_; 
v_tid_1670_ = lean_ctor_get_uint64(v_traceState_1658_, sizeof(void*)*1);
v_traces_1671_ = lean_ctor_get(v_traceState_1658_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_traceState_1658_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1673_ = v_traceState_1658_;
v_isShared_1674_ = v_isSharedCheck_1695_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_traces_1671_);
lean_dec(v_traceState_1658_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1695_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; double v___x_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1675_ = lean_box(0);
v___x_1676_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0);
v___x_1677_ = 0;
v___x_1678_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26));
v___x_1679_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1679_, 0, v_cls_1644_);
lean_ctor_set(v___x_1679_, 1, v___x_1675_);
lean_ctor_set(v___x_1679_, 2, v___x_1678_);
lean_ctor_set_float(v___x_1679_, sizeof(void*)*3, v___x_1676_);
lean_ctor_set_float(v___x_1679_, sizeof(void*)*3 + 8, v___x_1676_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*3 + 16, v___x_1677_);
v___x_1680_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0));
v___x_1681_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v_a_1653_);
lean_ctor_set(v___x_1681_, 2, v___x_1680_);
lean_inc(v_ref_1651_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_ref_1651_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_PersistentArray_push___redArg(v_traces_1671_, v___x_1682_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1683_);
v___x_1685_ = v___x_1673_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1683_);
lean_ctor_set_uint64(v_reuseFailAlloc_1694_, sizeof(void*)*1, v_tid_1670_);
v___x_1685_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 4, v___x_1685_);
v___x_1687_ = v___x_1668_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_env_1659_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_nextMacroScope_1660_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_ngen_1661_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_auxDeclNGen_1662_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v_cache_1663_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_messages_1664_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v_infoState_1665_);
lean_ctor_set(v_reuseFailAlloc_1693_, 8, v_snapshotTasks_1666_);
v___x_1687_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1688_ = lean_st_ref_set(v___y_1649_, v___x_1687_);
v___x_1689_ = lean_box(0);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1689_);
v___x_1691_ = v___x_1655_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___boxed(lean_object* v_cls_1698_, lean_object* v_msg_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_1698_, v_msg_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1705_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(lean_object* v_as_x27_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
if (lean_obj_tag(v_as_x27_1711_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_b_1712_);
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; lean_object* v_snd_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1850_; 
v_head_1721_ = lean_ctor_get(v_as_x27_1711_, 0);
v_tail_1722_ = lean_ctor_get(v_as_x27_1711_, 1);
v_snd_1723_ = lean_ctor_get(v_b_1712_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_b_1712_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v_b_1712_, 0);
lean_dec(v_unused_1851_);
v___x_1725_ = v_b_1712_;
v_isShared_1726_ = v_isSharedCheck_1850_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_snd_1723_);
lean_dec(v_b_1712_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1850_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_options_1733_; lean_object* v_name_1734_; lean_object* v_run_x27_1735_; lean_object* v_inheritedTraceOptions_1736_; uint8_t v_hasTrace_1737_; lean_object* v___x_1738_; lean_object* v___y_1740_; uint8_t v___x_1766_; 
v_options_1733_ = lean_ctor_get(v___y_1717_, 2);
v_name_1734_ = lean_ctor_get(v_head_1721_, 0);
v_run_x27_1735_ = lean_ctor_get(v_head_1721_, 1);
v_inheritedTraceOptions_1736_ = lean_ctor_get(v___y_1717_, 13);
v_hasTrace_1737_ = lean_ctor_get_uint8(v_options_1733_, sizeof(void*)*1);
v___x_1738_ = lean_box(0);
v___x_1766_ = lean_bool_not(v_hasTrace_1737_);
if (v___x_1766_ == 0)
{
lean_object* v___f_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___y_1772_; uint8_t v___y_1773_; lean_object* v___y_1774_; lean_object* v_a_1775_; lean_object* v___y_1788_; lean_object* v___y_1789_; uint8_t v___y_1790_; lean_object* v_a_1791_; uint8_t v___y_1801_; uint8_t v_a_1843_; 
lean_inc(v_snd_1723_);
lean_inc(v_name_1734_);
v___f_1767_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1767_, 0, v_name_1734_);
lean_closure_set(v___f_1767_, 1, v_snd_1723_);
v___x_1768_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25));
v___x_1769_ = 1;
v___x_1770_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26));
if (v_hasTrace_1737_ == 0)
{
v_a_1843_ = v_hasTrace_1737_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30);
v___x_1848_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1736_, v_options_1733_, v___x_1847_);
if (v___x_1848_ == 0)
{
v_a_1843_ = v___x_1848_;
goto v___jp_1842_;
}
else
{
v___y_1801_ = v___x_1848_;
goto v___jp_1800_;
}
}
v___jp_1771_:
{
lean_object* v___x_1776_; double v___x_1777_; double v___x_1778_; double v___x_1779_; double v___x_1780_; double v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1776_ = lean_io_mono_nanos_now();
v___x_1777_ = lean_float_of_nat(v___y_1774_);
v___x_1778_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27);
v___x_1779_ = lean_float_div(v___x_1777_, v___x_1778_);
v___x_1780_ = lean_float_of_nat(v___x_1776_);
v___x_1781_ = lean_float_div(v___x_1780_, v___x_1778_);
v___x_1782_ = lean_box_float(v___x_1779_);
v___x_1783_ = lean_box_float(v___x_1781_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v_a_1775_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v___x_1768_, v___x_1769_, v___x_1770_, v_options_1733_, v___y_1773_, v___y_1772_, v___f_1767_, v___x_1785_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
v___y_1740_ = v___x_1786_;
goto v___jp_1739_;
}
v___jp_1787_:
{
lean_object* v___x_1792_; double v___x_1793_; double v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1792_ = lean_io_get_num_heartbeats();
v___x_1793_ = lean_float_of_nat(v___y_1788_);
v___x_1794_ = lean_float_of_nat(v___x_1792_);
v___x_1795_ = lean_box_float(v___x_1793_);
v___x_1796_ = lean_box_float(v___x_1794_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_a_1791_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v___x_1768_, v___x_1769_, v___x_1770_, v_options_1733_, v___y_1790_, v___y_1789_, v___f_1767_, v___x_1798_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
v___y_1740_ = v___x_1799_;
goto v___jp_1739_;
}
v___jp_1800_:
{
lean_object* v___x_1802_; lean_object* v_a_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1802_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_1718_);
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1802_);
v___x_1804_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1805_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_options_1733_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_1735_);
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1713_);
lean_inc(v_snd_1723_);
v___x_1807_ = lean_apply_8(v_run_x27_1735_, v_snd_1723_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, lean_box(0));
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 1);
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
v___y_1772_ = v_a_1803_;
v___y_1773_ = v___y_1801_;
v___y_1774_ = v___x_1806_;
v_a_1775_ = v___x_1813_;
goto v___jp_1771_;
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_a_1816_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1807_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1807_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 0);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
v___y_1772_ = v_a_1803_;
v___y_1773_ = v___y_1801_;
v___y_1774_ = v___x_1806_;
v_a_1775_ = v___x_1821_;
goto v___jp_1771_;
}
}
}
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_1735_);
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1713_);
lean_inc(v_snd_1723_);
v___x_1825_ = lean_apply_8(v_run_x27_1735_, v_snd_1723_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, lean_box(0));
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 1);
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
v___y_1788_ = v___x_1824_;
v___y_1789_ = v_a_1803_;
v___y_1790_ = v___y_1801_;
v_a_1791_ = v___x_1831_;
goto v___jp_1787_;
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
v_a_1834_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1825_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1825_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set_tag(v___x_1836_, 0);
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v___y_1788_ = v___x_1824_;
v___y_1789_ = v_a_1803_;
v___y_1790_ = v___y_1801_;
v_a_1791_ = v___x_1839_;
goto v___jp_1787_;
}
}
}
}
}
v___jp_1842_:
{
lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = l_Lean_trace_profiler;
v___x_1845_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_options_1733_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref(v___f_1767_);
lean_inc_ref(v_run_x27_1735_);
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1713_);
lean_inc(v_snd_1723_);
v___x_1846_ = lean_apply_8(v_run_x27_1735_, v_snd_1723_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, lean_box(0));
v___y_1740_ = v___x_1846_;
goto v___jp_1739_;
}
else
{
v___y_1801_ = v_a_1843_;
goto v___jp_1800_;
}
}
}
else
{
lean_object* v___x_1849_; 
lean_inc_ref(v_run_x27_1735_);
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1713_);
lean_inc(v_snd_1723_);
v___x_1849_ = lean_apply_8(v_run_x27_1735_, v_snd_1723_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, lean_box(0));
v___y_1740_ = v___x_1849_;
goto v___jp_1739_;
}
v___jp_1727_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0));
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1728_);
v___x_1730_ = v___x_1725_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_snd_1723_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
v___jp_1739_:
{
if (lean_obj_tag(v___y_1740_) == 0)
{
lean_object* v_a_1741_; 
v_a_1741_ = lean_ctor_get(v___y_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___y_1740_, 1);
if (lean_obj_tag(v_a_1741_) == 1)
{
lean_object* v_val_1742_; lean_object* v___x_1743_; 
lean_del_object(v___x_1725_);
lean_dec(v_snd_1723_);
v_val_1742_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_val_1742_);
lean_dec_ref_known(v_a_1741_, 1);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1738_);
lean_ctor_set(v___x_1743_, 1, v_val_1742_);
v_as_x27_1711_ = v_tail_1722_;
v_b_1712_ = v___x_1743_;
goto _start;
}
else
{
lean_dec(v_a_1741_);
if (v_hasTrace_1737_ == 0)
{
goto v___jp_1727_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1745_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25));
v___x_1746_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30);
v___x_1747_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1736_, v_options_1733_, v___x_1746_);
if (v___x_1747_ == 0)
{
goto v___jp_1727_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2);
v___x_1749_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1745_, v___x_1748_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_dec_ref_known(v___x_1749_, 1);
goto v___jp_1727_;
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_del_object(v___x_1725_);
lean_dec(v_snd_1723_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_del_object(v___x_1725_);
lean_dec(v_snd_1723_);
v_a_1758_ = lean_ctor_get(v___y_1740_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___y_1740_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___y_1740_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___y_1740_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___boxed(lean_object* v_as_x27_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_as_x27_1852_, v_b_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_as_x27_1852_);
return v_res_1861_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1));
v___x_1865_ = l_Lean_stringToMessageData(v___x_1864_);
return v___x_1865_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3));
v___x_1868_ = l_Lean_stringToMessageData(v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_1869_, lean_object* v_goal_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0));
v___x_1879_ = l_Lean_Core_checkSystem(v___x_1878_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1955_; 
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; 
v_unused_1956_ = lean_ctor_get(v___x_1879_, 0);
lean_dec(v_unused_1956_);
v___x_1881_ = v___x_1879_;
v_isShared_1882_ = v_isSharedCheck_1955_;
goto v_resetjp_1880_;
}
else
{
lean_dec(v___x_1879_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1955_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_box(0);
lean_inc(v_goal_1870_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v_goal_1870_);
v___x_1885_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_passes_1869_, v___x_1884_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1946_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1946_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1946_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_fst_1890_; lean_object* v_snd_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1945_; 
v_fst_1890_ = lean_ctor_get(v_a_1886_, 0);
v_snd_1891_ = lean_ctor_get(v_a_1886_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1893_ = v_a_1886_;
v_isShared_1894_ = v_isSharedCheck_1945_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_snd_1891_);
lean_inc(v_fst_1890_);
lean_dec(v_a_1886_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1945_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
if (lean_obj_tag(v_fst_1890_) == 0)
{
uint8_t v___x_1900_; uint8_t v___x_1901_; 
lean_del_object(v___x_1881_);
v___x_1900_ = l_Lean_instBEqMVarId_beq(v_goal_1870_, v_snd_1891_);
lean_dec(v_goal_1870_);
v___x_1901_ = lean_bool_not(v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v_options_1902_; uint8_t v_hasTrace_1903_; 
lean_del_object(v___x_1893_);
v_options_1902_ = lean_ctor_get(v_a_1875_, 2);
v_hasTrace_1903_ = lean_ctor_get_uint8(v_options_1902_, sizeof(void*)*1);
if (v_hasTrace_1903_ == 0)
{
goto v___jp_1895_;
}
else
{
lean_object* v_inheritedTraceOptions_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_inheritedTraceOptions_1904_ = lean_ctor_get(v_a_1875_, 13);
v___x_1905_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25));
v___x_1906_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30);
v___x_1907_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1904_, v_options_1902_, v___x_1906_);
if (v___x_1907_ == 0)
{
goto v___jp_1895_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2);
v___x_1909_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1905_, v___x_1908_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_dec_ref_known(v___x_1909_, 1);
goto v___jp_1895_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec(v_snd_1891_);
lean_del_object(v___x_1888_);
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
}
else
{
lean_object* v_options_1918_; uint8_t v_hasTrace_1919_; 
lean_del_object(v___x_1888_);
v_options_1918_ = lean_ctor_get(v_a_1875_, 2);
v_hasTrace_1919_ = lean_ctor_get_uint8(v_options_1918_, sizeof(void*)*1);
if (v_hasTrace_1919_ == 0)
{
lean_del_object(v___x_1893_);
v_goal_1870_ = v_snd_1891_;
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_inheritedTraceOptions_1921_ = lean_ctor_get(v_a_1875_, 13);
v___x_1922_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25));
v___x_1923_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30);
v___x_1924_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1921_, v_options_1918_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_del_object(v___x_1893_);
v_goal_1870_ = v_snd_1891_;
goto _start;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1926_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4);
lean_inc(v_snd_1891_);
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_snd_1891_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set_tag(v___x_1893_, 7);
lean_ctor_set(v___x_1893_, 1, v___x_1927_);
lean_ctor_set(v___x_1893_, 0, v___x_1926_);
v___x_1929_ = v___x_1893_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_1922_, v___x_1929_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_dec_ref_known(v___x_1930_, 1);
v_goal_1870_ = v_snd_1891_;
goto _start;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_snd_1891_);
v_a_1932_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1930_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1930_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
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
lean_object* v_val_1941_; lean_object* v___x_1943_; 
lean_del_object(v___x_1893_);
lean_dec(v_snd_1891_);
lean_del_object(v___x_1888_);
lean_dec(v_goal_1870_);
v_val_1941_ = lean_ctor_get(v_fst_1890_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_fst_1890_, 1);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_val_1941_);
v___x_1943_ = v___x_1881_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_val_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
v___jp_1895_:
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_snd_1891_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1896_);
v___x_1898_ = v___x_1888_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_del_object(v___x_1881_);
lean_dec(v_goal_1870_);
v_a_1947_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1885_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1885_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_goal_1870_);
v_a_1957_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1879_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1879_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_1965_, lean_object* v_goal_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_1965_, v_goal_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_passes_1965_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0(lean_object* v_cls_1975_, lean_object* v_msg_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_1975_, v_msg_1976_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___boxed(lean_object* v_cls_1985_, lean_object* v_msg_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0(v_cls_1985_, v_msg_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5(lean_object* v_00_u03b1_1995_, lean_object* v_x_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_x_1996_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_x_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5(v_00_u03b1_2005_, v_x_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4(lean_object* v_as_2015_, lean_object* v_as_x27_2016_, lean_object* v_b_2017_, lean_object* v_a_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_as_x27_2016_, v_b_2017_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___boxed(lean_object* v_as_2027_, lean_object* v_as_x27_2028_, lean_object* v_b_2029_, lean_object* v_a_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4(v_as_2027_, v_as_x27_2028_, v_b_2029_, v_a_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v_as_x27_2028_);
lean_dec(v_as_2027_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4(lean_object* v_oldTraces_2039_, lean_object* v_data_2040_, lean_object* v_ref_2041_, lean_object* v_msg_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___redArg(v_oldTraces_2039_, v_data_2040_, v_ref_2041_, v_msg_2042_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___boxed(lean_object* v_oldTraces_2051_, lean_object* v_data_2052_, lean_object* v_ref_2053_, lean_object* v_msg_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4(v_oldTraces_2051_, v_data_2052_, v_ref_2053_, v_msg_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2062_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
