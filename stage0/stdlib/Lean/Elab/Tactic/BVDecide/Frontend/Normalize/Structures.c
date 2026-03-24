// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Structures
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ApplyControlFlow public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis public import Lean.Meta.Injective
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_MVarId_casesRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_getStructureInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addDefaultTypeAnalysisLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__2_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__3_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__4_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "applyIteSimproc"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_3),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_4),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(8, 189, 229, 251, 108, 195, 96, 103)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value_aux_5),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(27, 24, 128, 124, 120, 160, 139, 112)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyIteSimproc___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "applyCondSimproc"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_3),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_4),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(8, 189, 229, 251, 108, 195, 96, 103)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value_aux_5),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(232, 74, 182, 48, 21, 14, 86, 195)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_applyCondSimproc___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__0_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__1_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__2_value_aux_1),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__2_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Using injEq lemma: "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__3 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__3_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2;
static const lean_array_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "structures preprocessor generated more than 1 goal"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structures"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 214, 82, 86, 36, 11, 245, 232)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___closed__3_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(lean_object* v_cls_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_options_7_; uint8_t v_hasTrace_8_; 
v_options_7_ = lean_ctor_get(v___y_5_, 2);
v_hasTrace_8_ = lean_ctor_get_uint8(v_options_7_, sizeof(void*)*1);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_cls_4_);
v___x_9_ = lean_box(v_hasTrace_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_inheritedTraceOptions_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_inheritedTraceOptions_11_ = lean_ctor_get(v___y_5_, 13);
v___x_12_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1));
v___x_13_ = l_Lean_Name_append(v___x_12_, v_cls_4_);
v___x_14_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_11_, v_options_7_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_box(v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___boxed(lean_object* v_cls_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(v_cls_17_, v___y_18_);
lean_dec_ref(v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3(lean_object* v_cls_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(v_cls_21_, v___y_26_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___boxed(lean_object* v_cls_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3(v_cls_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4_spec__6(lean_object* v_msgData_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_45_; lean_object* v_env_46_; lean_object* v___x_47_; lean_object* v_mctx_48_; lean_object* v_lctx_49_; lean_object* v_options_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_45_ = lean_st_ref_get(v___y_43_);
v_env_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc_ref(v_env_46_);
lean_dec(v___x_45_);
v___x_47_ = lean_st_ref_get(v___y_41_);
v_mctx_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_mctx_48_);
lean_dec(v___x_47_);
v_lctx_49_ = lean_ctor_get(v___y_40_, 2);
v_options_50_ = lean_ctor_get(v___y_42_, 2);
lean_inc_ref(v_options_50_);
lean_inc_ref(v_lctx_49_);
v___x_51_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_51_, 0, v_env_46_);
lean_ctor_set(v___x_51_, 1, v_mctx_48_);
lean_ctor_set(v___x_51_, 2, v_lctx_49_);
lean_ctor_set(v___x_51_, 3, v_options_50_);
v___x_52_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v_msgData_39_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4_spec__6___boxed(lean_object* v_msgData_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4_spec__6(v_msgData_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_60_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_61_; double v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_float_of_nat(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg(lean_object* v_cls_66_, lean_object* v_msg_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_ref_73_; lean_object* v___x_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_119_; 
v_ref_73_ = lean_ctor_get(v___y_70_, 5);
v___x_74_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4_spec__6(v_msg_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_119_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_119_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_119_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v_traceState_80_; lean_object* v_env_81_; lean_object* v_nextMacroScope_82_; lean_object* v_ngen_83_; lean_object* v_auxDeclNGen_84_; lean_object* v_cache_85_; lean_object* v_messages_86_; lean_object* v_infoState_87_; lean_object* v_snapshotTasks_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_118_; 
v___x_79_ = lean_st_ref_take(v___y_71_);
v_traceState_80_ = lean_ctor_get(v___x_79_, 4);
v_env_81_ = lean_ctor_get(v___x_79_, 0);
v_nextMacroScope_82_ = lean_ctor_get(v___x_79_, 1);
v_ngen_83_ = lean_ctor_get(v___x_79_, 2);
v_auxDeclNGen_84_ = lean_ctor_get(v___x_79_, 3);
v_cache_85_ = lean_ctor_get(v___x_79_, 5);
v_messages_86_ = lean_ctor_get(v___x_79_, 6);
v_infoState_87_ = lean_ctor_get(v___x_79_, 7);
v_snapshotTasks_88_ = lean_ctor_get(v___x_79_, 8);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_118_ == 0)
{
v___x_90_ = v___x_79_;
v_isShared_91_ = v_isSharedCheck_118_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_snapshotTasks_88_);
lean_inc(v_infoState_87_);
lean_inc(v_messages_86_);
lean_inc(v_cache_85_);
lean_inc(v_traceState_80_);
lean_inc(v_auxDeclNGen_84_);
lean_inc(v_ngen_83_);
lean_inc(v_nextMacroScope_82_);
lean_inc(v_env_81_);
lean_dec(v___x_79_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_118_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
uint64_t v_tid_92_; lean_object* v_traces_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_117_; 
v_tid_92_ = lean_ctor_get_uint64(v_traceState_80_, sizeof(void*)*1);
v_traces_93_ = lean_ctor_get(v_traceState_80_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v_traceState_80_);
if (v_isSharedCheck_117_ == 0)
{
v___x_95_ = v_traceState_80_;
v_isShared_96_ = v_isSharedCheck_117_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_traces_93_);
lean_dec(v_traceState_80_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_117_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; double v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_97_ = lean_box(0);
v___x_98_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__0);
v___x_99_ = 0;
v___x_100_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__1));
v___x_101_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_101_, 0, v_cls_66_);
lean_ctor_set(v___x_101_, 1, v___x_97_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set_float(v___x_101_, sizeof(void*)*3, v___x_98_);
lean_ctor_set_float(v___x_101_, sizeof(void*)*3 + 8, v___x_98_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*3 + 16, v___x_99_);
v___x_102_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___closed__2));
v___x_103_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v_a_75_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_inc(v_ref_73_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_ref_73_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = l_Lean_PersistentArray_push___redArg(v_traces_93_, v___x_104_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_105_);
v___x_107_ = v___x_95_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_105_);
lean_ctor_set_uint64(v_reuseFailAlloc_116_, sizeof(void*)*1, v_tid_92_);
v___x_107_ = v_reuseFailAlloc_116_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 4, v___x_107_);
v___x_109_ = v___x_90_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_env_81_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_nextMacroScope_82_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v_ngen_83_);
lean_ctor_set(v_reuseFailAlloc_115_, 3, v_auxDeclNGen_84_);
lean_ctor_set(v_reuseFailAlloc_115_, 4, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_115_, 5, v_cache_85_);
lean_ctor_set(v_reuseFailAlloc_115_, 6, v_messages_86_);
lean_ctor_set(v_reuseFailAlloc_115_, 7, v_infoState_87_);
lean_ctor_set(v_reuseFailAlloc_115_, 8, v_snapshotTasks_88_);
v___x_109_ = v_reuseFailAlloc_115_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_110_ = lean_st_ref_set(v___y_71_, v___x_109_);
v___x_111_ = lean_box(0);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_111_);
v___x_113_ = v___x_77_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg___boxed(lean_object* v_cls_120_, lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg(v_cls_120_, v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(lean_object* v_msg_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_ref_134_; lean_object* v___x_135_; lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_144_; 
v_ref_134_ = lean_ctor_get(v___y_131_, 5);
v___x_135_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4_spec__6(v_msg_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
v_a_136_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_144_ == 0)
{
v___x_138_ = v___x_135_;
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
lean_inc(v_ref_134_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_ref_134_);
lean_ctor_set(v___x_140_, 1, v_a_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 1);
lean_ctor_set(v___x_138_, 0, v___x_140_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg___boxed(lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_151_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__0));
v___x_154_ = l_Lean_stringToMessageData(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__2));
v___x_157_ = l_Lean_stringToMessageData(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0(lean_object* v_constName_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_env_167_; lean_object* v___x_168_; 
v___x_166_ = lean_st_ref_get(v___y_164_);
v_env_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_166_);
lean_inc(v_constName_158_);
v___x_168_ = l_Lean_isInductiveCore_x3f(v_env_167_, v_constName_158_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_169_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1);
v___x_170_ = 0;
v___x_171_ = l_Lean_MessageData_ofConstName(v_constName_158_, v___x_170_);
v___x_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_169_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3);
v___x_174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_174_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
return v___x_175_;
}
else
{
lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_constName_158_);
v_val_176_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_168_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_dec(v___x_168_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set_tag(v___x_178_, 0);
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_val_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___boxed(lean_object* v_constName_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0(v_constName_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_192_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_instMonadEIO(lean_box(0));
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2(lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_toApplicative_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_271_; 
v___x_206_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0);
v___x_207_ = l_StateRefT_x27_instMonad___redArg(v___x_206_);
v_toApplicative_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v___x_207_, 1);
lean_dec(v_unused_272_);
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_271_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_toApplicative_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_271_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_toFunctor_212_; lean_object* v_toSeq_213_; lean_object* v_toSeqLeft_214_; lean_object* v_toSeqRight_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_269_; 
v_toFunctor_212_ = lean_ctor_get(v_toApplicative_208_, 0);
v_toSeq_213_ = lean_ctor_get(v_toApplicative_208_, 2);
v_toSeqLeft_214_ = lean_ctor_get(v_toApplicative_208_, 3);
v_toSeqRight_215_ = lean_ctor_get(v_toApplicative_208_, 4);
v_isSharedCheck_269_ = !lean_is_exclusive(v_toApplicative_208_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; 
v_unused_270_ = lean_ctor_get(v_toApplicative_208_, 1);
lean_dec(v_unused_270_);
v___x_217_ = v_toApplicative_208_;
v_isShared_218_ = v_isSharedCheck_269_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_toSeqRight_215_);
lean_inc(v_toSeqLeft_214_);
lean_inc(v_toSeq_213_);
lean_inc(v_toFunctor_212_);
lean_dec(v_toApplicative_208_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_269_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___x_228_; 
v___f_219_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1));
v___f_220_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_212_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_221_, 0, v_toFunctor_212_);
v___f_222_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_222_, 0, v_toFunctor_212_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___f_221_);
lean_ctor_set(v___x_223_, 1, v___f_222_);
v___f_224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_224_, 0, v_toSeqRight_215_);
v___f_225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_225_, 0, v_toSeqLeft_214_);
v___f_226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_226_, 0, v_toSeq_213_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 4, v___f_224_);
lean_ctor_set(v___x_217_, 3, v___f_225_);
lean_ctor_set(v___x_217_, 2, v___f_226_);
lean_ctor_set(v___x_217_, 1, v___f_219_);
lean_ctor_set(v___x_217_, 0, v___x_223_);
v___x_228_ = v___x_217_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___f_219_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v___f_226_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v___f_224_);
v___x_228_ = v_reuseFailAlloc_268_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_230_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___f_220_);
lean_ctor_set(v___x_210_, 0, v___x_228_);
v___x_230_ = v___x_210_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___f_220_);
v___x_230_ = v_reuseFailAlloc_267_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v_toApplicative_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_265_; 
v___x_231_ = l_StateRefT_x27_instMonad___redArg(v___x_230_);
v_toApplicative_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_231_, 1);
lean_dec(v_unused_266_);
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_265_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_toApplicative_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_265_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_toFunctor_236_; lean_object* v_toSeq_237_; lean_object* v_toSeqLeft_238_; lean_object* v_toSeqRight_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_263_; 
v_toFunctor_236_ = lean_ctor_get(v_toApplicative_232_, 0);
v_toSeq_237_ = lean_ctor_get(v_toApplicative_232_, 2);
v_toSeqLeft_238_ = lean_ctor_get(v_toApplicative_232_, 3);
v_toSeqRight_239_ = lean_ctor_get(v_toApplicative_232_, 4);
v_isSharedCheck_263_ = !lean_is_exclusive(v_toApplicative_232_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v_toApplicative_232_, 1);
lean_dec(v_unused_264_);
v___x_241_ = v_toApplicative_232_;
v_isShared_242_ = v_isSharedCheck_263_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_toSeqRight_239_);
lean_inc(v_toSeqLeft_238_);
lean_inc(v_toSeq_237_);
lean_inc(v_toFunctor_236_);
lean_dec(v_toApplicative_232_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_263_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___f_245_; lean_object* v___f_246_; lean_object* v___x_247_; lean_object* v___f_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___x_252_; 
v___f_243_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3));
v___f_244_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_236_);
v___f_245_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_245_, 0, v_toFunctor_236_);
v___f_246_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_246_, 0, v_toFunctor_236_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___f_245_);
lean_ctor_set(v___x_247_, 1, v___f_246_);
v___f_248_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_248_, 0, v_toSeqRight_239_);
v___f_249_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_249_, 0, v_toSeqLeft_238_);
v___f_250_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_250_, 0, v_toSeq_237_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 4, v___f_248_);
lean_ctor_set(v___x_241_, 3, v___f_249_);
lean_ctor_set(v___x_241_, 2, v___f_250_);
lean_ctor_set(v___x_241_, 1, v___f_243_);
lean_ctor_set(v___x_241_, 0, v___x_247_);
v___x_252_ = v___x_241_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___f_243_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v___f_250_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v___f_249_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v___f_248_);
v___x_252_ = v_reuseFailAlloc_262_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___f_244_);
lean_ctor_set(v___x_234_, 0, v___x_252_);
v___x_254_ = v___x_234_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___f_244_);
v___x_254_ = v_reuseFailAlloc_261_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_19415__overap_259_; lean_object* v___x_260_; 
v___x_255_ = l_StateRefT_x27_instMonad___redArg(v___x_254_);
v___x_256_ = l_ReaderT_instMonad___redArg(v___x_255_);
v___x_257_ = lean_box(0);
v___x_258_ = l_instInhabitedOfMonad___redArg(v___x_256_, v___x_257_);
v___x_19415__overap_259_ = lean_panic_fn(v___x_258_, v_msg_198_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
lean_inc(v___y_202_);
lean_inc_ref(v___y_201_);
lean_inc(v___y_200_);
lean_inc_ref(v___y_199_);
v___x_260_ = lean_apply_7(v___x_19415__overap_259_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, lean_box(0));
return v___x_260_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___boxed(lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2(v_msg_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_281_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__0));
v___x_284_ = l_Lean_stringToMessageData(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_288_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__4));
v___x_289_ = lean_unsigned_to_nat(11u);
v___x_290_ = lean_unsigned_to_nat(122u);
v___x_291_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__3));
v___x_292_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__2));
v___x_293_ = l_mkPanicMessageWithDecl(v___x_292_, v___x_291_, v___x_290_, v___x_289_, v___x_288_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1(lean_object* v_constName_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_310_; lean_object* v_env_311_; uint8_t v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_st_ref_get(v___y_300_);
v_env_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref(v_env_311_);
lean_dec(v___x_310_);
v___x_312_ = 0;
lean_inc(v_constName_294_);
v___x_313_ = l_Lean_Environment_findAsync_x3f(v_env_311_, v_constName_294_, v___x_312_);
if (lean_obj_tag(v___x_313_) == 1)
{
lean_object* v_val_314_; uint8_t v_kind_315_; 
v_val_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_314_);
lean_dec_ref(v___x_313_);
v_kind_315_ = lean_ctor_get_uint8(v_val_314_, sizeof(void*)*3);
if (v_kind_315_ == 6)
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_314_);
if (lean_obj_tag(v___x_316_) == 6)
{
lean_object* v_val_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_constName_294_);
v_val_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_val_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 0);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_val_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec_ref(v___x_316_);
v___x_325_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5);
v___x_326_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2(v___x_325_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
if (lean_obj_tag(v_a_327_) == 0)
{
lean_del_object(v___x_329_);
goto v___jp_302_;
}
else
{
lean_object* v_val_331_; lean_object* v___x_333_; 
lean_dec(v_constName_294_);
v_val_331_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_val_331_);
lean_dec_ref(v_a_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v_val_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_val_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_constName_294_);
v_a_336_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_326_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_326_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
else
{
lean_dec(v_val_314_);
goto v___jp_302_;
}
}
else
{
lean_dec(v___x_313_);
goto v___jp_302_;
}
v___jp_302_:
{
lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_303_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1);
v___x_304_ = 0;
v___x_305_ = l_Lean_MessageData_ofConstName(v_constName_294_, v___x_304_);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1);
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_308_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___boxed(lean_object* v_constName_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1(v_constName_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(lean_object* v_upperBound_389_, lean_object* v_a_390_, lean_object* v___x_391_, lean_object* v_a_392_, lean_object* v_b_393_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_lt(v_a_392_, v_upperBound_389_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_dec(v_a_392_);
lean_dec(v___x_391_);
lean_dec(v_a_390_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_b_393_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_397_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1));
v___x_398_ = lean_unsigned_to_nat(5u);
lean_inc(v_a_392_);
lean_inc(v___x_391_);
lean_inc(v_a_390_);
v___x_399_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath(v_a_390_, v___x_391_, v_a_392_, v___x_397_, v___x_398_);
v___x_400_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9));
v___x_401_ = 0;
v___x_402_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11));
v___x_403_ = l_Lean_Meta_Simp_Simprocs_addCore(v_b_393_, v___x_399_, v___x_400_, v___x_401_, v___x_402_);
v___x_404_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13));
v___x_405_ = lean_unsigned_to_nat(4u);
lean_inc(v_a_392_);
lean_inc(v___x_391_);
lean_inc(v_a_390_);
v___x_406_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath(v_a_390_, v___x_391_, v_a_392_, v___x_404_, v___x_405_);
v___x_407_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15));
v___x_408_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__17));
v___x_409_ = l_Lean_Meta_Simp_Simprocs_addCore(v___x_403_, v___x_406_, v___x_407_, v___x_401_, v___x_408_);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_a_392_, v___x_410_);
lean_dec(v_a_392_);
v_a_392_ = v___x_411_;
v_b_393_ = v___x_409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___boxed(lean_object* v_upperBound_413_, lean_object* v_a_414_, lean_object* v___x_415_, lean_object* v_a_416_, lean_object* v_b_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(v_upperBound_413_, v_a_414_, v___x_415_, v_a_416_, v_b_417_);
lean_dec(v_upperBound_413_);
return v_res_419_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__4(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__3));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5(lean_object* v___x_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
if (lean_obj_tag(v_a_430_) == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v___x_429_);
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v_a_431_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
else
{
lean_object* v_key_441_; lean_object* v_tail_442_; lean_object* v___x_443_; 
v_key_441_ = lean_ctor_get(v_a_430_, 0);
lean_inc(v_key_441_);
v_tail_442_ = lean_ctor_get(v_a_430_, 2);
lean_inc(v_tail_442_);
lean_dec_ref(v_a_430_);
lean_inc(v_key_441_);
v___x_443_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0(v_key_441_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v_numParams_445_; lean_object* v_ctors_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref(v___x_443_);
v_numParams_445_ = lean_ctor_get(v_a_444_, 1);
lean_inc(v_numParams_445_);
v_ctors_446_ = lean_ctor_get(v_a_444_, 4);
lean_inc(v_ctors_446_);
lean_dec(v_a_444_);
v___x_447_ = lean_box(0);
v___x_448_ = l_List_head_x21___redArg(v___x_447_, v_ctors_446_);
lean_dec(v_ctors_446_);
v___x_449_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1(v___x_448_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_527_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_449_);
v___x_451_ = lean_st_ref_get(v___y_437_);
v_fst_452_ = lean_ctor_get(v_a_431_, 0);
v_snd_453_ = lean_ctor_get(v_a_431_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_527_ == 0)
{
v___x_455_ = v_a_431_;
v_isShared_456_ = v_isSharedCheck_527_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_snd_453_);
lean_inc(v_fst_452_);
lean_dec(v_a_431_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_527_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_lemmas_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v_toConstantVal_483_; lean_object* v_name_484_; lean_object* v_env_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; 
v_toConstantVal_483_ = lean_ctor_get(v_a_450_, 0);
lean_inc_ref(v_toConstantVal_483_);
lean_dec(v_a_450_);
v_name_484_ = lean_ctor_get(v_toConstantVal_483_, 0);
lean_inc(v_name_484_);
lean_dec_ref(v_toConstantVal_483_);
v_env_485_ = lean_ctor_get(v___x_451_, 0);
lean_inc_ref(v_env_485_);
lean_dec(v___x_451_);
v___x_486_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_484_);
v___x_487_ = 0;
lean_inc(v___x_486_);
v___x_488_ = l_Lean_Environment_find_x3f(v_env_485_, v___x_486_, v___x_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_dec(v___x_486_);
v_lemmas_458_ = v_snd_453_;
v___y_459_ = v___y_432_;
v___y_460_ = v___y_433_;
v___y_461_ = v___y_434_;
v___y_462_ = v___y_435_;
v___y_463_ = v___y_436_;
v___y_464_ = v___y_437_;
goto v___jp_457_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_a_491_; uint8_t v___x_492_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; uint8_t v___x_514_; 
lean_dec_ref(v___x_488_);
v___x_489_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__2));
v___x_490_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(v___x_489_, v___y_436_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v___x_492_ = 1;
v___x_514_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
if (v___x_514_ == 0)
{
v___y_494_ = v___y_432_;
v___y_495_ = v___y_433_;
v___y_496_ = v___y_434_;
v___y_497_ = v___y_435_;
v___y_498_ = v___y_436_;
v___y_499_ = v___y_437_;
goto v___jp_493_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__4, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__4_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___closed__4);
lean_inc(v___x_486_);
v___x_516_ = l_Lean_MessageData_ofName(v___x_486_);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg(v___x_489_, v___x_517_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_dec_ref(v___x_518_);
v___y_494_ = v___y_432_;
v___y_495_ = v___y_433_;
v___y_496_ = v___y_434_;
v___y_497_ = v___y_435_;
v___y_498_ = v___y_436_;
v___y_499_ = v___y_437_;
goto v___jp_493_;
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v___x_486_);
lean_del_object(v___x_455_);
lean_dec(v_snd_453_);
lean_dec(v_fst_452_);
lean_dec(v_numParams_445_);
lean_dec(v_tail_442_);
lean_dec(v_key_441_);
lean_dec_ref(v___x_429_);
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
v___jp_493_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc(v___x_486_);
v___x_500_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_500_, 0, v___x_486_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_492_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1 + 1, v___x_487_);
v___x_501_ = lean_box(0);
v___x_502_ = l_Lean_mkConst(v___x_486_, v___x_501_);
v___x_503_ = l_Lean_Meta_simpGlobalConfig;
v___x_504_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_snd_453_, v___x_500_, v___x_502_, v___x_503_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v_lemmas_458_ = v_a_505_;
v___y_459_ = v___y_494_;
v___y_460_ = v___y_495_;
v___y_461_ = v___y_496_;
v___y_462_ = v___y_497_;
v___y_463_ = v___y_498_;
v___y_464_ = v___y_499_;
goto v___jp_457_;
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_del_object(v___x_455_);
lean_dec(v_fst_452_);
lean_dec(v_numParams_445_);
lean_dec(v_tail_442_);
lean_dec(v_key_441_);
lean_dec_ref(v___x_429_);
v_a_506_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_504_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
v___jp_457_:
{
lean_object* v___x_465_; lean_object* v_fieldNames_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc(v_key_441_);
lean_inc_ref(v___x_429_);
v___x_465_ = l_Lean_getStructureInfo(v___x_429_, v_key_441_);
v_fieldNames_466_ = lean_ctor_get(v___x_465_, 1);
lean_inc_ref(v_fieldNames_466_);
lean_dec_ref(v___x_465_);
v___x_467_ = lean_array_get_size(v_fieldNames_466_);
lean_dec_ref(v_fieldNames_466_);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(v___x_467_, v_key_441_, v_numParams_445_, v___x_468_, v_fst_452_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v_lemmas_458_);
lean_ctor_set(v___x_455_, 0, v_a_470_);
v___x_472_ = v___x_455_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_470_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_lemmas_458_);
v___x_472_ = v_reuseFailAlloc_474_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
v_a_430_ = v_tail_442_;
v_a_431_ = v___x_472_;
goto _start;
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v_lemmas_458_);
lean_del_object(v___x_455_);
lean_dec(v_tail_442_);
lean_dec_ref(v___x_429_);
v_a_475_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_469_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_469_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_numParams_445_);
lean_dec(v_tail_442_);
lean_dec(v_key_441_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v___x_429_);
v_a_528_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_449_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_449_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_tail_442_);
lean_dec(v_key_441_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v___x_429_);
v_a_536_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_443_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_443_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___boxed(lean_object* v___x_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5(v___x_544_, v_a_545_, v_a_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__6(lean_object* v___x_555_, lean_object* v_as_556_, size_t v_sz_557_, size_t v_i_558_, lean_object* v_b_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = lean_usize_dec_lt(v_i_558_, v_sz_557_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
lean_dec_ref(v___x_555_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v_b_559_);
return v___x_568_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_array_uget_borrowed(v_as_556_, v_i_558_);
lean_inc(v_a_569_);
lean_inc_ref(v___x_555_);
v___x_570_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5(v___x_555_, v_a_569_, v_b_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_583_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_583_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_583_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_583_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
if (lean_obj_tag(v_a_571_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; 
lean_dec_ref(v___x_555_);
v_a_575_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_a_575_);
lean_dec_ref(v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_a_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
else
{
lean_object* v_a_579_; size_t v___x_580_; size_t v___x_581_; 
lean_del_object(v___x_573_);
v_a_579_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v_a_571_);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_558_, v___x_580_);
v_i_558_ = v___x_581_;
v_b_559_ = v_a_579_;
goto _start;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v___x_555_);
v_a_584_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_570_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_570_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__6___boxed(lean_object* v___x_592_, lean_object* v_as_593_, lean_object* v_sz_594_, lean_object* v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
size_t v_sz_boxed_604_; size_t v_i_boxed_605_; lean_object* v_res_606_; 
v_sz_boxed_604_ = lean_unbox_usize(v_sz_594_);
lean_dec(v_sz_594_);
v_i_boxed_605_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_res_606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__6(v___x_592_, v_as_593_, v_sz_boxed_604_, v_i_boxed_605_, v_b_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v_as_593_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas(lean_object* v_simprocs_607_, lean_object* v_lemmas_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_typeAnalysis_618_; lean_object* v_interestingStructures_619_; lean_object* v_env_620_; lean_object* v_buckets_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_648_; 
v___x_616_ = lean_st_ref_get(v_a_610_);
v___x_617_ = lean_st_ref_get(v_a_614_);
v_typeAnalysis_618_ = lean_ctor_get(v___x_616_, 2);
lean_inc_ref(v_typeAnalysis_618_);
lean_dec(v___x_616_);
v_interestingStructures_619_ = lean_ctor_get(v_typeAnalysis_618_, 0);
lean_inc_ref(v_interestingStructures_619_);
lean_dec_ref(v_typeAnalysis_618_);
v_env_620_ = lean_ctor_get(v___x_617_, 0);
lean_inc_ref(v_env_620_);
lean_dec(v___x_617_);
v_buckets_621_ = lean_ctor_get(v_interestingStructures_619_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_interestingStructures_619_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v_interestingStructures_619_, 0);
lean_dec(v_unused_649_);
v___x_623_ = v_interestingStructures_619_;
v_isShared_624_ = v_isSharedCheck_648_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_buckets_621_);
lean_dec(v_interestingStructures_619_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_648_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v_lemmas_608_);
lean_ctor_set(v___x_623_, 0, v_simprocs_607_);
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_simprocs_607_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_lemmas_608_);
v___x_626_ = v_reuseFailAlloc_647_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
size_t v_sz_627_; size_t v___x_628_; lean_object* v___x_629_; 
v_sz_627_ = lean_array_size(v_buckets_621_);
v___x_628_ = ((size_t)0ULL);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__6(v_env_620_, v_buckets_621_, v_sz_627_, v___x_628_, v___x_626_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec_ref(v_buckets_621_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_646_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_646_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_646_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_646_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_fst_634_; lean_object* v_snd_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_645_; 
v_fst_634_ = lean_ctor_get(v_a_630_, 0);
v_snd_635_ = lean_ctor_get(v_a_630_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_645_ == 0)
{
v___x_637_ = v_a_630_;
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_snd_635_);
lean_inc(v_fst_634_);
lean_dec(v_a_630_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_fst_634_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_snd_635_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_640_);
v___x_642_ = v___x_632_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
else
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas___boxed(lean_object* v_simprocs_650_, lean_object* v_lemmas_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas(v_simprocs_650_, v_lemmas_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2(lean_object* v_upperBound_660_, lean_object* v_a_661_, lean_object* v___x_662_, lean_object* v_inst_663_, lean_object* v_R_664_, lean_object* v_a_665_, lean_object* v_b_666_, lean_object* v_c_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(v_upperBound_660_, v_a_661_, v___x_662_, v_a_665_, v_b_666_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___boxed(lean_object* v_upperBound_676_, lean_object* v_a_677_, lean_object* v___x_678_, lean_object* v_inst_679_, lean_object* v_R_680_, lean_object* v_a_681_, lean_object* v_b_682_, lean_object* v_c_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2(v_upperBound_676_, v_a_677_, v___x_678_, v_inst_679_, v_R_680_, v_a_681_, v_b_682_, v_c_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v_upperBound_676_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4(lean_object* v_cls_692_, lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___redArg(v_cls_692_, v_msg_693_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___boxed(lean_object* v_cls_702_, lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4(v_cls_702_, v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0(lean_object* v_00_u03b1_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_713_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___boxed(lean_object* v_00_u03b1_722_, lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0(v_00_u03b1_722_, v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_731_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0(void){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_732_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0(lean_object* v_00_u03b2_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(lean_object* v_x_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; 
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
v___x_745_ = lean_apply_7(v_x_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, lean_box(0));
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed(lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(lean_object* v_mvarId_755_, lean_object* v_x_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___f_764_; lean_object* v___x_765_; 
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_764_, 0, v_x_756_);
lean_closure_set(v___f_764_, 1, v___y_757_);
lean_closure_set(v___f_764_, 2, v___y_758_);
v___x_765_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_755_, v___f_764_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
return v___x_765_;
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___boxed(lean_object* v_mvarId_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_774_, v_x_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1(lean_object* v_00_u03b1_784_, lean_object* v_mvarId_785_, lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_785_, v_x_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___boxed(lean_object* v_00_u03b1_795_, lean_object* v_mvarId_796_, lean_object* v_x_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1(v_00_u03b1_795_, v_mvarId_796_, v_x_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_805_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0(void){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_806_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_unsigned_to_nat(32u);
v___x_810_ = lean_mk_empty_array_with_capacity(v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0(lean_object* v_simprocs_812_, lean_object* v_relevantLemmas_813_, lean_object* v___x_814_, lean_object* v_goal_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas(v_simprocs_812_, v_relevantLemmas_813_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v_fst_825_; lean_object* v_snd_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_921_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref(v___x_823_);
v_fst_825_ = lean_ctor_get(v_a_824_, 0);
v_snd_826_ = lean_ctor_get(v_a_824_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_921_ == 0)
{
v___x_828_ = v_a_824_;
v_isShared_829_ = v_isSharedCheck_921_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_snd_826_);
lean_inc(v_fst_825_);
lean_dec(v_a_824_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_921_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addDefaultTypeAnalysisLemmas(v_snd_826_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
v___x_832_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_821_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v_maxSteps_834_; lean_object* v___x_835_; uint8_t v___x_836_; uint8_t v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref(v___x_832_);
v_maxSteps_834_ = lean_ctor_get(v___y_816_, 1);
v___x_835_ = lean_unsigned_to_nat(2u);
v___x_836_ = 0;
v___x_837_ = 1;
v___x_838_ = 0;
v___x_839_ = lean_box(0);
lean_inc(v_maxSteps_834_);
v___x_840_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_840_, 0, v_maxSteps_834_);
lean_ctor_set(v___x_840_, 1, v___x_835_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 1, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 2, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 3, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 4, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 5, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 6, v___x_838_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 7, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 8, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 9, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 10, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 11, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 12, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 13, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 14, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 15, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 16, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 17, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 18, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 19, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 20, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 21, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 22, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 23, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 24, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 25, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 26, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 27, v___x_836_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 28, v___x_836_);
v___x_841_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_840_, v_a_831_, v_a_833_, v___y_818_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___x_841_);
lean_inc_ref(v___y_818_);
v___x_843_ = l_Lean_Meta_getPropHyps(v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_843_);
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_mk_empty_array_with_capacity(v___x_845_);
v___x_847_ = lean_array_push(v___x_846_, v_fst_825_);
v___x_848_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1);
lean_inc(v___x_814_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_814_);
lean_ctor_set(v___x_828_, 0, v___x_848_);
v___x_850_ = v___x_828_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_814_);
v___x_850_ = v_reuseFailAlloc_888_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; size_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_851_ = lean_unsigned_to_nat(32u);
v___x_852_ = lean_mk_empty_array_with_capacity(v___x_851_);
v___x_853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2);
v___x_854_ = ((size_t)5ULL);
lean_inc(v___x_814_);
v___x_855_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_852_);
lean_ctor_set(v___x_855_, 2, v___x_814_);
lean_ctor_set(v___x_855_, 3, v___x_814_);
lean_ctor_set_usize(v___x_855_, 4, v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_856_, 0, v___x_848_);
lean_ctor_set(v___x_856_, 1, v___x_848_);
lean_ctor_set(v___x_856_, 2, v___x_848_);
lean_ctor_set(v___x_856_, 3, v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_850_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_Meta_simpGoal(v_goal_815_, v_a_842_, v___x_847_, v___x_839_, v___x_837_, v_a_844_, v___x_857_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_879_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_879_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_879_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_879_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_fst_863_; 
v_fst_863_ = lean_ctor_get(v_a_859_, 0);
lean_inc(v_fst_863_);
lean_dec(v_a_859_);
if (lean_obj_tag(v_fst_863_) == 1)
{
lean_object* v_val_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_875_; 
v_val_864_ = lean_ctor_get(v_fst_863_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_fst_863_);
if (v_isSharedCheck_875_ == 0)
{
v___x_866_ = v_fst_863_;
v_isShared_867_ = v_isSharedCheck_875_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_val_864_);
lean_dec(v_fst_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_875_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_snd_868_; lean_object* v___x_870_; 
v_snd_868_ = lean_ctor_get(v_val_864_, 1);
lean_inc(v_snd_868_);
lean_dec(v_val_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_snd_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_snd_868_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_870_);
v___x_872_ = v___x_861_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v___x_877_; 
lean_dec(v_fst_863_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_839_);
v___x_877_ = v___x_861_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_839_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_858_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_858_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_a_842_);
lean_del_object(v___x_828_);
lean_dec(v_fst_825_);
lean_dec(v_goal_815_);
lean_dec(v___x_814_);
v_a_889_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_843_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_843_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_828_);
lean_dec(v_fst_825_);
lean_dec(v_goal_815_);
lean_dec(v___x_814_);
v_a_897_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_841_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_841_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_a_831_);
lean_del_object(v___x_828_);
lean_dec(v_fst_825_);
lean_dec(v_goal_815_);
lean_dec(v___x_814_);
v_a_905_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_832_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_832_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_del_object(v___x_828_);
lean_dec(v_fst_825_);
lean_dec(v_goal_815_);
lean_dec(v___x_814_);
v_a_913_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_830_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_830_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_goal_815_);
lean_dec(v___x_814_);
v_a_922_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_823_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_823_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___boxed(lean_object* v_simprocs_930_, lean_object* v_relevantLemmas_931_, lean_object* v___x_932_, lean_object* v_goal_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0(v_simprocs_930_, v_relevantLemmas_931_, v___x_932_, v_goal_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_941_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0(void){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1(void){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0(lean_box(0));
return v___x_943_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_simprocs_946_; 
v___x_944_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1);
v___x_945_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0);
v_simprocs_946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_simprocs_946_, 0, v___x_945_);
lean_ctor_set(v_simprocs_946_, 1, v___x_945_);
lean_ctor_set(v_simprocs_946_, 2, v___x_944_);
lean_ctor_set(v_simprocs_946_, 3, v___x_944_);
return v_simprocs_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess(lean_object* v_goal_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_simprocs_957_; lean_object* v___x_958_; lean_object* v_relevantLemmas_959_; lean_object* v___f_960_; lean_object* v___x_961_; 
v_simprocs_957_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2);
v___x_958_ = lean_unsigned_to_nat(0u);
v_relevantLemmas_959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__3));
lean_inc(v_goal_949_);
v___f_960_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___boxed), 11, 4);
lean_closure_set(v___f_960_, 0, v_simprocs_957_);
lean_closure_set(v___f_960_, 1, v_relevantLemmas_959_);
lean_closure_set(v___f_960_, 2, v___x_958_);
lean_closure_set(v___f_960_, 3, v_goal_949_);
v___x_961_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(v_goal_949_, v___f_960_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___boxed(lean_object* v_goal_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess(v_goal_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(lean_object* v_e_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = l_Lean_Expr_hasMVar(v_e_971_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_e_971_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v_mctx_977_; lean_object* v___x_978_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_981_; lean_object* v_cache_982_; lean_object* v_zetaDeltaFVarIds_983_; lean_object* v_postponed_984_; lean_object* v_diag_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_994_; 
v___x_976_ = lean_st_ref_get(v___y_972_);
v_mctx_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_ref(v_mctx_977_);
lean_dec(v___x_976_);
v___x_978_ = l_Lean_instantiateMVarsCore(v_mctx_977_, v_e_971_);
v_fst_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_fst_979_);
v_snd_980_ = lean_ctor_get(v___x_978_, 1);
lean_inc(v_snd_980_);
lean_dec_ref(v___x_978_);
v___x_981_ = lean_st_ref_take(v___y_972_);
v_cache_982_ = lean_ctor_get(v___x_981_, 1);
v_zetaDeltaFVarIds_983_ = lean_ctor_get(v___x_981_, 2);
v_postponed_984_ = lean_ctor_get(v___x_981_, 3);
v_diag_985_ = lean_ctor_get(v___x_981_, 4);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_981_, 0);
lean_dec(v_unused_995_);
v___x_987_ = v___x_981_;
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_diag_985_);
lean_inc(v_postponed_984_);
lean_inc(v_zetaDeltaFVarIds_983_);
lean_inc(v_cache_982_);
lean_dec(v___x_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_snd_980_);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_snd_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_cache_982_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_zetaDeltaFVarIds_983_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_postponed_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_diag_985_);
v___x_990_ = v_reuseFailAlloc_993_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_st_ref_set(v___y_972_, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_fst_979_);
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg___boxed(lean_object* v_e_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(v_e_996_, v___y_997_);
lean_dec(v___y_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0(lean_object* v_e_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(v_e_1000_, v___y_1002_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___boxed(lean_object* v_e_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0(v_e_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1013_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(lean_object* v_a_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 0)
{
uint8_t v___x_1016_; 
v___x_1016_ = 0;
return v___x_1016_;
}
else
{
lean_object* v_key_1017_; lean_object* v_tail_1018_; uint8_t v___x_1019_; 
v_key_1017_ = lean_ctor_get(v_x_1015_, 0);
v_tail_1018_ = lean_ctor_get(v_x_1015_, 2);
v___x_1019_ = lean_name_eq(v_key_1017_, v_a_1014_);
if (v___x_1019_ == 0)
{
v_x_1015_ = v_tail_1018_;
goto _start;
}
else
{
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg___boxed(lean_object* v_a_1021_, lean_object* v_x_1022_){
_start:
{
uint8_t v_res_1023_; lean_object* v_r_1024_; 
v_res_1023_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_1021_, v_x_1022_);
lean_dec(v_x_1022_);
lean_dec(v_a_1021_);
v_r_1024_ = lean_box(v_res_1023_);
return v_r_1024_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1025_; uint64_t v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(1723u);
v___x_1026_ = lean_uint64_of_nat(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(lean_object* v_m_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_buckets_1029_; lean_object* v___x_1030_; uint64_t v___y_1032_; 
v_buckets_1029_ = lean_ctor_get(v_m_1027_, 1);
v___x_1030_ = lean_array_get_size(v_buckets_1029_);
if (lean_obj_tag(v_a_1028_) == 0)
{
uint64_t v___x_1046_; 
v___x_1046_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0);
v___y_1032_ = v___x_1046_;
goto v___jp_1031_;
}
else
{
uint64_t v_hash_1047_; 
v_hash_1047_ = lean_ctor_get_uint64(v_a_1028_, sizeof(void*)*2);
v___y_1032_ = v_hash_1047_;
goto v___jp_1031_;
}
v___jp_1031_:
{
uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v_fold_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1033_ = 32ULL;
v___x_1034_ = lean_uint64_shift_right(v___y_1032_, v___x_1033_);
v_fold_1035_ = lean_uint64_xor(v___y_1032_, v___x_1034_);
v___x_1036_ = 16ULL;
v___x_1037_ = lean_uint64_shift_right(v_fold_1035_, v___x_1036_);
v___x_1038_ = lean_uint64_xor(v_fold_1035_, v___x_1037_);
v___x_1039_ = lean_uint64_to_usize(v___x_1038_);
v___x_1040_ = lean_usize_of_nat(v___x_1030_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_sub(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_usize_land(v___x_1039_, v___x_1042_);
v___x_1044_ = lean_array_uget_borrowed(v_buckets_1029_, v___x_1043_);
v___x_1045_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_1028_, v___x_1044_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___boxed(lean_object* v_m_1048_, lean_object* v_a_1049_){
_start:
{
uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_res_1050_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(v_m_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_m_1048_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0(uint8_t v___x_1052_, lean_object* v_interestingStructures_1053_, lean_object* v_decl_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = l_Lean_LocalDecl_isLet(v_decl_1054_, v___x_1052_);
if (v___x_1060_ == 0)
{
uint8_t v___x_1061_; 
v___x_1061_ = l_Lean_LocalDecl_isImplementationDetail(v_decl_1054_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1080_; 
v___x_1062_ = l_Lean_LocalDecl_type(v_decl_1054_);
v___x_1063_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(v___x_1062_, v___y_1056_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = l_Lean_Expr_getAppFn(v_a_1064_);
lean_dec(v_a_1064_);
v___x_1069_ = l_Lean_Expr_constName_x3f(v___x_1068_);
lean_dec_ref(v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 1)
{
lean_object* v_val_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v_val_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_val_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(v_interestingStructures_1053_, v_val_1070_);
lean_dec(v_val_1070_);
v___x_1072_ = lean_box(v___x_1071_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1072_);
v___x_1074_ = v___x_1066_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec(v___x_1069_);
v___x_1076_ = lean_box(v___x_1052_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1076_);
v___x_1078_ = v___x_1066_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_box(v___x_1052_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_box(v___x_1052_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0___boxed(lean_object* v___x_1085_, lean_object* v_interestingStructures_1086_, lean_object* v_decl_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v___x_3219__boxed_1093_; lean_object* v_res_1094_; 
v___x_3219__boxed_1093_ = lean_unbox(v___x_1085_);
v_res_1094_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0(v___x_3219__boxed_1093_, v_interestingStructures_1086_, v_decl_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec_ref(v_decl_1087_);
lean_dec_ref(v_interestingStructures_1086_);
return v_res_1094_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__0));
v___x_1097_ = l_Lean_stringToMessageData(v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1(lean_object* v_goal_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v_typeAnalysis_1107_; lean_object* v_interestingStructures_1108_; lean_object* v_size_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1106_ = lean_st_ref_get(v___y_1100_);
v_typeAnalysis_1107_ = lean_ctor_get(v___x_1106_, 2);
lean_inc_ref(v_typeAnalysis_1107_);
lean_dec(v___x_1106_);
v_interestingStructures_1108_ = lean_ctor_get(v_typeAnalysis_1107_, 0);
lean_inc_ref(v_interestingStructures_1108_);
lean_dec_ref(v_typeAnalysis_1107_);
v_size_1109_ = lean_ctor_get(v_interestingStructures_1108_, 0);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = lean_nat_dec_eq(v_size_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_box(v___x_1111_);
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1113_, 0, v___x_1112_);
lean_closure_set(v___f_1113_, 1, v_interestingStructures_1108_);
v___x_1114_ = l_Lean_MVarId_casesRec(v_goal_1098_, v___f_1113_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref(v___x_1114_);
if (lean_obj_tag(v_a_1115_) == 1)
{
lean_object* v_tail_1123_; 
v_tail_1123_ = lean_ctor_get(v_a_1115_, 1);
if (lean_obj_tag(v_tail_1123_) == 0)
{
lean_object* v_head_1124_; lean_object* v___x_1125_; 
v_head_1124_ = lean_ctor_get(v_a_1115_, 0);
lean_inc(v_head_1124_);
lean_dec_ref(v_a_1115_);
v___x_1125_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess(v_head_1124_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1125_;
}
else
{
lean_dec_ref(v_a_1115_);
v___y_1117_ = v___y_1101_;
v___y_1118_ = v___y_1102_;
v___y_1119_ = v___y_1103_;
v___y_1120_ = v___y_1104_;
goto v___jp_1116_;
}
}
else
{
lean_dec(v_a_1115_);
v___y_1117_ = v___y_1101_;
v___y_1118_ = v___y_1102_;
v___y_1119_ = v___y_1103_;
v___y_1120_ = v___y_1104_;
goto v___jp_1116_;
}
v___jp_1116_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1);
v___x_1122_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_1121_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
return v___x_1122_;
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1114_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1114_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref(v_interestingStructures_1108_);
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_goal_1098_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___boxed(lean_object* v_goal_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1(v_goal_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1144_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1(lean_object* v_00_u03b2_1153_, lean_object* v_m_1154_, lean_object* v_a_1155_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(v_m_1154_, v_a_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___boxed(lean_object* v_00_u03b2_1157_, lean_object* v_m_1158_, lean_object* v_a_1159_){
_start:
{
uint8_t v_res_1160_; lean_object* v_r_1161_; 
v_res_1160_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1(v_00_u03b2_1157_, v_m_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_m_1158_);
v_r_1161_ = lean_box(v_res_1160_);
return v_r_1161_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1(lean_object* v_00_u03b2_1162_, lean_object* v_a_1163_, lean_object* v_x_1164_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_1163_, v_x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1166_, lean_object* v_a_1167_, lean_object* v_x_1168_){
_start:
{
uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1(v_00_u03b2_1166_, v_a_1167_, v_x_1168_);
lean_dec(v_x_1168_);
lean_dec(v_a_1167_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Injective(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Injective(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures(builtin);
}
#ifdef __cplusplus
}
#endif
