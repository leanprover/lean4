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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_MVarId_casesRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_getStructureInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addDefaultTypeAnalysisLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__0_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__1_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2_value_aux_1),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__3 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__3_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__4 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__4_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__5;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Using injEq lemma: "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__6 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__6_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__7;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3_spec__5(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3_spec__5___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__2));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0(lean_object* v_constName_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v_env_62_; lean_object* v___x_63_; 
v___x_61_ = lean_st_ref_get(v___y_59_);
v_env_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_env_62_);
lean_dec(v___x_61_);
lean_inc(v_constName_53_);
v___x_63_ = l_Lean_isInductiveCore_x3f(v_env_62_, v_constName_53_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_64_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1);
v___x_65_ = 0;
v___x_66_ = l_Lean_MessageData_ofConstName(v_constName_53_, v___x_65_);
v___x_67_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__3);
v___x_69_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_69_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
lean_dec(v_constName_53_);
v_val_71_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___x_63_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_val_71_);
lean_dec(v___x_63_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set_tag(v___x_73_, 0);
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_val_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___boxed(lean_object* v_constName_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0(v_constName_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_87_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_instMonadEIO(lean_box(0));
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2(lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_toApplicative_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_166_; 
v___x_101_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0);
v___x_102_ = l_StateRefT_x27_instMonad___redArg(v___x_101_);
v_toApplicative_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v___x_102_, 1);
lean_dec(v_unused_167_);
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_166_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_toApplicative_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_166_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_toFunctor_107_; lean_object* v_toSeq_108_; lean_object* v_toSeqLeft_109_; lean_object* v_toSeqRight_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_164_; 
v_toFunctor_107_ = lean_ctor_get(v_toApplicative_103_, 0);
v_toSeq_108_ = lean_ctor_get(v_toApplicative_103_, 2);
v_toSeqLeft_109_ = lean_ctor_get(v_toApplicative_103_, 3);
v_toSeqRight_110_ = lean_ctor_get(v_toApplicative_103_, 4);
v_isSharedCheck_164_ = !lean_is_exclusive(v_toApplicative_103_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v_toApplicative_103_, 1);
lean_dec(v_unused_165_);
v___x_112_ = v_toApplicative_103_;
v_isShared_113_ = v_isSharedCheck_164_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_toSeqRight_110_);
lean_inc(v_toSeqLeft_109_);
lean_inc(v_toSeq_108_);
lean_inc(v_toFunctor_107_);
lean_dec(v_toApplicative_103_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_164_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_123_; 
v___f_114_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1));
v___f_115_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_107_);
v___f_116_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_116_, 0, v_toFunctor_107_);
v___f_117_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_117_, 0, v_toFunctor_107_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___f_116_);
lean_ctor_set(v___x_118_, 1, v___f_117_);
v___f_119_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_119_, 0, v_toSeqRight_110_);
v___f_120_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_120_, 0, v_toSeqLeft_109_);
v___f_121_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_121_, 0, v_toSeq_108_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___f_119_);
lean_ctor_set(v___x_112_, 3, v___f_120_);
lean_ctor_set(v___x_112_, 2, v___f_121_);
lean_ctor_set(v___x_112_, 1, v___f_114_);
lean_ctor_set(v___x_112_, 0, v___x_118_);
v___x_123_ = v___x_112_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___f_114_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v___f_121_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v___f_120_);
lean_ctor_set(v_reuseFailAlloc_163_, 4, v___f_119_);
v___x_123_ = v_reuseFailAlloc_163_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___f_115_);
lean_ctor_set(v___x_105_, 0, v___x_123_);
v___x_125_ = v___x_105_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___f_115_);
v___x_125_ = v_reuseFailAlloc_162_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v_toApplicative_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_160_; 
v___x_126_ = l_StateRefT_x27_instMonad___redArg(v___x_125_);
v_toApplicative_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v___x_126_, 1);
lean_dec(v_unused_161_);
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_160_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_toApplicative_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_160_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_toFunctor_131_; lean_object* v_toSeq_132_; lean_object* v_toSeqLeft_133_; lean_object* v_toSeqRight_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_158_; 
v_toFunctor_131_ = lean_ctor_get(v_toApplicative_127_, 0);
v_toSeq_132_ = lean_ctor_get(v_toApplicative_127_, 2);
v_toSeqLeft_133_ = lean_ctor_get(v_toApplicative_127_, 3);
v_toSeqRight_134_ = lean_ctor_get(v_toApplicative_127_, 4);
v_isSharedCheck_158_ = !lean_is_exclusive(v_toApplicative_127_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_toApplicative_127_, 1);
lean_dec(v_unused_159_);
v___x_136_ = v_toApplicative_127_;
v_isShared_137_ = v_isSharedCheck_158_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_toSeqRight_134_);
lean_inc(v_toSeqLeft_133_);
lean_inc(v_toSeq_132_);
lean_inc(v_toFunctor_131_);
lean_dec(v_toApplicative_127_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_158_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_147_; 
v___f_138_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3));
v___f_139_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_131_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_140_, 0, v_toFunctor_131_);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_141_, 0, v_toFunctor_131_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___f_140_);
lean_ctor_set(v___x_142_, 1, v___f_141_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_143_, 0, v_toSeqRight_134_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_144_, 0, v_toSeqLeft_133_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_145_, 0, v_toSeq_132_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 4, v___f_143_);
lean_ctor_set(v___x_136_, 3, v___f_144_);
lean_ctor_set(v___x_136_, 2, v___f_145_);
lean_ctor_set(v___x_136_, 1, v___f_138_);
lean_ctor_set(v___x_136_, 0, v___x_142_);
v___x_147_ = v___x_136_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___f_138_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v___f_145_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v___f_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v___f_143_);
v___x_147_ = v_reuseFailAlloc_157_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_149_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___f_139_);
lean_ctor_set(v___x_129_, 0, v___x_147_);
v___x_149_ = v___x_129_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___f_139_);
v___x_149_ = v_reuseFailAlloc_156_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_20021__overap_154_; lean_object* v___x_155_; 
v___x_150_ = l_StateRefT_x27_instMonad___redArg(v___x_149_);
v___x_151_ = l_ReaderT_instMonad___redArg(v___x_150_);
v___x_152_ = lean_box(0);
v___x_153_ = l_instInhabitedOfMonad___redArg(v___x_151_, v___x_152_);
v___x_20021__overap_154_ = lean_panic_fn_borrowed(v___x_153_, v_msg_93_);
lean_dec(v___x_153_);
lean_inc(v___y_99_);
lean_inc_ref(v___y_98_);
lean_inc(v___y_97_);
lean_inc_ref(v___y_96_);
lean_inc(v___y_95_);
lean_inc_ref(v___y_94_);
v___x_155_ = lean_apply_7(v___x_20021__overap_154_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, lean_box(0));
return v___x_155_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2___boxed(lean_object* v_msg_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2(v_msg_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_176_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__0));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_183_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__4));
v___x_184_ = lean_unsigned_to_nat(11u);
v___x_185_ = lean_unsigned_to_nat(122u);
v___x_186_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__3));
v___x_187_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__2));
v___x_188_ = l_mkPanicMessageWithDecl(v___x_187_, v___x_186_, v___x_185_, v___x_184_, v___x_183_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1(lean_object* v_constName_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_205_; lean_object* v_env_206_; uint8_t v___x_207_; lean_object* v___x_208_; 
v___x_205_ = lean_st_ref_get(v___y_195_);
v_env_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc_ref(v_env_206_);
lean_dec(v___x_205_);
v___x_207_ = 0;
lean_inc(v_constName_189_);
v___x_208_ = l_Lean_Environment_findAsync_x3f(v_env_206_, v_constName_189_, v___x_207_);
if (lean_obj_tag(v___x_208_) == 1)
{
lean_object* v_val_209_; uint8_t v_kind_210_; 
v_val_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_209_);
lean_dec_ref(v___x_208_);
v_kind_210_ = lean_ctor_get_uint8(v_val_209_, sizeof(void*)*3);
if (v_kind_210_ == 6)
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_209_);
if (lean_obj_tag(v___x_211_) == 6)
{
lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_constName_189_);
v_val_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 0);
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_val_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref(v___x_211_);
v___x_220_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__5);
v___x_221_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1_spec__2(v___x_220_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
if (lean_obj_tag(v_a_222_) == 0)
{
lean_del_object(v___x_224_);
goto v___jp_197_;
}
else
{
lean_object* v_val_226_; lean_object* v___x_228_; 
lean_dec(v_constName_189_);
v_val_226_ = lean_ctor_get(v_a_222_, 0);
lean_inc(v_val_226_);
lean_dec_ref(v_a_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v_val_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_val_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec(v_constName_189_);
v_a_231_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_221_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_221_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
else
{
lean_dec(v_val_209_);
goto v___jp_197_;
}
}
else
{
lean_dec(v___x_208_);
goto v___jp_197_;
}
v___jp_197_:
{
lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_198_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0___closed__1);
v___x_199_ = 0;
v___x_200_ = l_Lean_MessageData_ofConstName(v_constName_189_, v___x_199_);
v___x_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_198_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___closed__1);
v___x_203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_203_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1___boxed(lean_object* v_constName_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1(v_constName_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_247_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_248_; double v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_float_of_nat(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(lean_object* v_cls_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_ref_260_; lean_object* v___x_261_; lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_306_; 
v_ref_260_ = lean_ctor_get(v___y_257_, 5);
v___x_261_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_306_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_306_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_306_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v_traceState_267_; lean_object* v_env_268_; lean_object* v_nextMacroScope_269_; lean_object* v_ngen_270_; lean_object* v_auxDeclNGen_271_; lean_object* v_cache_272_; lean_object* v_messages_273_; lean_object* v_infoState_274_; lean_object* v_snapshotTasks_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_305_; 
v___x_266_ = lean_st_ref_take(v___y_258_);
v_traceState_267_ = lean_ctor_get(v___x_266_, 4);
v_env_268_ = lean_ctor_get(v___x_266_, 0);
v_nextMacroScope_269_ = lean_ctor_get(v___x_266_, 1);
v_ngen_270_ = lean_ctor_get(v___x_266_, 2);
v_auxDeclNGen_271_ = lean_ctor_get(v___x_266_, 3);
v_cache_272_ = lean_ctor_get(v___x_266_, 5);
v_messages_273_ = lean_ctor_get(v___x_266_, 6);
v_infoState_274_ = lean_ctor_get(v___x_266_, 7);
v_snapshotTasks_275_ = lean_ctor_get(v___x_266_, 8);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_305_ == 0)
{
v___x_277_ = v___x_266_;
v_isShared_278_ = v_isSharedCheck_305_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snapshotTasks_275_);
lean_inc(v_infoState_274_);
lean_inc(v_messages_273_);
lean_inc(v_cache_272_);
lean_inc(v_traceState_267_);
lean_inc(v_auxDeclNGen_271_);
lean_inc(v_ngen_270_);
lean_inc(v_nextMacroScope_269_);
lean_inc(v_env_268_);
lean_dec(v___x_266_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_305_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint64_t v_tid_279_; lean_object* v_traces_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_304_; 
v_tid_279_ = lean_ctor_get_uint64(v_traceState_267_, sizeof(void*)*1);
v_traces_280_ = lean_ctor_get(v_traceState_267_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_traceState_267_);
if (v_isSharedCheck_304_ == 0)
{
v___x_282_ = v_traceState_267_;
v_isShared_283_ = v_isSharedCheck_304_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_traces_280_);
lean_dec(v_traceState_267_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_304_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; double v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_284_ = lean_box(0);
v___x_285_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0);
v___x_286_ = 0;
v___x_287_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1));
v___x_288_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_288_, 0, v_cls_253_);
lean_ctor_set(v___x_288_, 1, v___x_284_);
lean_ctor_set(v___x_288_, 2, v___x_287_);
lean_ctor_set_float(v___x_288_, sizeof(void*)*3, v___x_285_);
lean_ctor_set_float(v___x_288_, sizeof(void*)*3 + 8, v___x_285_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*3 + 16, v___x_286_);
v___x_289_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2));
v___x_290_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v_a_262_);
lean_ctor_set(v___x_290_, 2, v___x_289_);
lean_inc(v_ref_260_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_ref_260_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_PersistentArray_push___redArg(v_traces_280_, v___x_291_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_292_);
v___x_294_ = v___x_282_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_292_);
lean_ctor_set_uint64(v_reuseFailAlloc_303_, sizeof(void*)*1, v_tid_279_);
v___x_294_ = v_reuseFailAlloc_303_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_296_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 4, v___x_294_);
v___x_296_ = v___x_277_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_env_268_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_nextMacroScope_269_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_ngen_270_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_auxDeclNGen_271_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_302_, 5, v_cache_272_);
lean_ctor_set(v_reuseFailAlloc_302_, 6, v_messages_273_);
lean_ctor_set(v_reuseFailAlloc_302_, 7, v_infoState_274_);
lean_ctor_set(v_reuseFailAlloc_302_, 8, v_snapshotTasks_275_);
v___x_296_ = v_reuseFailAlloc_302_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_297_ = lean_st_ref_set(v___y_258_, v___x_296_);
v___x_298_ = lean_box(0);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_298_);
v___x_300_ = v___x_264_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg___boxed(lean_object* v_cls_307_, lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(v_cls_307_, v_msg_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(lean_object* v_upperBound_351_, lean_object* v_a_352_, lean_object* v___x_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_nat_dec_lt(v_a_354_, v_upperBound_351_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v_a_354_);
lean_dec(v___x_353_);
lean_dec(v_a_352_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v_b_355_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1));
v___x_360_ = lean_unsigned_to_nat(5u);
lean_inc_n(v_a_354_, 2);
lean_inc_n(v___x_353_, 2);
lean_inc_n(v_a_352_, 2);
v___x_361_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath(v_a_352_, v___x_353_, v_a_354_, v___x_359_, v___x_360_);
v___x_362_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9));
v___x_363_ = 0;
v___x_364_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11));
v___x_365_ = l_Lean_Meta_Simp_Simprocs_addCore(v_b_355_, v___x_361_, v___x_362_, v___x_363_, v___x_364_);
v___x_366_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13));
v___x_367_ = lean_unsigned_to_nat(4u);
v___x_368_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkApplyProjControlDiscrPath(v_a_352_, v___x_353_, v_a_354_, v___x_366_, v___x_367_);
v___x_369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15));
v___x_370_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__17));
v___x_371_ = l_Lean_Meta_Simp_Simprocs_addCore(v___x_365_, v___x_368_, v___x_369_, v___x_363_, v___x_370_);
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_nat_add(v_a_354_, v___x_372_);
lean_dec(v_a_354_);
v_a_354_ = v___x_373_;
v_b_355_ = v___x_371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg___boxed(lean_object* v_upperBound_375_, lean_object* v_a_376_, lean_object* v___x_377_, lean_object* v_a_378_, lean_object* v_b_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(v_upperBound_375_, v_a_376_, v___x_377_, v_a_378_, v_b_379_);
lean_dec(v_upperBound_375_);
return v_res_381_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__5(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2));
v___x_392_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__4));
v___x_393_ = l_Lean_Name_append(v___x_392_, v___x_391_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__7(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__6));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4(lean_object* v___x_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
if (lean_obj_tag(v_a_398_) == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref(v___x_397_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v_a_399_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
else
{
lean_object* v_key_409_; lean_object* v_tail_410_; lean_object* v___x_411_; 
v_key_409_ = lean_ctor_get(v_a_398_, 0);
lean_inc_n(v_key_409_, 2);
v_tail_410_ = lean_ctor_get(v_a_398_, 2);
lean_inc(v_tail_410_);
lean_dec_ref(v_a_398_);
v___x_411_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0(v_key_409_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_numParams_413_; lean_object* v_ctors_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
v_numParams_413_ = lean_ctor_get(v_a_412_, 1);
lean_inc(v_numParams_413_);
v_ctors_414_ = lean_ctor_get(v_a_412_, 4);
lean_inc(v_ctors_414_);
lean_dec(v_a_412_);
v___x_415_ = lean_box(0);
v___x_416_ = l_List_head_x21___redArg(v___x_415_, v_ctors_414_);
lean_dec(v_ctors_414_);
v___x_417_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__1(v___x_416_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_419_; lean_object* v_fst_420_; lean_object* v_snd_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_497_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref(v___x_417_);
v___x_419_ = lean_st_ref_get(v___y_405_);
v_fst_420_ = lean_ctor_get(v_a_399_, 0);
v_snd_421_ = lean_ctor_get(v_a_399_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_399_);
if (v_isSharedCheck_497_ == 0)
{
v___x_423_ = v_a_399_;
v_isShared_424_ = v_isSharedCheck_497_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snd_421_);
lean_inc(v_fst_420_);
lean_dec(v_a_399_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_497_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_lemmas_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v_toConstantVal_451_; lean_object* v_name_452_; lean_object* v_env_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; 
v_toConstantVal_451_ = lean_ctor_get(v_a_418_, 0);
lean_inc_ref(v_toConstantVal_451_);
lean_dec(v_a_418_);
v_name_452_ = lean_ctor_get(v_toConstantVal_451_, 0);
lean_inc(v_name_452_);
lean_dec_ref(v_toConstantVal_451_);
v_env_453_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_env_453_);
lean_dec(v___x_419_);
v___x_454_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_452_);
v___x_455_ = 0;
lean_inc(v___x_454_);
v___x_456_ = l_Lean_Environment_find_x3f(v_env_453_, v___x_454_, v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_dec(v___x_454_);
v_lemmas_426_ = v_snd_421_;
v___y_427_ = v___y_400_;
v___y_428_ = v___y_401_;
v___y_429_ = v___y_402_;
v___y_430_ = v___y_403_;
v___y_431_ = v___y_404_;
v___y_432_ = v___y_405_;
goto v___jp_425_;
}
else
{
lean_object* v_options_457_; lean_object* v_inheritedTraceOptions_458_; uint8_t v_hasTrace_459_; uint8_t v___x_460_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; 
lean_dec_ref(v___x_456_);
v_options_457_ = lean_ctor_get(v___y_404_, 2);
v_inheritedTraceOptions_458_ = lean_ctor_get(v___y_404_, 13);
v_hasTrace_459_ = lean_ctor_get_uint8(v_options_457_, sizeof(void*)*1);
v___x_460_ = 1;
if (v_hasTrace_459_ == 0)
{
v___y_462_ = v___y_400_;
v___y_463_ = v___y_401_;
v___y_464_ = v___y_402_;
v___y_465_ = v___y_403_;
v___y_466_ = v___y_404_;
v___y_467_ = v___y_405_;
goto v___jp_461_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_482_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__2));
v___x_483_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__5, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__5_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__5);
v___x_484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_458_, v_options_457_, v___x_483_);
if (v___x_484_ == 0)
{
v___y_462_ = v___y_400_;
v___y_463_ = v___y_401_;
v___y_464_ = v___y_402_;
v___y_465_ = v___y_403_;
v___y_466_ = v___y_404_;
v___y_467_ = v___y_405_;
goto v___jp_461_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_485_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__7, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__7_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___closed__7);
lean_inc(v___x_454_);
v___x_486_ = l_Lean_MessageData_ofName(v___x_454_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(v___x_482_, v___x_487_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_dec_ref(v___x_488_);
v___y_462_ = v___y_400_;
v___y_463_ = v___y_401_;
v___y_464_ = v___y_402_;
v___y_465_ = v___y_403_;
v___y_466_ = v___y_404_;
v___y_467_ = v___y_405_;
goto v___jp_461_;
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v___x_454_);
lean_del_object(v___x_423_);
lean_dec(v_snd_421_);
lean_dec(v_fst_420_);
lean_dec(v_numParams_413_);
lean_dec(v_tail_410_);
lean_dec(v_key_409_);
lean_dec_ref(v___x_397_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
v___jp_461_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_inc(v___x_454_);
v___x_468_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_468_, 0, v___x_454_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*1, v___x_460_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*1 + 1, v___x_455_);
v___x_469_ = lean_box(0);
v___x_470_ = l_Lean_mkConst(v___x_454_, v___x_469_);
v___x_471_ = l_Lean_Meta_simpGlobalConfig;
v___x_472_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_snd_421_, v___x_468_, v___x_470_, v___x_471_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_472_);
v_lemmas_426_ = v_a_473_;
v___y_427_ = v___y_462_;
v___y_428_ = v___y_463_;
v___y_429_ = v___y_464_;
v___y_430_ = v___y_465_;
v___y_431_ = v___y_466_;
v___y_432_ = v___y_467_;
goto v___jp_425_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_del_object(v___x_423_);
lean_dec(v_fst_420_);
lean_dec(v_numParams_413_);
lean_dec(v_tail_410_);
lean_dec(v_key_409_);
lean_dec_ref(v___x_397_);
v_a_474_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_472_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_472_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
v___jp_425_:
{
lean_object* v___x_433_; lean_object* v_fieldNames_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_inc(v_key_409_);
lean_inc_ref(v___x_397_);
v___x_433_ = l_Lean_getStructureInfo(v___x_397_, v_key_409_);
v_fieldNames_434_ = lean_ctor_get(v___x_433_, 1);
lean_inc_ref(v_fieldNames_434_);
lean_dec_ref(v___x_433_);
v___x_435_ = lean_array_get_size(v_fieldNames_434_);
lean_dec_ref(v_fieldNames_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(v___x_435_, v_key_409_, v_numParams_413_, v___x_436_, v_fst_420_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref(v___x_437_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_lemmas_426_);
lean_ctor_set(v___x_423_, 0, v_a_438_);
v___x_440_ = v___x_423_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_438_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_lemmas_426_);
v___x_440_ = v_reuseFailAlloc_442_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
v_a_398_ = v_tail_410_;
v_a_399_ = v___x_440_;
goto _start;
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_lemmas_426_);
lean_del_object(v___x_423_);
lean_dec(v_tail_410_);
lean_dec_ref(v___x_397_);
v_a_443_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_437_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_437_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_numParams_413_);
lean_dec(v_tail_410_);
lean_dec(v_key_409_);
lean_dec_ref(v_a_399_);
lean_dec_ref(v___x_397_);
v_a_498_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_417_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_417_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_tail_410_);
lean_dec(v_key_409_);
lean_dec_ref(v_a_399_);
lean_dec_ref(v___x_397_);
v_a_506_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_411_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_411_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4___boxed(lean_object* v___x_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4(v___x_514_, v_a_515_, v_a_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5(lean_object* v___x_525_, lean_object* v_as_526_, size_t v_sz_527_, size_t v_i_528_, lean_object* v_b_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = lean_usize_dec_lt(v_i_528_, v_sz_527_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_dec_ref(v___x_525_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_b_529_);
return v___x_538_;
}
else
{
lean_object* v_a_539_; lean_object* v___x_540_; 
v_a_539_ = lean_array_uget_borrowed(v_as_526_, v_i_528_);
lean_inc(v_a_539_);
lean_inc_ref(v___x_525_);
v___x_540_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__4(v___x_525_, v_a_539_, v_b_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_553_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_553_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_553_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_553_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
if (lean_obj_tag(v_a_541_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; 
lean_dec_ref(v___x_525_);
v_a_545_ = lean_ctor_get(v_a_541_, 0);
lean_inc(v_a_545_);
lean_dec_ref(v_a_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_a_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
else
{
lean_object* v_a_549_; size_t v___x_550_; size_t v___x_551_; 
lean_del_object(v___x_543_);
v_a_549_ = lean_ctor_get(v_a_541_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v_a_541_);
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_add(v_i_528_, v___x_550_);
v_i_528_ = v___x_551_;
v_b_529_ = v_a_549_;
goto _start;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v___x_525_);
v_a_554_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_540_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_540_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5___boxed(lean_object* v___x_562_, lean_object* v_as_563_, lean_object* v_sz_564_, lean_object* v_i_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v_sz_boxed_574_ = lean_unbox_usize(v_sz_564_);
lean_dec(v_sz_564_);
v_i_boxed_575_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5(v___x_562_, v_as_563_, v_sz_boxed_574_, v_i_boxed_575_, v_b_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_as_563_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas(lean_object* v_simprocs_577_, lean_object* v_lemmas_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_typeAnalysis_588_; lean_object* v_interestingStructures_589_; lean_object* v_env_590_; lean_object* v_buckets_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_618_; 
v___x_586_ = lean_st_ref_get(v_a_580_);
v___x_587_ = lean_st_ref_get(v_a_584_);
v_typeAnalysis_588_ = lean_ctor_get(v___x_586_, 2);
lean_inc_ref(v_typeAnalysis_588_);
lean_dec(v___x_586_);
v_interestingStructures_589_ = lean_ctor_get(v_typeAnalysis_588_, 0);
lean_inc_ref(v_interestingStructures_589_);
lean_dec_ref(v_typeAnalysis_588_);
v_env_590_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_587_);
v_buckets_591_ = lean_ctor_get(v_interestingStructures_589_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_interestingStructures_589_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_interestingStructures_589_, 0);
lean_dec(v_unused_619_);
v___x_593_ = v_interestingStructures_589_;
v_isShared_594_ = v_isSharedCheck_618_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_buckets_591_);
lean_dec(v_interestingStructures_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_618_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_lemmas_578_);
lean_ctor_set(v___x_593_, 0, v_simprocs_577_);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_simprocs_577_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_lemmas_578_);
v___x_596_ = v_reuseFailAlloc_617_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
size_t v_sz_597_; size_t v___x_598_; lean_object* v___x_599_; 
v_sz_597_ = lean_array_size(v_buckets_591_);
v___x_598_ = ((size_t)0ULL);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__5(v_env_590_, v_buckets_591_, v_sz_597_, v___x_598_, v___x_596_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec_ref(v_buckets_591_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_616_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_616_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_616_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_616_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_615_; 
v_fst_604_ = lean_ctor_get(v_a_600_, 0);
v_snd_605_ = lean_ctor_get(v_a_600_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_a_600_);
if (v_isSharedCheck_615_ == 0)
{
v___x_607_ = v_a_600_;
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_inc(v_fst_604_);
lean_dec(v_a_600_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_fst_604_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_snd_605_);
v___x_610_ = v_reuseFailAlloc_614_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_610_);
v___x_612_ = v___x_602_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas___boxed(lean_object* v_simprocs_620_, lean_object* v_lemmas_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas(v_simprocs_620_, v_lemmas_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2(lean_object* v_upperBound_630_, lean_object* v_a_631_, lean_object* v___x_632_, lean_object* v_inst_633_, lean_object* v_R_634_, lean_object* v_a_635_, lean_object* v_b_636_, lean_object* v_c_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___redArg(v_upperBound_630_, v_a_631_, v___x_632_, v_a_635_, v_b_636_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2___boxed(lean_object* v_upperBound_646_, lean_object* v_a_647_, lean_object* v___x_648_, lean_object* v_inst_649_, lean_object* v_R_650_, lean_object* v_a_651_, lean_object* v_b_652_, lean_object* v_c_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__2(v_upperBound_646_, v_a_647_, v___x_648_, v_inst_649_, v_R_650_, v_a_651_, v_b_652_, v_c_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v_upperBound_646_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3(lean_object* v_cls_662_, lean_object* v_msg_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___redArg(v_cls_662_, v_msg_663_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3___boxed(lean_object* v_cls_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__3(v_cls_672_, v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0(lean_object* v_00_u03b1_682_, lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_683_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___boxed(lean_object* v_00_u03b1_692_, lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0(v_00_u03b1_692_, v_msg_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_701_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0(void){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_702_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__0);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0(lean_object* v_00_u03b2_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0___closed__1);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(lean_object* v_x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
v___x_715_ = lean_apply_7(v_x_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, lean_box(0));
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed(lean_object* v_x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(lean_object* v_mvarId_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___f_734_; lean_object* v___x_735_; 
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
v___f_734_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_734_, 0, v_x_726_);
lean_closure_set(v___f_734_, 1, v___y_727_);
lean_closure_set(v___f_734_, 2, v___y_728_);
v___x_735_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_725_, v___f_734_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_735_) == 0)
{
return v___x_735_;
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg___boxed(lean_object* v_mvarId_744_, lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_744_, v_x_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1(lean_object* v_00_u03b1_754_, lean_object* v_mvarId_755_, lean_object* v_x_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_755_, v_x_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___boxed(lean_object* v_00_u03b1_765_, lean_object* v_mvarId_766_, lean_object* v_x_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1(v_00_u03b1_765_, v_mvarId_766_, v_x_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_775_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0(void){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_776_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__0);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_unsigned_to_nat(32u);
v___x_780_ = lean_mk_empty_array_with_capacity(v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0(lean_object* v_simprocs_782_, lean_object* v_relevantLemmas_783_, lean_object* v___x_784_, lean_object* v_goal_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas(v_simprocs_782_, v_relevantLemmas_783_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v_fst_795_; lean_object* v_snd_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_891_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref(v___x_793_);
v_fst_795_ = lean_ctor_get(v_a_794_, 0);
v_snd_796_ = lean_ctor_get(v_a_794_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_a_794_);
if (v_isSharedCheck_891_ == 0)
{
v___x_798_ = v_a_794_;
v_isShared_799_ = v_isSharedCheck_891_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_snd_796_);
lean_inc(v_fst_795_);
lean_dec(v_a_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_891_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addDefaultTypeAnalysisLemmas(v_snd_796_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_791_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v_maxSteps_804_; lean_object* v___x_805_; uint8_t v___x_806_; uint8_t v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v___x_802_);
v_maxSteps_804_ = lean_ctor_get(v___y_786_, 1);
v___x_805_ = lean_unsigned_to_nat(2u);
v___x_806_ = 0;
v___x_807_ = 1;
v___x_808_ = 0;
v___x_809_ = lean_box(0);
lean_inc(v_maxSteps_804_);
v___x_810_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_810_, 0, v_maxSteps_804_);
lean_ctor_set(v___x_810_, 1, v___x_805_);
lean_ctor_set(v___x_810_, 2, v___x_809_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 1, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 2, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 3, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 4, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 5, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 6, v___x_808_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 7, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 8, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 9, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 10, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 11, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 12, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 13, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 14, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 15, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 16, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 17, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 18, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 19, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 20, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 21, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 22, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 23, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 24, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 25, v___x_807_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 26, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 27, v___x_806_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3 + 28, v___x_806_);
v___x_811_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_810_, v_a_801_, v_a_803_, v___y_788_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref(v___x_811_);
v___x_813_ = l_Lean_Meta_getPropHyps(v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_813_);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_mk_empty_array_with_capacity(v___x_815_);
v___x_817_ = lean_array_push(v___x_816_, v_fst_795_);
v___x_818_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__1);
lean_inc(v___x_784_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_784_);
lean_ctor_set(v___x_798_, 0, v___x_818_);
v___x_820_ = v___x_798_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_784_);
v___x_820_ = v_reuseFailAlloc_858_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; size_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_821_ = lean_unsigned_to_nat(32u);
v___x_822_ = lean_mk_empty_array_with_capacity(v___x_821_);
v___x_823_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___closed__2);
v___x_824_ = ((size_t)5ULL);
lean_inc(v___x_784_);
v___x_825_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_822_);
lean_ctor_set(v___x_825_, 2, v___x_784_);
lean_ctor_set(v___x_825_, 3, v___x_784_);
lean_ctor_set_usize(v___x_825_, 4, v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_826_, 0, v___x_818_);
lean_ctor_set(v___x_826_, 1, v___x_818_);
lean_ctor_set(v___x_826_, 2, v___x_818_);
lean_ctor_set(v___x_826_, 3, v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_820_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_Meta_simpGoal(v_goal_785_, v_a_812_, v___x_817_, v___x_809_, v___x_807_, v_a_814_, v___x_827_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_849_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_849_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_849_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_849_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_fst_833_; 
v_fst_833_ = lean_ctor_get(v_a_829_, 0);
lean_inc(v_fst_833_);
lean_dec(v_a_829_);
if (lean_obj_tag(v_fst_833_) == 1)
{
lean_object* v_val_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_845_; 
v_val_834_ = lean_ctor_get(v_fst_833_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_fst_833_);
if (v_isSharedCheck_845_ == 0)
{
v___x_836_ = v_fst_833_;
v_isShared_837_ = v_isSharedCheck_845_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_val_834_);
lean_dec(v_fst_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_845_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_snd_838_; lean_object* v___x_840_; 
v_snd_838_ = lean_ctor_get(v_val_834_, 1);
lean_inc(v_snd_838_);
lean_dec(v_val_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_snd_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_snd_838_);
v___x_840_ = v_reuseFailAlloc_844_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_840_);
v___x_842_ = v___x_831_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
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
else
{
lean_object* v___x_847_; 
lean_dec(v_fst_833_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_809_);
v___x_847_ = v___x_831_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_809_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_828_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_828_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_a_812_);
lean_del_object(v___x_798_);
lean_dec(v_fst_795_);
lean_dec(v_goal_785_);
lean_dec(v___x_784_);
v_a_859_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_813_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_813_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_del_object(v___x_798_);
lean_dec(v_fst_795_);
lean_dec(v_goal_785_);
lean_dec(v___x_784_);
v_a_867_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_811_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_811_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
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
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_a_801_);
lean_del_object(v___x_798_);
lean_dec(v_fst_795_);
lean_dec(v_goal_785_);
lean_dec(v___x_784_);
v_a_875_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_802_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_802_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_del_object(v___x_798_);
lean_dec(v_fst_795_);
lean_dec(v_goal_785_);
lean_dec(v___x_784_);
v_a_883_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_800_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_800_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_goal_785_);
lean_dec(v___x_784_);
v_a_892_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_793_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_793_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___boxed(lean_object* v_simprocs_900_, lean_object* v_relevantLemmas_901_, lean_object* v___x_902_, lean_object* v_goal_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0(v_simprocs_900_, v_relevantLemmas_901_, v___x_902_, v_goal_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_911_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1(void){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__0(lean_box(0));
return v___x_913_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_simprocs_916_; 
v___x_914_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__1);
v___x_915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__0);
v_simprocs_916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_simprocs_916_, 0, v___x_915_);
lean_ctor_set(v_simprocs_916_, 1, v___x_915_);
lean_ctor_set(v_simprocs_916_, 2, v___x_914_);
lean_ctor_set(v_simprocs_916_, 3, v___x_914_);
return v_simprocs_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess(lean_object* v_goal_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_simprocs_927_; lean_object* v___x_928_; lean_object* v_relevantLemmas_929_; lean_object* v___f_930_; lean_object* v___x_931_; 
v_simprocs_927_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__2);
v___x_928_ = lean_unsigned_to_nat(0u);
v_relevantLemmas_929_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___closed__3));
lean_inc(v_goal_919_);
v___f_930_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___lam__0___boxed), 11, 4);
lean_closure_set(v___f_930_, 0, v_simprocs_927_);
lean_closure_set(v___f_930_, 1, v_relevantLemmas_929_);
lean_closure_set(v___f_930_, 2, v___x_928_);
lean_closure_set(v___f_930_, 3, v_goal_919_);
v___x_931_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess_spec__1___redArg(v_goal_919_, v___f_930_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess___boxed(lean_object* v_goal_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess(v_goal_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(lean_object* v_e_941_, lean_object* v___y_942_){
_start:
{
uint8_t v___x_944_; 
v___x_944_ = l_Lean_Expr_hasMVar(v_e_941_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v_e_941_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; lean_object* v_mctx_947_; lean_object* v___x_948_; lean_object* v_fst_949_; lean_object* v_snd_950_; lean_object* v___x_951_; lean_object* v_cache_952_; lean_object* v_zetaDeltaFVarIds_953_; lean_object* v_postponed_954_; lean_object* v_diag_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_964_; 
v___x_946_ = lean_st_ref_get(v___y_942_);
v_mctx_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc_ref(v_mctx_947_);
lean_dec(v___x_946_);
v___x_948_ = l_Lean_instantiateMVarsCore(v_mctx_947_, v_e_941_);
v_fst_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_fst_949_);
v_snd_950_ = lean_ctor_get(v___x_948_, 1);
lean_inc(v_snd_950_);
lean_dec_ref(v___x_948_);
v___x_951_ = lean_st_ref_take(v___y_942_);
v_cache_952_ = lean_ctor_get(v___x_951_, 1);
v_zetaDeltaFVarIds_953_ = lean_ctor_get(v___x_951_, 2);
v_postponed_954_ = lean_ctor_get(v___x_951_, 3);
v_diag_955_ = lean_ctor_get(v___x_951_, 4);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___x_951_, 0);
lean_dec(v_unused_965_);
v___x_957_ = v___x_951_;
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_diag_955_);
lean_inc(v_postponed_954_);
lean_inc(v_zetaDeltaFVarIds_953_);
lean_inc(v_cache_952_);
lean_dec(v___x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v_snd_950_);
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_snd_950_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_cache_952_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_zetaDeltaFVarIds_953_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_postponed_954_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v_diag_955_);
v___x_960_ = v_reuseFailAlloc_963_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_st_ref_set(v___y_942_, v___x_960_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_fst_949_);
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg___boxed(lean_object* v_e_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(v_e_966_, v___y_967_);
lean_dec(v___y_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0(lean_object* v_e_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(v_e_970_, v___y_972_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___boxed(lean_object* v_e_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0(v_e_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_983_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(lean_object* v_a_984_, lean_object* v_x_985_){
_start:
{
if (lean_obj_tag(v_x_985_) == 0)
{
uint8_t v___x_986_; 
v___x_986_ = 0;
return v___x_986_;
}
else
{
lean_object* v_key_987_; lean_object* v_tail_988_; uint8_t v___x_989_; 
v_key_987_ = lean_ctor_get(v_x_985_, 0);
v_tail_988_ = lean_ctor_get(v_x_985_, 2);
v___x_989_ = lean_name_eq(v_key_987_, v_a_984_);
if (v___x_989_ == 0)
{
v_x_985_ = v_tail_988_;
goto _start;
}
else
{
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg___boxed(lean_object* v_a_991_, lean_object* v_x_992_){
_start:
{
uint8_t v_res_993_; lean_object* v_r_994_; 
v_res_993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_991_, v_x_992_);
lean_dec(v_x_992_);
lean_dec(v_a_991_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_995_; uint64_t v___x_996_; 
v___x_995_ = lean_unsigned_to_nat(1723u);
v___x_996_ = lean_uint64_of_nat(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(lean_object* v_m_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_buckets_999_; lean_object* v___x_1000_; uint64_t v___y_1002_; 
v_buckets_999_ = lean_ctor_get(v_m_997_, 1);
v___x_1000_ = lean_array_get_size(v_buckets_999_);
if (lean_obj_tag(v_a_998_) == 0)
{
uint64_t v___x_1016_; 
v___x_1016_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___closed__0);
v___y_1002_ = v___x_1016_;
goto v___jp_1001_;
}
else
{
uint64_t v_hash_1017_; 
v_hash_1017_ = lean_ctor_get_uint64(v_a_998_, sizeof(void*)*2);
v___y_1002_ = v_hash_1017_;
goto v___jp_1001_;
}
v___jp_1001_:
{
uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v_fold_1005_; uint64_t v___x_1006_; uint64_t v___x_1007_; uint64_t v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1003_ = 32ULL;
v___x_1004_ = lean_uint64_shift_right(v___y_1002_, v___x_1003_);
v_fold_1005_ = lean_uint64_xor(v___y_1002_, v___x_1004_);
v___x_1006_ = 16ULL;
v___x_1007_ = lean_uint64_shift_right(v_fold_1005_, v___x_1006_);
v___x_1008_ = lean_uint64_xor(v_fold_1005_, v___x_1007_);
v___x_1009_ = lean_uint64_to_usize(v___x_1008_);
v___x_1010_ = lean_usize_of_nat(v___x_1000_);
v___x_1011_ = ((size_t)1ULL);
v___x_1012_ = lean_usize_sub(v___x_1010_, v___x_1011_);
v___x_1013_ = lean_usize_land(v___x_1009_, v___x_1012_);
v___x_1014_ = lean_array_uget_borrowed(v_buckets_999_, v___x_1013_);
v___x_1015_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_998_, v___x_1014_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg___boxed(lean_object* v_m_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(v_m_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_m_1018_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0(uint8_t v___x_1022_, lean_object* v_interestingStructures_1023_, lean_object* v_decl_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = l_Lean_LocalDecl_isLet(v_decl_1024_, v___x_1022_);
if (v___x_1030_ == 0)
{
uint8_t v___x_1031_; 
v___x_1031_ = l_Lean_LocalDecl_isImplementationDetail(v_decl_1024_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1050_; 
v___x_1032_ = l_Lean_LocalDecl_type(v_decl_1024_);
v___x_1033_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__0___redArg(v___x_1032_, v___y_1026_);
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1050_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1050_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = l_Lean_Expr_getAppFn(v_a_1034_);
lean_dec(v_a_1034_);
v___x_1039_ = l_Lean_Expr_constName_x3f(v___x_1038_);
lean_dec_ref(v___x_1038_);
if (lean_obj_tag(v___x_1039_) == 1)
{
lean_object* v_val_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v_val_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_val_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(v_interestingStructures_1023_, v_val_1040_);
lean_dec(v_val_1040_);
v___x_1042_ = lean_box(v___x_1041_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1042_);
v___x_1044_ = v___x_1036_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec(v___x_1039_);
v___x_1046_ = lean_box(v___x_1022_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1046_);
v___x_1048_ = v___x_1036_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_box(v___x_1022_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_box(v___x_1022_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0___boxed(lean_object* v___x_1055_, lean_object* v_interestingStructures_1056_, lean_object* v_decl_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v___x_3219__boxed_1063_; lean_object* v_res_1064_; 
v___x_3219__boxed_1063_ = lean_unbox(v___x_1055_);
v_res_1064_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0(v___x_3219__boxed_1063_, v_interestingStructures_1056_, v_decl_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v_decl_1057_);
lean_dec_ref(v_interestingStructures_1056_);
return v_res_1064_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__0));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1(lean_object* v_goal_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; lean_object* v_typeAnalysis_1077_; lean_object* v_interestingStructures_1078_; lean_object* v_size_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1076_ = lean_st_ref_get(v___y_1070_);
v_typeAnalysis_1077_ = lean_ctor_get(v___x_1076_, 2);
lean_inc_ref(v_typeAnalysis_1077_);
lean_dec(v___x_1076_);
v_interestingStructures_1078_ = lean_ctor_get(v_typeAnalysis_1077_, 0);
lean_inc_ref(v_interestingStructures_1078_);
lean_dec_ref(v_typeAnalysis_1077_);
v_size_1079_ = lean_ctor_get(v_interestingStructures_1078_, 0);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_nat_dec_eq(v_size_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(v___x_1081_);
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1083_, 0, v___x_1082_);
lean_closure_set(v___f_1083_, 1, v_interestingStructures_1078_);
v___x_1084_ = l_Lean_MVarId_casesRec(v_goal_1068_, v___f_1083_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_tail_1093_; 
v_tail_1093_ = lean_ctor_get(v_a_1085_, 1);
if (lean_obj_tag(v_tail_1093_) == 0)
{
lean_object* v_head_1094_; lean_object* v___x_1095_; 
v_head_1094_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_head_1094_);
lean_dec_ref(v_a_1085_);
v___x_1095_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Structures_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_postprocess(v_head_1094_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
return v___x_1095_;
}
else
{
lean_dec_ref(v_a_1085_);
v___y_1087_ = v___y_1071_;
v___y_1088_ = v___y_1072_;
v___y_1089_ = v___y_1073_;
v___y_1090_ = v___y_1074_;
goto v___jp_1086_;
}
}
else
{
lean_dec(v_a_1085_);
v___y_1087_ = v___y_1071_;
v___y_1088_ = v___y_1072_;
v___y_1089_ = v___y_1073_;
v___y_1090_ = v___y_1074_;
goto v___jp_1086_;
}
v___jp_1086_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___closed__1);
v___x_1092_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_1091_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1092_;
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_a_1096_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1084_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1084_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref(v_interestingStructures_1078_);
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_goal_1068_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1___boxed(lean_object* v_goal_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass___lam__1(v_goal_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1114_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1(lean_object* v_00_u03b2_1123_, lean_object* v_m_1124_, lean_object* v_a_1125_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___redArg(v_m_1124_, v_a_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1___boxed(lean_object* v_00_u03b2_1127_, lean_object* v_m_1128_, lean_object* v_a_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1(v_00_u03b2_1127_, v_m_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_m_1128_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1(lean_object* v_00_u03b2_1132_, lean_object* v_a_1133_, lean_object* v_x_1134_){
_start:
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_1133_, v_x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1136_, lean_object* v_a_1137_, lean_object* v_x_1138_){
_start:
{
uint8_t v_res_1139_; lean_object* v_r_1140_; 
v_res_1139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_structuresPass_spec__1_spec__1(v_00_u03b2_1136_, v_a_1137_, v_x_1138_);
lean_dec(v_x_1138_);
lean_dec(v_a_1137_);
v_r_1140_ = lean_box(v_res_1139_);
return v_r_1140_;
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
