// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Structures
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow import Lean.Meta.Injective import Lean.Meta.Tactic.Cases
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
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
lean_object* l_Lean_MVarId_casesRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_Lean_getStructureInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addDefaultTypeAnalysisLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "applyIteSimproc"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_3),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 54, 65, 115, 92, 106, 117, 217)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_4),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(84, 239, 46, 245, 153, 49, 212, 168)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "applyCondSimproc"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_3),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 54, 65, 115, 92, 106, 117, 217)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_4),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(223, 15, 140, 191, 132, 164, 133, 159)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__0_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value_aux_1),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__2_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__3 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__3_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Using injEq lemma: "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__5 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__5_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "structures preprocessor generated more than 1 goal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structures"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 214, 82, 86, 36, 11, 245, 232)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2(lean_object* v_msg_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_toApplicative_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_79_; 
v___x_14_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0);
v___x_15_ = l_StateRefT_x27_instMonad___redArg(v___x_14_);
v_toApplicative_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v___x_15_, 1);
lean_dec(v_unused_80_);
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_79_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_toApplicative_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_79_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v_toFunctor_20_; lean_object* v_toSeq_21_; lean_object* v_toSeqLeft_22_; lean_object* v_toSeqRight_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_77_; 
v_toFunctor_20_ = lean_ctor_get(v_toApplicative_16_, 0);
v_toSeq_21_ = lean_ctor_get(v_toApplicative_16_, 2);
v_toSeqLeft_22_ = lean_ctor_get(v_toApplicative_16_, 3);
v_toSeqRight_23_ = lean_ctor_get(v_toApplicative_16_, 4);
v_isSharedCheck_77_ = !lean_is_exclusive(v_toApplicative_16_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; 
v_unused_78_ = lean_ctor_get(v_toApplicative_16_, 1);
lean_dec(v_unused_78_);
v___x_25_ = v_toApplicative_16_;
v_isShared_26_ = v_isSharedCheck_77_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_toSeqRight_23_);
lean_inc(v_toSeqLeft_22_);
lean_inc(v_toSeq_21_);
lean_inc(v_toFunctor_20_);
lean_dec(v_toApplicative_16_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_77_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_36_; 
v___f_27_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1));
v___f_28_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_20_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_29_, 0, v_toFunctor_20_);
v___f_30_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_30_, 0, v_toFunctor_20_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___f_29_);
lean_ctor_set(v___x_31_, 1, v___f_30_);
v___f_32_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_32_, 0, v_toSeqRight_23_);
v___f_33_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_33_, 0, v_toSeqLeft_22_);
v___f_34_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_34_, 0, v_toSeq_21_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 4, v___f_32_);
lean_ctor_set(v___x_25_, 3, v___f_33_);
lean_ctor_set(v___x_25_, 2, v___f_34_);
lean_ctor_set(v___x_25_, 1, v___f_27_);
lean_ctor_set(v___x_25_, 0, v___x_31_);
v___x_36_ = v___x_25_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___f_27_);
lean_ctor_set(v_reuseFailAlloc_76_, 2, v___f_34_);
lean_ctor_set(v_reuseFailAlloc_76_, 3, v___f_33_);
lean_ctor_set(v_reuseFailAlloc_76_, 4, v___f_32_);
v___x_36_ = v_reuseFailAlloc_76_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_38_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v___f_28_);
lean_ctor_set(v___x_18_, 0, v___x_36_);
v___x_38_ = v___x_18_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___f_28_);
v___x_38_ = v_reuseFailAlloc_75_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v_toApplicative_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_73_; 
v___x_39_ = l_StateRefT_x27_instMonad___redArg(v___x_38_);
v_toApplicative_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; 
v_unused_74_ = lean_ctor_get(v___x_39_, 1);
lean_dec(v_unused_74_);
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_73_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_toApplicative_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_73_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_toFunctor_44_; lean_object* v_toSeq_45_; lean_object* v_toSeqLeft_46_; lean_object* v_toSeqRight_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_71_; 
v_toFunctor_44_ = lean_ctor_get(v_toApplicative_40_, 0);
v_toSeq_45_ = lean_ctor_get(v_toApplicative_40_, 2);
v_toSeqLeft_46_ = lean_ctor_get(v_toApplicative_40_, 3);
v_toSeqRight_47_ = lean_ctor_get(v_toApplicative_40_, 4);
v_isSharedCheck_71_ = !lean_is_exclusive(v_toApplicative_40_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v_toApplicative_40_, 1);
lean_dec(v_unused_72_);
v___x_49_ = v_toApplicative_40_;
v_isShared_50_ = v_isSharedCheck_71_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_toSeqRight_47_);
lean_inc(v_toSeqLeft_46_);
lean_inc(v_toSeq_45_);
lean_inc(v_toFunctor_44_);
lean_dec(v_toApplicative_40_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_71_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_60_; 
v___f_51_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3));
v___f_52_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_44_);
v___f_53_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_53_, 0, v_toFunctor_44_);
v___f_54_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_54_, 0, v_toFunctor_44_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___f_53_);
lean_ctor_set(v___x_55_, 1, v___f_54_);
v___f_56_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_56_, 0, v_toSeqRight_47_);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_57_, 0, v_toSeqLeft_46_);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_58_, 0, v_toSeq_45_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 4, v___f_56_);
lean_ctor_set(v___x_49_, 3, v___f_57_);
lean_ctor_set(v___x_49_, 2, v___f_58_);
lean_ctor_set(v___x_49_, 1, v___f_51_);
lean_ctor_set(v___x_49_, 0, v___x_55_);
v___x_60_ = v___x_49_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v___f_51_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v___f_58_);
lean_ctor_set(v_reuseFailAlloc_70_, 3, v___f_57_);
lean_ctor_set(v_reuseFailAlloc_70_, 4, v___f_56_);
v___x_60_ = v_reuseFailAlloc_70_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_62_; 
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___f_52_);
lean_ctor_set(v___x_42_, 0, v___x_60_);
v___x_62_ = v___x_42_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___f_52_);
v___x_62_ = v_reuseFailAlloc_69_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_19962__overap_67_; lean_object* v___x_68_; 
v___x_63_ = l_StateRefT_x27_instMonad___redArg(v___x_62_);
v___x_64_ = l_ReaderT_instMonad___redArg(v___x_63_);
v___x_65_ = lean_box(0);
v___x_66_ = l_instInhabitedOfMonad___redArg(v___x_64_, v___x_65_);
v___x_19962__overap_67_ = lean_panic_fn_borrowed(v___x_66_, v_msg_6_);
lean_dec(v___x_66_);
lean_inc(v___y_12_);
lean_inc_ref(v___y_11_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
v___x_68_ = lean_apply_7(v___x_19962__overap_67_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_68_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___boxed(lean_object* v_msg_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2(v_msg_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(lean_object* v_msgData_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_env_97_; lean_object* v___x_98_; lean_object* v_mctx_99_; lean_object* v_lctx_100_; lean_object* v_options_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_96_ = lean_st_ref_get(v___y_94_);
v_env_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_env_97_);
lean_dec(v___x_96_);
v___x_98_ = lean_st_ref_get(v___y_92_);
v_mctx_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc_ref(v_mctx_99_);
lean_dec(v___x_98_);
v_lctx_100_ = lean_ctor_get(v___y_91_, 2);
v_options_101_ = lean_ctor_get(v___y_93_, 2);
lean_inc_ref(v_options_101_);
lean_inc_ref(v_lctx_100_);
v___x_102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_102_, 0, v_env_97_);
lean_ctor_set(v___x_102_, 1, v_mctx_99_);
lean_ctor_set(v___x_102_, 2, v_lctx_100_);
lean_ctor_set(v___x_102_, 3, v_options_101_);
v___x_103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_msgData_90_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5___boxed(lean_object* v_msgData_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msgData_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(lean_object* v_msg_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_ref_118_; lean_object* v___x_119_; lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_128_; 
v_ref_118_ = lean_ctor_get(v___y_115_, 5);
v___x_119_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msg_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_128_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
lean_inc(v_ref_118_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v_ref_118_);
lean_ctor_set(v___x_124_, 1, v_a_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 1);
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg___boxed(lean_object* v_msg_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_135_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__0));
v___x_138_ = l_Lean_stringToMessageData(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__2));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_145_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__6));
v___x_146_ = lean_unsigned_to_nat(11u);
v___x_147_ = lean_unsigned_to_nat(122u);
v___x_148_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__5));
v___x_149_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__4));
v___x_150_ = l_mkPanicMessageWithDecl(v___x_149_, v___x_148_, v___x_147_, v___x_146_, v___x_145_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(lean_object* v_constName_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_167_; lean_object* v_env_168_; uint8_t v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_st_ref_get(v___y_157_);
v_env_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc_ref(v_env_168_);
lean_dec(v___x_167_);
v___x_169_ = 0;
lean_inc(v_constName_151_);
v___x_170_ = l_Lean_Environment_findAsync_x3f(v_env_168_, v_constName_151_, v___x_169_);
if (lean_obj_tag(v___x_170_) == 1)
{
lean_object* v_val_171_; uint8_t v_kind_172_; 
v_val_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_171_);
lean_dec_ref_known(v___x_170_, 1);
v_kind_172_ = lean_ctor_get_uint8(v_val_171_, sizeof(void*)*3);
if (v_kind_172_ == 6)
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_171_);
if (lean_obj_tag(v___x_173_) == 6)
{
lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_constName_151_);
v_val_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 0);
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_val_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec_ref(v___x_173_);
v___x_182_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7);
v___x_183_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2(v___x_182_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_192_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_192_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
if (lean_obj_tag(v_a_184_) == 0)
{
lean_del_object(v___x_186_);
goto v___jp_159_;
}
else
{
lean_object* v_val_188_; lean_object* v___x_190_; 
lean_dec(v_constName_151_);
v_val_188_ = lean_ctor_get(v_a_184_, 0);
lean_inc(v_val_188_);
lean_dec_ref_known(v_a_184_, 1);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v_val_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_val_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec(v_constName_151_);
v_a_193_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_183_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_183_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
lean_dec(v_val_171_);
goto v___jp_159_;
}
}
else
{
lean_dec(v___x_170_);
goto v___jp_159_;
}
v___jp_159_:
{
lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_160_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1);
v___x_161_ = 0;
v___x_162_ = l_Lean_MessageData_ofConstName(v_constName_151_, v___x_161_);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_160_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3);
v___x_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_165_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___boxed(lean_object* v_constName_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(v_constName_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_209_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(lean_object* v_constName_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; lean_object* v_env_222_; lean_object* v___x_223_; 
v___x_221_ = lean_st_ref_get(v___y_219_);
v_env_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_ref(v_env_222_);
lean_dec(v___x_221_);
lean_inc(v_constName_213_);
v___x_223_ = l_Lean_isInductiveCore_x3f(v_env_222_, v_constName_213_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_224_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1);
v___x_225_ = 0;
v___x_226_ = l_Lean_MessageData_ofConstName(v_constName_213_, v___x_225_);
v___x_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_224_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_229_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec(v_constName_213_);
v_val_231_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_223_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_val_231_);
lean_dec(v___x_223_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 0);
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_val_231_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___boxed(lean_object* v_constName_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(v_constName_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_247_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_248_; double v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_float_of_nat(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(lean_object* v_cls_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_ref_260_; lean_object* v___x_261_; lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_306_; 
v_ref_260_ = lean_ctor_get(v___y_257_, 5);
v___x_261_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
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
v___x_285_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0);
v___x_286_ = 0;
v___x_287_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1));
v___x_288_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_288_, 0, v_cls_253_);
lean_ctor_set(v___x_288_, 1, v___x_284_);
lean_ctor_set(v___x_288_, 2, v___x_287_);
lean_ctor_set_float(v___x_288_, sizeof(void*)*3, v___x_285_);
lean_ctor_set_float(v___x_288_, sizeof(void*)*3 + 8, v___x_285_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*3 + 16, v___x_286_);
v___x_289_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2));
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___boxed(lean_object* v_cls_307_, lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(v_cls_307_, v_msg_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(lean_object* v_upperBound_348_, lean_object* v_a_349_, lean_object* v___x_350_, lean_object* v_a_351_, lean_object* v_b_352_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = lean_nat_dec_lt(v_a_351_, v_upperBound_348_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec(v_a_351_);
lean_dec(v___x_350_);
lean_dec(v_a_349_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v_b_352_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_356_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1));
v___x_357_ = lean_unsigned_to_nat(5u);
lean_inc_n(v_a_351_, 2);
lean_inc_n(v___x_350_, 2);
lean_inc_n(v_a_349_, 2);
v___x_358_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(v_a_349_, v___x_350_, v_a_351_, v___x_356_, v___x_357_);
v___x_359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8));
v___x_360_ = 0;
v___x_361_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10));
v___x_362_ = l_Lean_Meta_Simp_Simprocs_addCore(v_b_352_, v___x_358_, v___x_359_, v___x_360_, v___x_361_);
v___x_363_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12));
v___x_364_ = lean_unsigned_to_nat(4u);
v___x_365_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(v_a_349_, v___x_350_, v_a_351_, v___x_363_, v___x_364_);
v___x_366_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14));
v___x_367_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16));
v___x_368_ = l_Lean_Meta_Simp_Simprocs_addCore(v___x_362_, v___x_365_, v___x_366_, v___x_360_, v___x_367_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_a_351_, v___x_369_);
lean_dec(v_a_351_);
v_a_351_ = v___x_370_;
v_b_352_ = v___x_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___boxed(lean_object* v_upperBound_372_, lean_object* v_a_373_, lean_object* v___x_374_, lean_object* v_a_375_, lean_object* v_b_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v_upperBound_372_, v_a_373_, v___x_374_, v_a_375_, v_b_376_);
lean_dec(v_upperBound_372_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1));
v___x_388_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__3));
v___x_389_ = l_Lean_Name_append(v___x_388_, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__5));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(lean_object* v___x_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
if (lean_obj_tag(v_a_394_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref(v___x_393_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v_a_395_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v_key_405_; lean_object* v_tail_406_; lean_object* v___x_407_; 
v_key_405_ = lean_ctor_get(v_a_394_, 0);
lean_inc_n(v_key_405_, 2);
v_tail_406_ = lean_ctor_get(v_a_394_, 2);
lean_inc(v_tail_406_);
lean_dec_ref_known(v_a_394_, 3);
v___x_407_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(v_key_405_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v_numParams_409_; lean_object* v_ctors_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v_numParams_409_ = lean_ctor_get(v_a_408_, 1);
lean_inc(v_numParams_409_);
v_ctors_410_ = lean_ctor_get(v_a_408_, 4);
lean_inc(v_ctors_410_);
lean_dec(v_a_408_);
v___x_411_ = lean_box(0);
v___x_412_ = l_List_head_x21___redArg(v___x_411_, v_ctors_410_);
lean_dec(v_ctors_410_);
v___x_413_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(v___x_412_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_493_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = lean_st_ref_get(v___y_401_);
v_fst_416_ = lean_ctor_get(v_a_395_, 0);
v_snd_417_ = lean_ctor_get(v_a_395_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_493_ == 0)
{
v___x_419_ = v_a_395_;
v_isShared_420_ = v_isSharedCheck_493_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snd_417_);
lean_inc(v_fst_416_);
lean_dec(v_a_395_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_493_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_lemmas_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v_toConstantVal_447_; lean_object* v_name_448_; lean_object* v_env_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; 
v_toConstantVal_447_ = lean_ctor_get(v_a_414_, 0);
lean_inc_ref(v_toConstantVal_447_);
lean_dec(v_a_414_);
v_name_448_ = lean_ctor_get(v_toConstantVal_447_, 0);
lean_inc(v_name_448_);
lean_dec_ref(v_toConstantVal_447_);
v_env_449_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_env_449_);
lean_dec(v___x_415_);
v___x_450_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_448_);
v___x_451_ = 0;
lean_inc(v___x_450_);
v___x_452_ = l_Lean_Environment_find_x3f(v_env_449_, v___x_450_, v___x_451_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_dec(v___x_450_);
v_lemmas_422_ = v_snd_417_;
v___y_423_ = v___y_396_;
v___y_424_ = v___y_397_;
v___y_425_ = v___y_398_;
v___y_426_ = v___y_399_;
v___y_427_ = v___y_400_;
v___y_428_ = v___y_401_;
goto v___jp_421_;
}
else
{
lean_object* v_options_453_; lean_object* v_inheritedTraceOptions_454_; uint8_t v_hasTrace_455_; uint8_t v___x_456_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; 
lean_dec_ref_known(v___x_452_, 1);
v_options_453_ = lean_ctor_get(v___y_400_, 2);
v_inheritedTraceOptions_454_ = lean_ctor_get(v___y_400_, 13);
v_hasTrace_455_ = lean_ctor_get_uint8(v_options_453_, sizeof(void*)*1);
v___x_456_ = 1;
if (v_hasTrace_455_ == 0)
{
v___y_458_ = v___y_396_;
v___y_459_ = v___y_397_;
v___y_460_ = v___y_398_;
v___y_461_ = v___y_399_;
v___y_462_ = v___y_400_;
v___y_463_ = v___y_401_;
goto v___jp_457_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_478_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1));
v___x_479_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4);
v___x_480_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_454_, v_options_453_, v___x_479_);
if (v___x_480_ == 0)
{
v___y_458_ = v___y_396_;
v___y_459_ = v___y_397_;
v___y_460_ = v___y_398_;
v___y_461_ = v___y_399_;
v___y_462_ = v___y_400_;
v___y_463_ = v___y_401_;
goto v___jp_457_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6);
lean_inc(v___x_450_);
v___x_482_ = l_Lean_MessageData_ofName(v___x_450_);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(v___x_478_, v___x_483_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_dec_ref_known(v___x_484_, 1);
v___y_458_ = v___y_396_;
v___y_459_ = v___y_397_;
v___y_460_ = v___y_398_;
v___y_461_ = v___y_399_;
v___y_462_ = v___y_400_;
v___y_463_ = v___y_401_;
goto v___jp_457_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v___x_450_);
lean_del_object(v___x_419_);
lean_dec(v_snd_417_);
lean_dec(v_fst_416_);
lean_dec(v_numParams_409_);
lean_dec(v_tail_406_);
lean_dec(v_key_405_);
lean_dec_ref(v___x_393_);
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
v___jp_457_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc(v___x_450_);
v___x_464_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_464_, 0, v___x_450_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*1, v___x_456_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*1 + 1, v___x_451_);
v___x_465_ = lean_box(0);
v___x_466_ = l_Lean_mkConst(v___x_450_, v___x_465_);
v___x_467_ = l_Lean_Meta_simpGlobalConfig;
v___x_468_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_snd_417_, v___x_464_, v___x_466_, v___x_467_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v_lemmas_422_ = v_a_469_;
v___y_423_ = v___y_458_;
v___y_424_ = v___y_459_;
v___y_425_ = v___y_460_;
v___y_426_ = v___y_461_;
v___y_427_ = v___y_462_;
v___y_428_ = v___y_463_;
goto v___jp_421_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_del_object(v___x_419_);
lean_dec(v_fst_416_);
lean_dec(v_numParams_409_);
lean_dec(v_tail_406_);
lean_dec(v_key_405_);
lean_dec_ref(v___x_393_);
v_a_470_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_468_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
v___jp_421_:
{
lean_object* v___x_429_; lean_object* v_fieldNames_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_inc(v_key_405_);
lean_inc_ref(v___x_393_);
v___x_429_ = l_Lean_getStructureInfo(v___x_393_, v_key_405_);
v_fieldNames_430_ = lean_ctor_get(v___x_429_, 1);
lean_inc_ref(v_fieldNames_430_);
lean_dec_ref(v___x_429_);
v___x_431_ = lean_array_get_size(v_fieldNames_430_);
lean_dec_ref(v_fieldNames_430_);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v___x_431_, v_key_405_, v_numParams_409_, v___x_432_, v_fst_416_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v_lemmas_422_);
lean_ctor_set(v___x_419_, 0, v_a_434_);
v___x_436_ = v___x_419_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_434_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_lemmas_422_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
v_a_394_ = v_tail_406_;
v_a_395_ = v___x_436_;
goto _start;
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v_lemmas_422_);
lean_del_object(v___x_419_);
lean_dec(v_tail_406_);
lean_dec_ref(v___x_393_);
v_a_439_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_433_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_433_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_numParams_409_);
lean_dec(v_tail_406_);
lean_dec(v_key_405_);
lean_dec_ref(v_a_395_);
lean_dec_ref(v___x_393_);
v_a_494_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_413_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_413_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_tail_406_);
lean_dec(v_key_405_);
lean_dec_ref(v_a_395_);
lean_dec_ref(v___x_393_);
v_a_502_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_407_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_407_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___boxed(lean_object* v___x_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(v___x_510_, v_a_511_, v_a_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5(lean_object* v___x_521_, lean_object* v_as_522_, size_t v_sz_523_, size_t v_i_524_, lean_object* v_b_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = lean_usize_dec_lt(v_i_524_, v_sz_523_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec_ref(v___x_521_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v_b_525_);
return v___x_534_;
}
else
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_array_uget_borrowed(v_as_522_, v_i_524_);
lean_inc(v_a_535_);
lean_inc_ref(v___x_521_);
v___x_536_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(v___x_521_, v_a_535_, v_b_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_549_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_549_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_549_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_549_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
if (lean_obj_tag(v_a_537_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; 
lean_dec_ref(v___x_521_);
v_a_541_ = lean_ctor_get(v_a_537_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v_a_537_, 1);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v_a_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
lean_object* v_a_545_; size_t v___x_546_; size_t v___x_547_; 
lean_del_object(v___x_539_);
v_a_545_ = lean_ctor_get(v_a_537_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v_a_537_, 1);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_524_, v___x_546_);
v_i_524_ = v___x_547_;
v_b_525_ = v_a_545_;
goto _start;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v___x_521_);
v_a_550_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_536_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_536_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5___boxed(lean_object* v___x_558_, lean_object* v_as_559_, lean_object* v_sz_560_, lean_object* v_i_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
size_t v_sz_boxed_570_; size_t v_i_boxed_571_; lean_object* v_res_572_; 
v_sz_boxed_570_ = lean_unbox_usize(v_sz_560_);
lean_dec(v_sz_560_);
v_i_boxed_571_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5(v___x_558_, v_as_559_, v_sz_boxed_570_, v_i_boxed_571_, v_b_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v_as_559_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(lean_object* v_simprocs_573_, lean_object* v_lemmas_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_typeAnalysis_584_; lean_object* v_interestingStructures_585_; lean_object* v_env_586_; lean_object* v_buckets_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_614_; 
v___x_582_ = lean_st_ref_get(v_a_576_);
v___x_583_ = lean_st_ref_get(v_a_580_);
v_typeAnalysis_584_ = lean_ctor_get(v___x_582_, 2);
lean_inc_ref(v_typeAnalysis_584_);
lean_dec(v___x_582_);
v_interestingStructures_585_ = lean_ctor_get(v_typeAnalysis_584_, 0);
lean_inc_ref(v_interestingStructures_585_);
lean_dec_ref(v_typeAnalysis_584_);
v_env_586_ = lean_ctor_get(v___x_583_, 0);
lean_inc_ref(v_env_586_);
lean_dec(v___x_583_);
v_buckets_587_ = lean_ctor_get(v_interestingStructures_585_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_interestingStructures_585_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_interestingStructures_585_, 0);
lean_dec(v_unused_615_);
v___x_589_ = v_interestingStructures_585_;
v_isShared_590_ = v_isSharedCheck_614_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_buckets_587_);
lean_dec(v_interestingStructures_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_614_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v_lemmas_574_);
lean_ctor_set(v___x_589_, 0, v_simprocs_573_);
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_simprocs_573_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_lemmas_574_);
v___x_592_ = v_reuseFailAlloc_613_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
size_t v_sz_593_; size_t v___x_594_; lean_object* v___x_595_; 
v_sz_593_ = lean_array_size(v_buckets_587_);
v___x_594_ = ((size_t)0ULL);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5(v_env_586_, v_buckets_587_, v_sz_593_, v___x_594_, v___x_592_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec_ref(v_buckets_587_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_612_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_612_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_612_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_612_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
v_fst_600_ = lean_ctor_get(v_a_596_, 0);
v_snd_601_ = lean_ctor_get(v_a_596_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_611_ == 0)
{
v___x_603_ = v_a_596_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_snd_601_);
lean_inc(v_fst_600_);
lean_dec(v_a_596_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_fst_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_snd_601_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_606_);
v___x_608_ = v___x_598_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
else
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas___boxed(lean_object* v_simprocs_616_, lean_object* v_lemmas_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(v_simprocs_616_, v_lemmas_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2(lean_object* v_upperBound_626_, lean_object* v_a_627_, lean_object* v___x_628_, lean_object* v_inst_629_, lean_object* v_R_630_, lean_object* v_a_631_, lean_object* v_b_632_, lean_object* v_c_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v_upperBound_626_, v_a_627_, v___x_628_, v_a_631_, v_b_632_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___boxed(lean_object* v_upperBound_642_, lean_object* v_a_643_, lean_object* v___x_644_, lean_object* v_inst_645_, lean_object* v_R_646_, lean_object* v_a_647_, lean_object* v_b_648_, lean_object* v_c_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2(v_upperBound_642_, v_a_643_, v___x_644_, v_inst_645_, v_R_646_, v_a_647_, v_b_648_, v_c_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v_upperBound_642_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(lean_object* v_cls_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(v_cls_658_, v_msg_659_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___boxed(lean_object* v_cls_668_, lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(v_cls_668_, v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0(lean_object* v_00_u03b1_678_, lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_679_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___boxed(lean_object* v_00_u03b1_688_, lean_object* v_msg_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0(v_00_u03b1_688_, v_msg_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_697_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0(void){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_698_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0(lean_object* v_00_u03b2_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
v___x_711_ = lean_apply_7(v_x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, lean_box(0));
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed(lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(lean_object* v_mvarId_721_, lean_object* v_x_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___f_730_; lean_object* v___x_731_; 
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_730_, 0, v_x_722_);
lean_closure_set(v___f_730_, 1, v___y_723_);
lean_closure_set(v___f_730_, 2, v___y_724_);
v___x_731_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_721_, v___f_730_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_731_) == 0)
{
return v___x_731_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___boxed(lean_object* v_mvarId_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_740_, v_x_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1(lean_object* v_00_u03b1_750_, lean_object* v_mvarId_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_751_, v_x_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___boxed(lean_object* v_00_u03b1_761_, lean_object* v_mvarId_762_, lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1(v_00_u03b1_761_, v_mvarId_762_, v_x_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0(void){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_unsigned_to_nat(32u);
v___x_776_ = lean_mk_empty_array_with_capacity(v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0(lean_object* v_simprocs_778_, lean_object* v_relevantLemmas_779_, lean_object* v___x_780_, lean_object* v_goal_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(v_simprocs_778_, v_relevantLemmas_779_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v_fst_791_; lean_object* v_snd_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_888_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v_fst_791_ = lean_ctor_get(v_a_790_, 0);
v_snd_792_ = lean_ctor_get(v_a_790_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_888_ == 0)
{
v___x_794_ = v_a_790_;
v_isShared_795_ = v_isSharedCheck_888_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_snd_792_);
lean_inc(v_fst_791_);
lean_dec(v_a_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_888_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addDefaultTypeAnalysisLemmas(v_snd_792_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_787_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v_maxSteps_800_; lean_object* v___x_801_; uint8_t v___x_802_; uint8_t v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v_maxSteps_800_ = lean_ctor_get(v___y_782_, 1);
v___x_801_ = lean_unsigned_to_nat(2u);
v___x_802_ = 0;
v___x_803_ = 1;
v___x_804_ = 0;
v___x_805_ = lean_box(0);
lean_inc(v_maxSteps_800_);
v___x_806_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_806_, 0, v_maxSteps_800_);
lean_ctor_set(v___x_806_, 1, v___x_801_);
lean_ctor_set(v___x_806_, 2, v___x_805_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 1, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 2, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 3, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 4, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 5, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 6, v___x_804_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 7, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 8, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 9, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 10, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 11, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 12, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 13, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 14, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 15, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 16, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 17, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 18, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 19, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 20, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 21, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 22, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 23, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 24, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 25, v___x_803_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 26, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 27, v___x_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3 + 28, v___x_802_);
v___x_807_ = l_Lean_Options_empty;
v___x_808_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_806_, v_a_797_, v_a_799_, v___x_807_, v___y_784_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v___x_810_ = l_Lean_Meta_getPropHyps(v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_mk_empty_array_with_capacity(v___x_812_);
v___x_814_ = lean_array_push(v___x_813_, v_fst_791_);
v___x_815_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1);
lean_inc(v___x_780_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_780_);
lean_ctor_set(v___x_794_, 0, v___x_815_);
v___x_817_ = v___x_794_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_780_);
v___x_817_ = v_reuseFailAlloc_855_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; size_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_818_ = lean_unsigned_to_nat(32u);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_818_);
v___x_820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2);
v___x_821_ = ((size_t)5ULL);
lean_inc(v___x_780_);
v___x_822_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_819_);
lean_ctor_set(v___x_822_, 2, v___x_780_);
lean_ctor_set(v___x_822_, 3, v___x_780_);
lean_ctor_set_usize(v___x_822_, 4, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_823_, 0, v___x_815_);
lean_ctor_set(v___x_823_, 1, v___x_815_);
lean_ctor_set(v___x_823_, 2, v___x_815_);
lean_ctor_set(v___x_823_, 3, v___x_822_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_817_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = l_Lean_Meta_simpGoal(v_goal_781_, v_a_809_, v___x_814_, v___x_805_, v___x_803_, v_a_811_, v___x_824_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_846_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_846_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_846_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_846_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_fst_830_; 
v_fst_830_ = lean_ctor_get(v_a_826_, 0);
lean_inc(v_fst_830_);
lean_dec(v_a_826_);
if (lean_obj_tag(v_fst_830_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_842_; 
v_val_831_ = lean_ctor_get(v_fst_830_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_fst_830_);
if (v_isSharedCheck_842_ == 0)
{
v___x_833_ = v_fst_830_;
v_isShared_834_ = v_isSharedCheck_842_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_val_831_);
lean_dec(v_fst_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_842_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_snd_835_; lean_object* v___x_837_; 
v_snd_835_ = lean_ctor_get(v_val_831_, 1);
lean_inc(v_snd_835_);
lean_dec(v_val_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_snd_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_snd_835_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_837_);
v___x_839_ = v___x_828_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v___x_844_; 
lean_dec(v_fst_830_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_805_);
v___x_844_ = v___x_828_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_805_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_847_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_825_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_825_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_809_);
lean_del_object(v___x_794_);
lean_dec(v_fst_791_);
lean_dec(v_goal_781_);
lean_dec(v___x_780_);
v_a_856_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_810_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_810_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_del_object(v___x_794_);
lean_dec(v_fst_791_);
lean_dec(v_goal_781_);
lean_dec(v___x_780_);
v_a_864_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_808_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_808_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_797_);
lean_del_object(v___x_794_);
lean_dec(v_fst_791_);
lean_dec(v_goal_781_);
lean_dec(v___x_780_);
v_a_872_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_798_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_798_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
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
lean_del_object(v___x_794_);
lean_dec(v_fst_791_);
lean_dec(v_goal_781_);
lean_dec(v___x_780_);
v_a_880_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_796_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_796_);
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
lean_dec(v_goal_781_);
lean_dec(v___x_780_);
v_a_889_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_789_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_789_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___boxed(lean_object* v_simprocs_897_, lean_object* v_relevantLemmas_898_, lean_object* v___x_899_, lean_object* v_goal_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0(v_simprocs_897_, v_relevantLemmas_898_, v___x_899_, v_goal_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_909_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1(void){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0(lean_box(0));
return v___x_910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_simprocs_913_; 
v___x_911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1);
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0);
v_simprocs_913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_simprocs_913_, 0, v___x_912_);
lean_ctor_set(v_simprocs_913_, 1, v___x_912_);
lean_ctor_set(v_simprocs_913_, 2, v___x_911_);
lean_ctor_set(v_simprocs_913_, 3, v___x_911_);
return v_simprocs_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(lean_object* v_goal_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_simprocs_924_; lean_object* v___x_925_; lean_object* v_relevantLemmas_926_; lean_object* v___f_927_; lean_object* v___x_928_; 
v_simprocs_924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2);
v___x_925_ = lean_unsigned_to_nat(0u);
v_relevantLemmas_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3));
lean_inc(v_goal_916_);
v___f_927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___boxed), 11, 4);
lean_closure_set(v___f_927_, 0, v_simprocs_924_);
lean_closure_set(v___f_927_, 1, v_relevantLemmas_926_);
lean_closure_set(v___f_927_, 2, v___x_925_);
lean_closure_set(v___f_927_, 3, v_goal_916_);
v___x_928_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_goal_916_, v___f_927_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___boxed(lean_object* v_goal_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(v_goal_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(lean_object* v_e_938_, lean_object* v___y_939_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_Expr_hasMVar(v_e_938_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_e_938_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; lean_object* v_mctx_944_; lean_object* v___x_945_; lean_object* v_fst_946_; lean_object* v_snd_947_; lean_object* v___x_948_; lean_object* v_cache_949_; lean_object* v_zetaDeltaFVarIds_950_; lean_object* v_postponed_951_; lean_object* v_diag_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_961_; 
v___x_943_ = lean_st_ref_get(v___y_939_);
v_mctx_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc_ref(v_mctx_944_);
lean_dec(v___x_943_);
v___x_945_ = l_Lean_instantiateMVarsCore(v_mctx_944_, v_e_938_);
v_fst_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_fst_946_);
v_snd_947_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_snd_947_);
lean_dec_ref(v___x_945_);
v___x_948_ = lean_st_ref_take(v___y_939_);
v_cache_949_ = lean_ctor_get(v___x_948_, 1);
v_zetaDeltaFVarIds_950_ = lean_ctor_get(v___x_948_, 2);
v_postponed_951_ = lean_ctor_get(v___x_948_, 3);
v_diag_952_ = lean_ctor_get(v___x_948_, 4);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v___x_948_, 0);
lean_dec(v_unused_962_);
v___x_954_ = v___x_948_;
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_diag_952_);
lean_inc(v_postponed_951_);
lean_inc(v_zetaDeltaFVarIds_950_);
lean_inc(v_cache_949_);
lean_dec(v___x_948_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v_snd_947_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_snd_947_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_cache_949_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_zetaDeltaFVarIds_950_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_postponed_951_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v_diag_952_);
v___x_957_ = v_reuseFailAlloc_960_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_st_ref_set(v___y_939_, v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v_fst_946_);
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg___boxed(lean_object* v_e_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v_e_963_, v___y_964_);
lean_dec(v___y_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0(lean_object* v_e_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v_e_967_, v___y_969_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___boxed(lean_object* v_e_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0(v_e_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_980_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(lean_object* v_a_981_, lean_object* v_x_982_){
_start:
{
if (lean_obj_tag(v_x_982_) == 0)
{
uint8_t v___x_983_; 
v___x_983_ = 0;
return v___x_983_;
}
else
{
lean_object* v_key_984_; lean_object* v_tail_985_; uint8_t v___x_986_; 
v_key_984_ = lean_ctor_get(v_x_982_, 0);
v_tail_985_ = lean_ctor_get(v_x_982_, 2);
v___x_986_ = lean_name_eq(v_key_984_, v_a_981_);
if (v___x_986_ == 0)
{
v_x_982_ = v_tail_985_;
goto _start;
}
else
{
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg___boxed(lean_object* v_a_988_, lean_object* v_x_989_){
_start:
{
uint8_t v_res_990_; lean_object* v_r_991_; 
v_res_990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_988_, v_x_989_);
lean_dec(v_x_989_);
lean_dec(v_a_988_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_992_; uint64_t v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(1723u);
v___x_993_ = lean_uint64_of_nat(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(lean_object* v_m_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_buckets_996_; lean_object* v___x_997_; uint64_t v___y_999_; 
v_buckets_996_ = lean_ctor_get(v_m_994_, 1);
v___x_997_ = lean_array_get_size(v_buckets_996_);
if (lean_obj_tag(v_a_995_) == 0)
{
uint64_t v___x_1013_; 
v___x_1013_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0);
v___y_999_ = v___x_1013_;
goto v___jp_998_;
}
else
{
uint64_t v_hash_1014_; 
v_hash_1014_ = lean_ctor_get_uint64(v_a_995_, sizeof(void*)*2);
v___y_999_ = v_hash_1014_;
goto v___jp_998_;
}
v___jp_998_:
{
uint64_t v___x_1000_; uint64_t v___x_1001_; uint64_t v_fold_1002_; uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; size_t v___x_1006_; size_t v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1000_ = 32ULL;
v___x_1001_ = lean_uint64_shift_right(v___y_999_, v___x_1000_);
v_fold_1002_ = lean_uint64_xor(v___y_999_, v___x_1001_);
v___x_1003_ = 16ULL;
v___x_1004_ = lean_uint64_shift_right(v_fold_1002_, v___x_1003_);
v___x_1005_ = lean_uint64_xor(v_fold_1002_, v___x_1004_);
v___x_1006_ = lean_uint64_to_usize(v___x_1005_);
v___x_1007_ = lean_usize_of_nat(v___x_997_);
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_sub(v___x_1007_, v___x_1008_);
v___x_1010_ = lean_usize_land(v___x_1006_, v___x_1009_);
v___x_1011_ = lean_array_uget_borrowed(v_buckets_996_, v___x_1010_);
v___x_1012_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_995_, v___x_1011_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___boxed(lean_object* v_m_1015_, lean_object* v_a_1016_){
_start:
{
uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(v_m_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_m_1015_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0(uint8_t v___x_1019_, lean_object* v_interestingStructures_1020_, lean_object* v_decl_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Lean_LocalDecl_isLet(v_decl_1021_, v___x_1019_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; 
v___x_1028_ = l_Lean_LocalDecl_isImplementationDetail(v_decl_1021_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1047_; 
v___x_1029_ = l_Lean_LocalDecl_type(v_decl_1021_);
v___x_1030_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v___x_1029_, v___y_1023_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1047_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1047_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = l_Lean_Expr_getAppFn(v_a_1031_);
lean_dec(v_a_1031_);
v___x_1036_ = l_Lean_Expr_constName_x3f(v___x_1035_);
lean_dec_ref(v___x_1035_);
if (lean_obj_tag(v___x_1036_) == 1)
{
lean_object* v_val_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v_val_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(v_interestingStructures_1020_, v_val_1037_);
lean_dec(v_val_1037_);
v___x_1039_ = lean_box(v___x_1038_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1039_);
v___x_1041_ = v___x_1033_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_dec(v___x_1036_);
v___x_1043_ = lean_box(v___x_1019_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1043_);
v___x_1045_ = v___x_1033_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_box(v___x_1019_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_box(v___x_1019_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0___boxed(lean_object* v___x_1052_, lean_object* v_interestingStructures_1053_, lean_object* v_decl_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v___x_3219__boxed_1060_; lean_object* v_res_1061_; 
v___x_3219__boxed_1060_ = lean_unbox(v___x_1052_);
v_res_1061_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0(v___x_3219__boxed_1060_, v_interestingStructures_1053_, v_decl_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec_ref(v_decl_1054_);
lean_dec_ref(v_interestingStructures_1053_);
return v_res_1061_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1(lean_object* v_goal_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_typeAnalysis_1074_; lean_object* v_interestingStructures_1075_; lean_object* v_size_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1073_ = lean_st_ref_get(v___y_1067_);
v_typeAnalysis_1074_ = lean_ctor_get(v___x_1073_, 2);
lean_inc_ref(v_typeAnalysis_1074_);
lean_dec(v___x_1073_);
v_interestingStructures_1075_ = lean_ctor_get(v_typeAnalysis_1074_, 0);
lean_inc_ref(v_interestingStructures_1075_);
lean_dec_ref(v_typeAnalysis_1074_);
v_size_1076_ = lean_ctor_get(v_interestingStructures_1075_, 0);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_nat_dec_eq(v_size_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(v___x_1078_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1080_, 0, v___x_1079_);
lean_closure_set(v___f_1080_, 1, v_interestingStructures_1075_);
v___x_1081_ = l_Lean_MVarId_casesRec(v_goal_1065_, v___f_1080_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
if (lean_obj_tag(v_a_1082_) == 1)
{
lean_object* v_tail_1090_; 
v_tail_1090_ = lean_ctor_get(v_a_1082_, 1);
if (lean_obj_tag(v_tail_1090_) == 0)
{
lean_object* v_head_1091_; lean_object* v___x_1092_; 
v_head_1091_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_head_1091_);
lean_dec_ref_known(v_a_1082_, 2);
v___x_1092_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(v_head_1091_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1092_;
}
else
{
lean_dec_ref_known(v_a_1082_, 2);
v___y_1084_ = v___y_1068_;
v___y_1085_ = v___y_1069_;
v___y_1086_ = v___y_1070_;
v___y_1087_ = v___y_1071_;
goto v___jp_1083_;
}
}
else
{
lean_dec(v_a_1082_);
v___y_1084_ = v___y_1068_;
v___y_1085_ = v___y_1069_;
v___y_1086_ = v___y_1070_;
v___y_1087_ = v___y_1071_;
goto v___jp_1083_;
}
v___jp_1083_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1);
v___x_1089_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_1088_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
return v___x_1089_;
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1081_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1081_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec_ref(v_interestingStructures_1075_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_goal_1065_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___boxed(lean_object* v_goal_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1(v_goal_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(lean_object* v_00_u03b2_1120_, lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
uint8_t v___x_1123_; 
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(v_m_1121_, v_a_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___boxed(lean_object* v_00_u03b2_1124_, lean_object* v_m_1125_, lean_object* v_a_1126_){
_start:
{
uint8_t v_res_1127_; lean_object* v_r_1128_; 
v_res_1127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(v_00_u03b2_1124_, v_m_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_m_1125_);
v_r_1128_ = lean_box(v_res_1127_);
return v_r_1128_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1(lean_object* v_00_u03b2_1129_, lean_object* v_a_1130_, lean_object* v_x_1131_){
_start:
{
uint8_t v___x_1132_; 
v___x_1132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_1130_, v_x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1133_, lean_object* v_a_1134_, lean_object* v_x_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1(v_00_u03b2_1133_, v_a_1134_, v_x_1135_);
lean_dec(v_x_1135_);
lean_dec(v_a_1134_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
}
#ifdef __cplusplus
}
#endif
