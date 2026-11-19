// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Cegar.Subsolver
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.BitVec public import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Tactic.BVDecide.External
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
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_BvSolverM_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_empty___redArg();
lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_BvSolverM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlReaderT___redArg();
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Cadical_Solver_new();
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(uint8_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(uint8_t);
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
lean_object* l_instMonadControlStateRefT_x27___redArg();
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_BvSolverM_pop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_BvSolverM_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1_spec__1___boxed(lean_object*);
static const lean_array_object l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__2_value;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to reify subsolver hypothesis "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__12;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__14;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__15;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__17;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__20;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__21;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__23;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__24;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__26;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__27;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__29;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__30;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__31;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__32 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__32_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__34;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__35;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__36;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__37;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__38;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__39;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__40;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__41;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__42;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__43;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__44 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__44_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__44_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__45 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__45_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__46;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__47;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__48;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__49;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__50;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__51;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__52;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__53;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__54 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__54_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__55;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_BvSolverM_pop___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_BvSolverM_solve___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_unsigned_to_nat(16u);
v___x_7_ = lean_mk_array(v___x_6_, v___x_5_);
return v___x_7_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__2(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__1);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__3(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__2);
v___x_12_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__0));
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0___closed__3);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1_spec__1(lean_object* v_aig_15_){
_start:
{
lean_object* v_decls_16_; lean_object* v___x_17_; uint8_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_decls_16_ = lean_ctor_get(v_aig_15_, 0);
v___x_17_ = lean_array_get_size(v_decls_16_);
v___x_18_ = 0;
v___x_19_ = lean_box(v___x_18_);
v___x_20_ = lean_mk_array(v___x_17_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1_spec__1___boxed(lean_object* v_aig_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1_spec__1(v_aig_21_);
lean_dec_ref(v_aig_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1(lean_object* v_aig_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1___closed__0));
v___x_27_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1_spec__1(v_aig_25_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_26_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1___boxed(lean_object* v_aig_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1(v_aig_29_);
lean_dec_ref(v_aig_29_);
return v_res_30_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1);
v___x_35_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
lean_ctor_set(v___x_35_, 2, v___x_34_);
lean_ctor_set(v___x_35_, 3, v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_box(0);
v___x_37_ = lean_unsigned_to_nat(16u);
v___x_38_ = lean_mk_array(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3);
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0;
v___x_45_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_46_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6);
v___x_47_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5);
v___x_48_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0;
v___x_49_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v___x_47_);
lean_ctor_set(v___x_49_, 2, v___x_46_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg(lean_object* v_ctx_52_, lean_object* v_mvar_53_, lean_object* v_reifyState_54_, uint8_t v_trackFunAtoms_55_){
_start:
{
lean_object* v_config_57_; lean_object* v_exprDef_58_; lean_object* v_certDef_59_; lean_object* v_reflectionDef_60_; lean_object* v_solver_61_; lean_object* v_lratPath_62_; lean_object* v_restrictedTypes_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_102_; 
v_config_57_ = lean_ctor_get(v_ctx_52_, 5);
v_exprDef_58_ = lean_ctor_get(v_ctx_52_, 0);
v_certDef_59_ = lean_ctor_get(v_ctx_52_, 1);
v_reflectionDef_60_ = lean_ctor_get(v_ctx_52_, 2);
v_solver_61_ = lean_ctor_get(v_ctx_52_, 3);
v_lratPath_62_ = lean_ctor_get(v_ctx_52_, 4);
v_restrictedTypes_63_ = lean_ctor_get(v_ctx_52_, 6);
v_isSharedCheck_102_ = !lean_is_exclusive(v_ctx_52_);
if (v_isSharedCheck_102_ == 0)
{
v___x_65_ = v_ctx_52_;
v_isShared_66_ = v_isSharedCheck_102_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_restrictedTypes_63_);
lean_inc(v_config_57_);
lean_inc(v_lratPath_62_);
lean_inc(v_solver_61_);
lean_inc(v_reflectionDef_60_);
lean_inc(v_certDef_59_);
lean_inc(v_exprDef_58_);
lean_dec(v_ctx_52_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_102_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v_timeout_67_; uint8_t v_trimProofs_68_; uint8_t v_binaryProofs_69_; uint8_t v_acNf_70_; uint8_t v_andFlattening_71_; uint8_t v_embeddedConstraintSubst_72_; uint8_t v_graphviz_73_; lean_object* v_maxSteps_74_; uint8_t v_solverMode_75_; lean_object* v_cegarRounds_76_; uint8_t v_eprSymBreak_77_; uint8_t v_eprProjections_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_101_; 
v_timeout_67_ = lean_ctor_get(v_config_57_, 0);
v_trimProofs_68_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3);
v_binaryProofs_69_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3 + 1);
v_acNf_70_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3 + 2);
v_andFlattening_71_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_72_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3 + 4);
v_graphviz_73_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3 + 8);
v_maxSteps_74_ = lean_ctor_get(v_config_57_, 1);
v_solverMode_75_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3 + 10);
v_cegarRounds_76_ = lean_ctor_get(v_config_57_, 2);
v_eprSymBreak_77_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3 + 13);
v_eprProjections_78_ = lean_ctor_get_uint8(v_config_57_, sizeof(void*)*3 + 14);
v_isSharedCheck_101_ = !lean_is_exclusive(v_config_57_);
if (v_isSharedCheck_101_ == 0)
{
v___x_80_ = v_config_57_;
v_isShared_81_ = v_isSharedCheck_101_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_cegarRounds_76_);
lean_inc(v_maxSteps_74_);
lean_inc(v_timeout_67_);
lean_dec(v_config_57_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_101_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint8_t v___x_82_; lean_object* v___x_84_; 
v___x_82_ = 0;
lean_inc(v_timeout_67_);
if (v_isShared_81_ == 0)
{
v___x_84_ = v___x_80_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_timeout_67_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_maxSteps_74_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_cegarRounds_76_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3, v_trimProofs_68_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3 + 1, v_binaryProofs_69_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3 + 2, v_acNf_70_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3 + 3, v_andFlattening_71_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_72_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3 + 8, v_graphviz_73_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3 + 10, v_solverMode_75_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3 + 13, v_eprSymBreak_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_100_, sizeof(void*)*3 + 14, v_eprProjections_78_);
v___x_84_ = v_reuseFailAlloc_100_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v_ctx_86_; 
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*3 + 5, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*3 + 6, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*3 + 7, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*3 + 9, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*3 + 11, v_trackFunAtoms_55_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*3 + 12, v___x_82_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 5, v___x_84_);
v_ctx_86_ = v___x_65_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_exprDef_58_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_certDef_59_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_reflectionDef_60_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_solver_61_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_lratPath_62_);
lean_ctor_set(v_reuseFailAlloc_99_, 5, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 6, v_restrictedTypes_63_);
v_ctx_86_ = v_reuseFailAlloc_99_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_87_ = l_Lean_Cadical_Solver_new();
v___x_88_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_solverMode_75_);
v___x_89_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(v___x_88_);
v___x_90_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v___x_89_, v___x_87_);
lean_dec_ref(v___x_89_);
v___x_91_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2);
v___x_92_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7);
v___x_93_ = lean_unsigned_to_nat(1000u);
v___x_94_ = lean_nat_mul(v_timeout_67_, v___x_93_);
lean_dec(v_timeout_67_);
v___x_95_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8));
v___x_96_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_96_, 0, v___x_92_);
lean_ctor_set(v___x_96_, 1, v___x_87_);
lean_ctor_set(v___x_96_, 2, v___x_94_);
lean_ctor_set(v___x_96_, 3, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_97_, 0, v_reifyState_54_);
lean_ctor_set(v___x_97_, 1, v___x_91_);
lean_ctor_set(v___x_97_, 2, v___x_96_);
lean_ctor_set(v___x_97_, 3, v_mvar_53_);
lean_ctor_set(v___x_97_, 4, v_ctx_86_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___boxed(lean_object* v_ctx_103_, lean_object* v_mvar_104_, lean_object* v_reifyState_105_, lean_object* v_trackFunAtoms_106_, lean_object* v_a_107_){
_start:
{
uint8_t v_trackFunAtoms_boxed_108_; lean_object* v_res_109_; 
v_trackFunAtoms_boxed_108_ = lean_unbox(v_trackFunAtoms_106_);
v_res_109_ = l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg(v_ctx_103_, v_mvar_104_, v_reifyState_105_, v_trackFunAtoms_boxed_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new(lean_object* v_ctx_110_, lean_object* v_mvar_111_, lean_object* v_reifyState_112_, uint8_t v_trackFunAtoms_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg(v_ctx_110_, v_mvar_111_, v_reifyState_112_, v_trackFunAtoms_113_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___boxed(lean_object* v_ctx_122_, lean_object* v_mvar_123_, lean_object* v_reifyState_124_, lean_object* v_trackFunAtoms_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
uint8_t v_trackFunAtoms_boxed_133_; lean_object* v_res_134_; 
v_trackFunAtoms_boxed_133_ = lean_unbox(v_trackFunAtoms_125_);
v_res_134_ = l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new(v_ctx_122_, v_mvar_123_, v_reifyState_124_, v_trackFunAtoms_boxed_133_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__0(lean_object* v_snd_135_, lean_object* v_s_136_){
_start:
{
lean_object* v_reifyState_137_; lean_object* v_preProcessState_138_; lean_object* v_mvar_139_; lean_object* v_ctx_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v_reifyState_137_ = lean_ctor_get(v_s_136_, 0);
v_preProcessState_138_ = lean_ctor_get(v_s_136_, 1);
v_mvar_139_ = lean_ctor_get(v_s_136_, 3);
v_ctx_140_ = lean_ctor_get(v_s_136_, 4);
v_isSharedCheck_149_ = !lean_is_exclusive(v_s_136_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v_s_136_, 2);
lean_dec(v_unused_150_);
v___x_142_ = v_s_136_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_ctx_140_);
lean_inc(v_mvar_139_);
lean_inc(v_preProcessState_138_);
lean_inc(v_reifyState_137_);
lean_dec(v_s_136_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 2, v_snd_135_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_reifyState_137_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_preProcessState_138_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_snd_135_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_mvar_139_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_ctx_140_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_144_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1(lean_object* v_toApplicative_151_, lean_object* v_fst_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_toPure_154_; lean_object* v___x_155_; 
v_toPure_154_ = lean_ctor_get(v_toApplicative_151_, 1);
lean_inc(v_toPure_154_);
lean_dec_ref(v_toApplicative_151_);
v___x_155_ = lean_apply_2(v_toPure_154_, lean_box(0), v_fst_152_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2(lean_object* v_toApplicative_156_, lean_object* v_a_157_, lean_object* v_inst_158_, lean_object* v_toBind_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_fst_161_ = lean_ctor_get(v_a_160_, 0);
lean_inc(v_fst_161_);
v_snd_162_ = lean_ctor_get(v_a_160_, 1);
lean_inc(v_snd_162_);
lean_dec_ref(v_a_160_);
v___f_163_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_163_, 0, v_snd_162_);
v___f_164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_164_, 0, v_toApplicative_156_);
lean_closure_set(v___f_164_, 1, v_fst_161_);
lean_inc(v_a_157_);
v___x_165_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_165_, 0, lean_box(0));
lean_closure_set(v___x_165_, 1, lean_box(0));
lean_closure_set(v___x_165_, 2, lean_box(0));
lean_closure_set(v___x_165_, 3, v_a_157_);
lean_closure_set(v___x_165_, 4, v___f_163_);
v___x_166_ = lean_apply_2(v_inst_158_, lean_box(0), v___x_165_);
v___x_167_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_166_, v___f_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2___boxed(lean_object* v_toApplicative_168_, lean_object* v_a_169_, lean_object* v_inst_170_, lean_object* v_toBind_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2(v_toApplicative_168_, v_a_169_, v_inst_170_, v_toBind_171_, v_a_172_);
lean_dec(v_a_169_);
return v_res_173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_Sat_AIG_empty___redArg();
return v___x_174_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0);
v___x_176_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1);
v___x_178_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5);
v___x_179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3(lean_object* v_s_181_){
_start:
{
lean_object* v_bvSolver_182_; lean_object* v_reifyState_183_; lean_object* v_preProcessState_184_; lean_object* v_mvar_185_; lean_object* v_ctx_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_199_; 
v_bvSolver_182_ = lean_ctor_get(v_s_181_, 2);
v_reifyState_183_ = lean_ctor_get(v_s_181_, 0);
v_preProcessState_184_ = lean_ctor_get(v_s_181_, 1);
v_mvar_185_ = lean_ctor_get(v_s_181_, 3);
v_ctx_186_ = lean_ctor_get(v_s_181_, 4);
v_isSharedCheck_199_ = !lean_is_exclusive(v_s_181_);
if (v_isSharedCheck_199_ == 0)
{
v___x_188_ = v_s_181_;
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_ctx_186_);
lean_inc(v_mvar_185_);
lean_inc(v_bvSolver_182_);
lean_inc(v_preProcessState_184_);
lean_inc(v_reifyState_183_);
lean_dec(v_s_181_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_satSolver_190_; lean_object* v_solverTimeBudgetMs_191_; lean_object* v_assumptions_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v_satSolver_190_ = lean_ctor_get(v_bvSolver_182_, 1);
v_solverTimeBudgetMs_191_ = lean_ctor_get(v_bvSolver_182_, 2);
v_assumptions_192_ = lean_ctor_get(v_bvSolver_182_, 3);
v___x_193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2);
lean_inc_ref(v_assumptions_192_);
lean_inc(v_solverTimeBudgetMs_191_);
lean_inc_ref(v_satSolver_190_);
v___x_194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_satSolver_190_);
lean_ctor_set(v___x_194_, 2, v_solverTimeBudgetMs_191_);
lean_ctor_set(v___x_194_, 3, v_assumptions_192_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 2, v___x_194_);
v___x_196_ = v___x_188_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_reifyState_183_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_preProcessState_184_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v_mvar_185_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v_ctx_186_);
v___x_196_ = v_reuseFailAlloc_198_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v_bvSolver_182_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__4(lean_object* v_ctx_200_, lean_object* v_x_201_, lean_object* v_inst_202_, lean_object* v_toBind_203_, lean_object* v___f_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_BvSolverM_run___boxed), 11, 4);
lean_closure_set(v___x_206_, 0, lean_box(0));
lean_closure_set(v___x_206_, 1, v_ctx_200_);
lean_closure_set(v___x_206_, 2, v_a_205_);
lean_closure_set(v___x_206_, 3, v_x_201_);
v___x_207_ = lean_apply_2(v_inst_202_, lean_box(0), v___x_206_);
v___x_208_ = lean_apply_4(v_toBind_203_, lean_box(0), lean_box(0), v___x_207_, v___f_204_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5(lean_object* v_x_209_, lean_object* v_inst_210_, lean_object* v_toBind_211_, lean_object* v___f_212_, lean_object* v_a_213_, lean_object* v___f_214_, lean_object* v_inst_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_ctx_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_ctx_217_ = lean_ctor_get(v_a_216_, 4);
lean_inc_ref(v_ctx_217_);
lean_dec_ref(v_a_216_);
lean_inc(v_toBind_211_);
v___f_218_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__4), 6, 5);
lean_closure_set(v___f_218_, 0, v_ctx_217_);
lean_closure_set(v___f_218_, 1, v_x_209_);
lean_closure_set(v___f_218_, 2, v_inst_210_);
lean_closure_set(v___f_218_, 3, v_toBind_211_);
lean_closure_set(v___f_218_, 4, v___f_212_);
lean_inc(v_a_213_);
v___x_219_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_219_, 0, lean_box(0));
lean_closure_set(v___x_219_, 1, lean_box(0));
lean_closure_set(v___x_219_, 2, lean_box(0));
lean_closure_set(v___x_219_, 3, v_a_213_);
lean_closure_set(v___x_219_, 4, v___f_214_);
v___x_220_ = lean_apply_2(v_inst_215_, lean_box(0), v___x_219_);
v___x_221_ = lean_apply_4(v_toBind_211_, lean_box(0), lean_box(0), v___x_220_, v___f_218_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5___boxed(lean_object* v_x_222_, lean_object* v_inst_223_, lean_object* v_toBind_224_, lean_object* v___f_225_, lean_object* v_a_226_, lean_object* v___f_227_, lean_object* v_inst_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5(v_x_222_, v_inst_223_, v_toBind_224_, v___f_225_, v_a_226_, v___f_227_, v_inst_228_, v_a_229_);
lean_dec(v_a_226_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_x_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_toApplicative_237_; lean_object* v_toBind_238_; lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_toApplicative_237_ = lean_ctor_get(v_inst_232_, 0);
lean_inc_ref(v_toApplicative_237_);
v_toBind_238_ = lean_ctor_get(v_inst_232_, 1);
lean_inc_n(v_toBind_238_, 3);
lean_dec_ref(v_inst_232_);
lean_inc_n(v_inst_234_, 2);
lean_inc_n(v_a_236_, 3);
v___f_239_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_239_, 0, v_toApplicative_237_);
lean_closure_set(v___f_239_, 1, v_a_236_);
lean_closure_set(v___f_239_, 2, v_inst_234_);
lean_closure_set(v___f_239_, 3, v_toBind_238_);
v___f_240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___closed__0));
v___f_241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_241_, 0, v_x_235_);
lean_closure_set(v___f_241_, 1, v_inst_233_);
lean_closure_set(v___f_241_, 2, v_toBind_238_);
lean_closure_set(v___f_241_, 3, v___f_239_);
lean_closure_set(v___f_241_, 4, v_a_236_);
lean_closure_set(v___f_241_, 5, v___f_240_);
lean_closure_set(v___f_241_, 6, v_inst_234_);
v___x_242_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, lean_box(0));
lean_closure_set(v___x_242_, 2, v_a_236_);
v___x_243_ = lean_apply_2(v_inst_234_, lean_box(0), v___x_242_);
v___x_244_ = lean_apply_4(v_toBind_238_, lean_box(0), lean_box(0), v___x_243_, v___f_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___boxed(lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_x_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_245_, v_inst_246_, v_inst_247_, v_x_248_, v_a_249_);
lean_dec(v_a_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM(lean_object* v_00_u03c3_251_, lean_object* v_m_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_00_u03b1_257_, lean_object* v_x_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_254_, v_inst_255_, v_inst_256_, v_x_258_, v_a_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___boxed(lean_object* v_00_u03c3_261_, lean_object* v_m_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_00_u03b1_267_, lean_object* v_x_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM(v_00_u03c3_261_, v_m_262_, v_inst_263_, v_inst_264_, v_inst_265_, v_inst_266_, v_00_u03b1_267_, v_x_268_, v_a_269_);
lean_dec(v_a_269_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_box(0);
v___x_272_ = lean_unsigned_to_nat(16u);
v___x_273_ = lean_mk_array(v___x_272_, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__0);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__3));
v___x_285_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1);
v___x_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_ctor_set(v___x_286_, 2, v___x_285_);
lean_ctor_set(v___x_286_, 3, v___x_284_);
lean_ctor_set(v___x_286_, 4, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__5);
v___x_288_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__4));
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__6);
v___x_291_ = lean_box(0);
v___x_292_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1);
v___x_293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_291_);
lean_ctor_set(v___x_293_, 2, v___x_291_);
lean_ctor_set(v___x_293_, 3, v___x_292_);
lean_ctor_set(v___x_293_, 4, v___x_290_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0(lean_object* v_s_294_){
_start:
{
lean_object* v_reifyState_295_; lean_object* v_preProcessState_296_; lean_object* v_bvSolver_297_; lean_object* v_mvar_298_; lean_object* v_ctx_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_308_; 
v_reifyState_295_ = lean_ctor_get(v_s_294_, 0);
v_preProcessState_296_ = lean_ctor_get(v_s_294_, 1);
v_bvSolver_297_ = lean_ctor_get(v_s_294_, 2);
v_mvar_298_ = lean_ctor_get(v_s_294_, 3);
v_ctx_299_ = lean_ctor_get(v_s_294_, 4);
v_isSharedCheck_308_ = !lean_is_exclusive(v_s_294_);
if (v_isSharedCheck_308_ == 0)
{
v___x_301_ = v_s_294_;
v_isShared_302_ = v_isSharedCheck_308_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_ctx_299_);
lean_inc(v_mvar_298_);
lean_inc(v_bvSolver_297_);
lean_inc(v_preProcessState_296_);
lean_inc(v_reifyState_295_);
lean_dec(v_s_294_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_308_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__7);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_303_);
v___x_305_ = v___x_301_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_preProcessState_296_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_bvSolver_297_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_mvar_298_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_ctx_299_);
v___x_305_ = v_reuseFailAlloc_307_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_reifyState_295_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__1(lean_object* v_snd_309_, lean_object* v_s_310_){
_start:
{
lean_object* v_preProcessState_311_; lean_object* v_bvSolver_312_; lean_object* v_mvar_313_; lean_object* v_ctx_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_323_; 
v_preProcessState_311_ = lean_ctor_get(v_s_310_, 1);
v_bvSolver_312_ = lean_ctor_get(v_s_310_, 2);
v_mvar_313_ = lean_ctor_get(v_s_310_, 3);
v_ctx_314_ = lean_ctor_get(v_s_310_, 4);
v_isSharedCheck_323_ = !lean_is_exclusive(v_s_310_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v_s_310_, 0);
lean_dec(v_unused_324_);
v___x_316_ = v_s_310_;
v_isShared_317_ = v_isSharedCheck_323_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_ctx_314_);
lean_inc(v_mvar_313_);
lean_inc(v_bvSolver_312_);
lean_inc(v_preProcessState_311_);
lean_dec(v_s_310_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_323_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_box(0);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v_snd_309_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_snd_309_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_preProcessState_311_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_bvSolver_312_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v_mvar_313_);
lean_ctor_set(v_reuseFailAlloc_322_, 4, v_ctx_314_);
v___x_320_ = v_reuseFailAlloc_322_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_318_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3(lean_object* v_toApplicative_325_, lean_object* v_a_326_, lean_object* v_inst_327_, lean_object* v_toBind_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_fst_330_ = lean_ctor_get(v_a_329_, 0);
lean_inc(v_fst_330_);
v_snd_331_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_snd_331_);
lean_dec_ref(v_a_329_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_332_, 0, v_snd_331_);
v___f_333_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_333_, 0, v_toApplicative_325_);
lean_closure_set(v___f_333_, 1, v_fst_330_);
lean_inc(v_a_326_);
v___x_334_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_334_, 0, lean_box(0));
lean_closure_set(v___x_334_, 1, lean_box(0));
lean_closure_set(v___x_334_, 2, lean_box(0));
lean_closure_set(v___x_334_, 3, v_a_326_);
lean_closure_set(v___x_334_, 4, v___f_332_);
v___x_335_ = lean_apply_2(v_inst_327_, lean_box(0), v___x_334_);
v___x_336_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_335_, v___f_333_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3___boxed(lean_object* v_toApplicative_337_, lean_object* v_a_338_, lean_object* v_inst_339_, lean_object* v_toBind_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3(v_toApplicative_337_, v_a_338_, v_inst_339_, v_toBind_340_, v_a_341_);
lean_dec(v_a_338_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2(lean_object* v_a_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_st_mk_ref(v_a_343_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2___boxed(lean_object* v_a_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2(v_a_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4(lean_object* v_x_368_, lean_object* v___x_369_, lean_object* v_ref_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
lean_inc(v___y_379_);
lean_inc_ref(v___y_378_);
lean_inc(v___y_377_);
lean_inc_ref(v___y_376_);
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
lean_inc(v___y_373_);
lean_inc_ref(v___y_372_);
lean_inc(v___y_371_);
lean_inc(v_ref_370_);
v___x_381_ = lean_apply_12(v_x_368_, v___x_369_, v_ref_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, lean_box(0));
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_391_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_391_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_386_ = lean_st_ref_get(v_ref_370_);
lean_dec(v_ref_370_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_a_382_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_387_);
v___x_389_ = v___x_384_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v_ref_370_);
v_a_392_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_381_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_381_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4___boxed(lean_object* v_x_400_, lean_object* v___x_401_, lean_object* v_ref_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4(v_x_400_, v___x_401_, v_ref_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5(lean_object* v_config_416_, lean_object* v_x_417_, lean_object* v___x_418_, lean_object* v_inst_419_, lean_object* v_toBind_420_, lean_object* v___f_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___f_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2___boxed), 11, 1);
lean_closure_set(v___f_423_, 0, v_a_422_);
v___x_424_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0));
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_config_416_);
v___f_426_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4___boxed), 13, 2);
lean_closure_set(v___f_426_, 0, v_x_417_);
lean_closure_set(v___f_426_, 1, v___x_425_);
v___x_427_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_427_, 0, lean_box(0));
lean_closure_set(v___x_427_, 1, lean_box(0));
lean_closure_set(v___x_427_, 2, v___x_418_);
lean_closure_set(v___x_427_, 3, lean_box(0));
lean_closure_set(v___x_427_, 4, lean_box(0));
lean_closure_set(v___x_427_, 5, v___f_423_);
lean_closure_set(v___x_427_, 6, v___f_426_);
v___x_428_ = lean_apply_2(v_inst_419_, lean_box(0), v___x_427_);
v___x_429_ = lean_apply_4(v_toBind_420_, lean_box(0), lean_box(0), v___x_428_, v___f_421_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6(lean_object* v_x_430_, lean_object* v___x_431_, lean_object* v_inst_432_, lean_object* v_toBind_433_, lean_object* v___f_434_, lean_object* v_a_435_, lean_object* v___f_436_, lean_object* v_inst_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_ctx_439_; lean_object* v_config_440_; lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_ctx_439_ = lean_ctor_get(v_a_438_, 4);
lean_inc_ref(v_ctx_439_);
lean_dec_ref(v_a_438_);
v_config_440_ = lean_ctor_get(v_ctx_439_, 5);
lean_inc_ref(v_config_440_);
lean_dec_ref(v_ctx_439_);
lean_inc(v_toBind_433_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5), 7, 6);
lean_closure_set(v___f_441_, 0, v_config_440_);
lean_closure_set(v___f_441_, 1, v_x_430_);
lean_closure_set(v___f_441_, 2, v___x_431_);
lean_closure_set(v___f_441_, 3, v_inst_432_);
lean_closure_set(v___f_441_, 4, v_toBind_433_);
lean_closure_set(v___f_441_, 5, v___f_434_);
lean_inc(v_a_435_);
v___x_442_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_442_, 0, lean_box(0));
lean_closure_set(v___x_442_, 1, lean_box(0));
lean_closure_set(v___x_442_, 2, lean_box(0));
lean_closure_set(v___x_442_, 3, v_a_435_);
lean_closure_set(v___x_442_, 4, v___f_436_);
v___x_443_ = lean_apply_2(v_inst_437_, lean_box(0), v___x_442_);
v___x_444_ = lean_apply_4(v_toBind_433_, lean_box(0), lean_box(0), v___x_443_, v___f_441_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6___boxed(lean_object* v_x_445_, lean_object* v___x_446_, lean_object* v_inst_447_, lean_object* v_toBind_448_, lean_object* v___f_449_, lean_object* v_a_450_, lean_object* v___f_451_, lean_object* v_inst_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6(v_x_445_, v___x_446_, v_inst_447_, v_toBind_448_, v___f_449_, v_a_450_, v___f_451_, v_inst_452_, v_a_453_);
lean_dec(v_a_450_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0(void){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_instMonadEIO___redArg();
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0);
v___x_457_ = l_StateRefT_x27_instMonad___redArg(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_x_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___x_468_; lean_object* v_toApplicative_469_; lean_object* v_toFunctor_470_; lean_object* v_toSeq_471_; lean_object* v_toSeqLeft_472_; lean_object* v_toSeqRight_473_; lean_object* v___f_474_; lean_object* v___f_475_; lean_object* v___f_476_; lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___f_479_; lean_object* v___f_480_; lean_object* v___f_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_toApplicative_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_524_; 
v___x_468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1);
v_toApplicative_469_ = lean_ctor_get(v___x_468_, 0);
v_toFunctor_470_ = lean_ctor_get(v_toApplicative_469_, 0);
v_toSeq_471_ = lean_ctor_get(v_toApplicative_469_, 2);
v_toSeqLeft_472_ = lean_ctor_get(v_toApplicative_469_, 3);
v_toSeqRight_473_ = lean_ctor_get(v_toApplicative_469_, 4);
v___f_474_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2));
v___f_475_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_470_, 2);
v___f_476_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_476_, 0, v_toFunctor_470_);
v___f_477_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_477_, 0, v_toFunctor_470_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___f_476_);
lean_ctor_set(v___x_478_, 1, v___f_477_);
lean_inc(v_toSeqRight_473_);
v___f_479_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_479_, 0, v_toSeqRight_473_);
lean_inc(v_toSeqLeft_472_);
v___f_480_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_480_, 0, v_toSeqLeft_472_);
lean_inc(v_toSeq_471_);
v___f_481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_481_, 0, v_toSeq_471_);
v___x_482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_482_, 0, v___x_478_);
lean_ctor_set(v___x_482_, 1, v___f_474_);
lean_ctor_set(v___x_482_, 2, v___f_481_);
lean_ctor_set(v___x_482_, 3, v___f_480_);
lean_ctor_set(v___x_482_, 4, v___f_479_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___f_475_);
v___x_484_ = l_StateRefT_x27_instMonad___redArg(v___x_483_);
v_toApplicative_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_484_, 1);
lean_dec(v_unused_525_);
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_524_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_toApplicative_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_524_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v_toFunctor_489_; lean_object* v_toSeq_490_; lean_object* v_toSeqLeft_491_; lean_object* v_toSeqRight_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_522_; 
v_toFunctor_489_ = lean_ctor_get(v_toApplicative_485_, 0);
v_toSeq_490_ = lean_ctor_get(v_toApplicative_485_, 2);
v_toSeqLeft_491_ = lean_ctor_get(v_toApplicative_485_, 3);
v_toSeqRight_492_ = lean_ctor_get(v_toApplicative_485_, 4);
v_isSharedCheck_522_ = !lean_is_exclusive(v_toApplicative_485_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_toApplicative_485_, 1);
lean_dec(v_unused_523_);
v___x_494_ = v_toApplicative_485_;
v_isShared_495_ = v_isSharedCheck_522_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_toSeqRight_492_);
lean_inc(v_toSeqLeft_491_);
lean_inc(v_toSeq_490_);
lean_inc(v_toFunctor_489_);
lean_dec(v_toApplicative_485_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_522_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v___f_499_; lean_object* v___x_500_; lean_object* v___f_501_; lean_object* v___f_502_; lean_object* v___f_503_; lean_object* v___x_505_; 
v___f_496_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4));
v___f_497_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5));
lean_inc_ref(v_toFunctor_489_);
v___f_498_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_498_, 0, v_toFunctor_489_);
v___f_499_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_499_, 0, v_toFunctor_489_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___f_498_);
lean_ctor_set(v___x_500_, 1, v___f_499_);
v___f_501_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_501_, 0, v_toSeqRight_492_);
v___f_502_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_502_, 0, v_toSeqLeft_491_);
v___f_503_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_503_, 0, v_toSeq_490_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 4, v___f_501_);
lean_ctor_set(v___x_494_, 3, v___f_502_);
lean_ctor_set(v___x_494_, 2, v___f_503_);
lean_ctor_set(v___x_494_, 1, v___f_496_);
lean_ctor_set(v___x_494_, 0, v___x_500_);
v___x_505_ = v___x_494_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___f_496_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v___f_503_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v___f_502_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v___f_501_);
v___x_505_ = v_reuseFailAlloc_521_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___f_497_);
lean_ctor_set(v___x_487_, 0, v___x_505_);
v___x_507_ = v___x_487_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___f_497_);
v___x_507_ = v_reuseFailAlloc_520_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_toApplicative_512_; lean_object* v_toBind_513_; lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_508_ = l_StateRefT_x27_instMonad___redArg(v___x_507_);
v___x_509_ = l_ReaderT_instMonad___redArg(v___x_508_);
v___x_510_ = l_StateRefT_x27_instMonad___redArg(v___x_509_);
v___x_511_ = l_ReaderT_instMonad___redArg(v___x_510_);
v_toApplicative_512_ = lean_ctor_get(v_inst_463_, 0);
lean_inc_ref(v_toApplicative_512_);
v_toBind_513_ = lean_ctor_get(v_inst_463_, 1);
lean_inc_n(v_toBind_513_, 3);
lean_dec_ref(v_inst_463_);
v___f_514_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__6));
lean_inc_n(v_inst_465_, 2);
lean_inc_n(v_a_467_, 3);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_515_, 0, v_toApplicative_512_);
lean_closure_set(v___f_515_, 1, v_a_467_);
lean_closure_set(v___f_515_, 2, v_inst_465_);
lean_closure_set(v___f_515_, 3, v_toBind_513_);
v___f_516_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_516_, 0, v_x_466_);
lean_closure_set(v___f_516_, 1, v___x_511_);
lean_closure_set(v___f_516_, 2, v_inst_464_);
lean_closure_set(v___f_516_, 3, v_toBind_513_);
lean_closure_set(v___f_516_, 4, v___f_515_);
lean_closure_set(v___f_516_, 5, v_a_467_);
lean_closure_set(v___f_516_, 6, v___f_514_);
lean_closure_set(v___f_516_, 7, v_inst_465_);
v___x_517_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_517_, 0, lean_box(0));
lean_closure_set(v___x_517_, 1, lean_box(0));
lean_closure_set(v___x_517_, 2, v_a_467_);
v___x_518_ = lean_apply_2(v_inst_465_, lean_box(0), v___x_517_);
v___x_519_ = lean_apply_4(v_toBind_513_, lean_box(0), lean_box(0), v___x_518_, v___f_516_);
return v___x_519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___boxed(lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_x_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_526_, v_inst_527_, v_inst_528_, v_x_529_, v_a_530_);
lean_dec(v_a_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM(lean_object* v_00_u03c3_532_, lean_object* v_m_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_00_u03b1_538_, lean_object* v_x_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_535_, v_inst_536_, v_inst_537_, v_x_539_, v_a_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___boxed(lean_object* v_00_u03c3_542_, lean_object* v_m_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_00_u03b1_548_, lean_object* v_x_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM(v_00_u03c3_542_, v_m_543_, v_inst_544_, v_inst_545_, v_inst_546_, v_inst_547_, v_00_u03b1_548_, v_x_549_, v_a_550_);
lean_dec(v_a_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__0(lean_object* v_s_552_){
_start:
{
lean_object* v_reifyState_553_; lean_object* v_preProcessState_554_; lean_object* v_bvSolver_555_; lean_object* v_mvar_556_; lean_object* v_ctx_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_566_; 
v_reifyState_553_ = lean_ctor_get(v_s_552_, 0);
v_preProcessState_554_ = lean_ctor_get(v_s_552_, 1);
v_bvSolver_555_ = lean_ctor_get(v_s_552_, 2);
v_mvar_556_ = lean_ctor_get(v_s_552_, 3);
v_ctx_557_ = lean_ctor_get(v_s_552_, 4);
v_isSharedCheck_566_ = !lean_is_exclusive(v_s_552_);
if (v_isSharedCheck_566_ == 0)
{
v___x_559_ = v_s_552_;
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_ctx_557_);
lean_inc(v_mvar_556_);
lean_inc(v_bvSolver_555_);
lean_inc(v_preProcessState_554_);
lean_inc(v_reifyState_553_);
lean_dec(v_s_552_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_reifyState_553_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_bvSolver_555_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_mvar_556_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_ctx_557_);
v___x_563_ = v_reuseFailAlloc_565_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_preProcessState_554_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1(lean_object* v_snd_567_, lean_object* v_s_568_){
_start:
{
lean_object* v_reifyState_569_; lean_object* v_bvSolver_570_; lean_object* v_mvar_571_; lean_object* v_ctx_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_582_; 
v_reifyState_569_ = lean_ctor_get(v_s_568_, 0);
v_bvSolver_570_ = lean_ctor_get(v_s_568_, 2);
v_mvar_571_ = lean_ctor_get(v_s_568_, 3);
v_ctx_572_ = lean_ctor_get(v_s_568_, 4);
v_isSharedCheck_582_ = !lean_is_exclusive(v_s_568_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v_s_568_, 1);
lean_dec(v_unused_583_);
v___x_574_ = v_s_568_;
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_ctx_572_);
lean_inc(v_mvar_571_);
lean_inc(v_bvSolver_570_);
lean_inc(v_reifyState_569_);
lean_dec(v_s_568_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_caches_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v_caches_576_ = lean_ctor_get(v_snd_567_, 0);
v___x_577_ = lean_box(0);
lean_inc_ref(v_caches_576_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v_caches_576_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_reifyState_569_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_caches_576_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_bvSolver_570_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_mvar_571_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_ctx_572_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_577_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1___boxed(lean_object* v_snd_584_, lean_object* v_s_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1(v_snd_584_, v_s_585_);
lean_dec_ref(v_snd_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3(lean_object* v_toApplicative_587_, lean_object* v_a_588_, lean_object* v_inst_589_, lean_object* v_toBind_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_fst_592_ = lean_ctor_get(v_a_591_, 0);
lean_inc(v_fst_592_);
v_snd_593_ = lean_ctor_get(v_a_591_, 1);
lean_inc(v_snd_593_);
lean_dec_ref(v_a_591_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_594_, 0, v_snd_593_);
v___f_595_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_595_, 0, v_toApplicative_587_);
lean_closure_set(v___f_595_, 1, v_fst_592_);
lean_inc(v_a_588_);
v___x_596_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_596_, 0, lean_box(0));
lean_closure_set(v___x_596_, 1, lean_box(0));
lean_closure_set(v___x_596_, 2, lean_box(0));
lean_closure_set(v___x_596_, 3, v_a_588_);
lean_closure_set(v___x_596_, 4, v___f_594_);
v___x_597_ = lean_apply_2(v_inst_589_, lean_box(0), v___x_596_);
v___x_598_ = lean_apply_4(v_toBind_590_, lean_box(0), lean_box(0), v___x_597_, v___f_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3___boxed(lean_object* v_toApplicative_599_, lean_object* v_a_600_, lean_object* v_inst_601_, lean_object* v_toBind_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3(v_toApplicative_599_, v_a_600_, v_inst_601_, v_toBind_602_, v_a_603_);
lean_dec(v_a_600_);
return v_res_604_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_box(0);
v___x_606_ = lean_unsigned_to_nat(16u);
v___x_607_ = lean_mk_array(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1);
v___x_612_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
lean_ctor_set(v___x_612_, 2, v___x_611_);
lean_ctor_set(v___x_612_, 3, v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__4(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__3));
v___x_616_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1);
v___x_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_ctor_set(v___x_617_, 2, v___x_616_);
lean_ctor_set(v___x_617_, 3, v___x_615_);
lean_ctor_set(v___x_617_, 4, v___x_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2(lean_object* v_a_618_, lean_object* v_x_619_, lean_object* v___x_620_, lean_object* v_target_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_typeAnalysis_642_; lean_object* v_target_643_; lean_object* v_hypotheses_644_; uint8_t v_didChange_645_; lean_object* v_eprBvProblem_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_673_; 
v___x_632_ = l_Lean_Expr_mvarId_x21(v_target_621_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2);
v___x_635_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2);
v___x_636_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0));
v___x_637_ = 0;
v___x_638_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__4);
v___x_639_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_639_, 0, v___x_634_);
lean_ctor_set(v___x_639_, 1, v___x_635_);
lean_ctor_set(v___x_639_, 2, v___x_633_);
lean_ctor_set(v___x_639_, 3, v___x_636_);
lean_ctor_set(v___x_639_, 4, v___x_638_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*5, v___x_637_);
v___x_640_ = lean_st_mk_ref(v___x_639_);
v___x_641_ = lean_st_ref_take(v___x_640_);
v_typeAnalysis_642_ = lean_ctor_get(v___x_641_, 1);
v_target_643_ = lean_ctor_get(v___x_641_, 2);
v_hypotheses_644_ = lean_ctor_get(v___x_641_, 3);
v_didChange_645_ = lean_ctor_get_uint8(v___x_641_, sizeof(void*)*5);
v_eprBvProblem_646_ = lean_ctor_get(v___x_641_, 4);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_641_, 0);
lean_dec(v_unused_674_);
v___x_648_ = v___x_641_;
v_isShared_649_ = v_isSharedCheck_673_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_eprBvProblem_646_);
lean_inc(v_hypotheses_644_);
lean_inc(v_target_643_);
lean_inc(v_typeAnalysis_642_);
lean_dec(v___x_641_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_673_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v_a_618_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_618_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_typeAnalysis_642_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_target_643_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_hypotheses_644_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_eprBvProblem_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_672_, sizeof(void*)*5, v_didChange_645_);
v___x_651_ = v_reuseFailAlloc_672_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_st_ref_put(v___x_640_, v___x_651_);
lean_inc(v___y_630_);
lean_inc_ref(v___y_629_);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
lean_inc(v___y_626_);
lean_inc_ref(v___y_625_);
lean_inc(v___y_624_);
lean_inc_ref(v___y_623_);
lean_inc(v___y_622_);
lean_inc(v___x_640_);
v___x_653_ = lean_apply_12(v_x_619_, v___x_620_, v___x_640_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, lean_box(0));
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_663_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_663_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_658_ = lean_st_ref_get(v___x_640_);
lean_dec(v___x_640_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_a_654_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v___x_640_);
v_a_664_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_653_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_653_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___boxed(lean_object* v_a_675_, lean_object* v_x_676_, lean_object* v___x_677_, lean_object* v_target_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2(v_a_675_, v_x_676_, v___x_677_, v_target_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v_target_678_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4(lean_object* v___x_690_, uint8_t v___x_691_, lean_object* v___x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Meta_mkFreshExprMVar(v___x_690_, v___x_691_, v___x_692_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4___boxed(lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
uint8_t v___x_1969__boxed_717_; lean_object* v_res_718_; 
v___x_1969__boxed_717_ = lean_unbox(v___x_705_);
v_res_718_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4(v___x_704_, v___x_1969__boxed_717_, v___x_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
return v_res_718_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
v___x_723_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__1));
v___x_724_ = l_Lean_mkConst(v___x_723_, v___x_722_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2);
v___x_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___f_731_; 
v___x_727_ = lean_box(0);
v___x_728_ = 0;
v___x_729_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3);
v___x_730_ = lean_box(v___x_728_);
v___f_731_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4___boxed), 13, 3);
lean_closure_set(v___f_731_, 0, v___x_729_);
lean_closure_set(v___f_731_, 1, v___x_730_);
lean_closure_set(v___f_731_, 2, v___x_727_);
return v___f_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5(lean_object* v_x_732_, lean_object* v___x_733_, lean_object* v___x_734_, lean_object* v___x_735_, lean_object* v_mvar_736_, lean_object* v___x_737_, lean_object* v_inst_738_, lean_object* v_toBind_739_, lean_object* v___f_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___f_742_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___boxed), 14, 3);
lean_closure_set(v___f_742_, 0, v_a_741_);
lean_closure_set(v___f_742_, 1, v_x_732_);
lean_closure_set(v___f_742_, 2, v___x_733_);
v___f_743_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4);
v___x_744_ = l_Lean_MVarId_withContext___redArg(v___x_734_, v___x_735_, v_mvar_736_, v___f_743_);
v___x_745_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_745_, 0, lean_box(0));
lean_closure_set(v___x_745_, 1, lean_box(0));
lean_closure_set(v___x_745_, 2, v___x_737_);
lean_closure_set(v___x_745_, 3, lean_box(0));
lean_closure_set(v___x_745_, 4, lean_box(0));
lean_closure_set(v___x_745_, 5, v___x_744_);
lean_closure_set(v___x_745_, 6, v___f_742_);
v___x_746_ = lean_apply_2(v_inst_738_, lean_box(0), v___x_745_);
v___x_747_ = lean_apply_4(v_toBind_739_, lean_box(0), lean_box(0), v___x_746_, v___f_740_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6(lean_object* v_x_748_, lean_object* v___x_749_, lean_object* v___x_750_, lean_object* v___x_751_, lean_object* v___x_752_, lean_object* v_inst_753_, lean_object* v_toBind_754_, lean_object* v___f_755_, lean_object* v_a_756_, lean_object* v___f_757_, lean_object* v_inst_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_mvar_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_mvar_760_ = lean_ctor_get(v_a_759_, 3);
lean_inc(v_mvar_760_);
lean_dec_ref(v_a_759_);
lean_inc(v_toBind_754_);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5), 10, 9);
lean_closure_set(v___f_761_, 0, v_x_748_);
lean_closure_set(v___f_761_, 1, v___x_749_);
lean_closure_set(v___f_761_, 2, v___x_750_);
lean_closure_set(v___f_761_, 3, v___x_751_);
lean_closure_set(v___f_761_, 4, v_mvar_760_);
lean_closure_set(v___f_761_, 5, v___x_752_);
lean_closure_set(v___f_761_, 6, v_inst_753_);
lean_closure_set(v___f_761_, 7, v_toBind_754_);
lean_closure_set(v___f_761_, 8, v___f_755_);
lean_inc(v_a_756_);
v___x_762_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_762_, 0, lean_box(0));
lean_closure_set(v___x_762_, 1, lean_box(0));
lean_closure_set(v___x_762_, 2, lean_box(0));
lean_closure_set(v___x_762_, 3, v_a_756_);
lean_closure_set(v___x_762_, 4, v___f_757_);
v___x_763_ = lean_apply_2(v_inst_758_, lean_box(0), v___x_762_);
v___x_764_ = lean_apply_4(v_toBind_754_, lean_box(0), lean_box(0), v___x_763_, v___f_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6___boxed(lean_object* v_x_765_, lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v___x_769_, lean_object* v_inst_770_, lean_object* v_toBind_771_, lean_object* v___f_772_, lean_object* v_a_773_, lean_object* v___f_774_, lean_object* v_inst_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6(v_x_765_, v___x_766_, v___x_767_, v___x_768_, v___x_769_, v_inst_770_, v_toBind_771_, v___f_772_, v_a_773_, v___f_774_, v_inst_775_, v_a_776_);
lean_dec(v_a_773_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7(lean_object* v_x_781_, lean_object* v___x_782_, lean_object* v___x_783_, lean_object* v___x_784_, lean_object* v_inst_785_, lean_object* v_toBind_786_, lean_object* v___f_787_, lean_object* v_a_788_, lean_object* v___f_789_, lean_object* v_inst_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_ctx_792_; lean_object* v___x_793_; lean_object* v_config_794_; lean_object* v_mode_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___f_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_ctx_792_ = lean_ctor_get(v_a_791_, 4);
lean_inc_ref(v_ctx_792_);
lean_dec_ref(v_a_791_);
v___x_793_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_792_);
v_config_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc_ref(v_config_794_);
v_mode_795_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_mode_795_);
lean_dec_ref(v___x_793_);
v___x_796_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___closed__0));
v___x_797_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_795_, v_config_794_, v___x_796_);
lean_inc(v_inst_790_);
lean_inc_n(v_a_788_, 2);
lean_inc(v_toBind_786_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6___boxed), 12, 11);
lean_closure_set(v___f_798_, 0, v_x_781_);
lean_closure_set(v___f_798_, 1, v___x_797_);
lean_closure_set(v___f_798_, 2, v___x_782_);
lean_closure_set(v___f_798_, 3, v___x_783_);
lean_closure_set(v___f_798_, 4, v___x_784_);
lean_closure_set(v___f_798_, 5, v_inst_785_);
lean_closure_set(v___f_798_, 6, v_toBind_786_);
lean_closure_set(v___f_798_, 7, v___f_787_);
lean_closure_set(v___f_798_, 8, v_a_788_);
lean_closure_set(v___f_798_, 9, v___f_789_);
lean_closure_set(v___f_798_, 10, v_inst_790_);
v___x_799_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_799_, 0, lean_box(0));
lean_closure_set(v___x_799_, 1, lean_box(0));
lean_closure_set(v___x_799_, 2, v_a_788_);
v___x_800_ = lean_apply_2(v_inst_790_, lean_box(0), v___x_799_);
v___x_801_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_800_, v___f_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___boxed(lean_object* v_x_802_, lean_object* v___x_803_, lean_object* v___x_804_, lean_object* v___x_805_, lean_object* v_inst_806_, lean_object* v_toBind_807_, lean_object* v___f_808_, lean_object* v_a_809_, lean_object* v___f_810_, lean_object* v_inst_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7(v_x_802_, v___x_803_, v___x_804_, v___x_805_, v_inst_806_, v_toBind_807_, v___f_808_, v_a_809_, v___f_810_, v_inst_811_, v_a_812_);
lean_dec(v_a_809_);
return v_res_813_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0(void){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_instMonadControlReaderT___redArg();
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1(void){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_x_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_822_; lean_object* v_toApplicative_823_; lean_object* v_toFunctor_824_; lean_object* v_toSeq_825_; lean_object* v_toSeqLeft_826_; lean_object* v_toSeqRight_827_; lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_toApplicative_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_912_; 
v___x_822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1);
v_toApplicative_823_ = lean_ctor_get(v___x_822_, 0);
v_toFunctor_824_ = lean_ctor_get(v_toApplicative_823_, 0);
v_toSeq_825_ = lean_ctor_get(v_toApplicative_823_, 2);
v_toSeqLeft_826_ = lean_ctor_get(v_toApplicative_823_, 3);
v_toSeqRight_827_ = lean_ctor_get(v_toApplicative_823_, 4);
v___f_828_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2));
v___f_829_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_824_, 2);
v___f_830_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_830_, 0, v_toFunctor_824_);
v___f_831_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_831_, 0, v_toFunctor_824_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___f_830_);
lean_ctor_set(v___x_832_, 1, v___f_831_);
lean_inc(v_toSeqRight_827_);
v___f_833_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_833_, 0, v_toSeqRight_827_);
lean_inc(v_toSeqLeft_826_);
v___f_834_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_834_, 0, v_toSeqLeft_826_);
lean_inc(v_toSeq_825_);
v___f_835_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_835_, 0, v_toSeq_825_);
v___x_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_836_, 0, v___x_832_);
lean_ctor_set(v___x_836_, 1, v___f_828_);
lean_ctor_set(v___x_836_, 2, v___f_835_);
lean_ctor_set(v___x_836_, 3, v___f_834_);
lean_ctor_set(v___x_836_, 4, v___f_833_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___f_829_);
v___x_838_ = l_StateRefT_x27_instMonad___redArg(v___x_837_);
v_toApplicative_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_838_, 1);
lean_dec(v_unused_913_);
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_912_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_toApplicative_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_912_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_toFunctor_843_; lean_object* v_toSeq_844_; lean_object* v_toSeqLeft_845_; lean_object* v_toSeqRight_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_910_; 
v_toFunctor_843_ = lean_ctor_get(v_toApplicative_839_, 0);
v_toSeq_844_ = lean_ctor_get(v_toApplicative_839_, 2);
v_toSeqLeft_845_ = lean_ctor_get(v_toApplicative_839_, 3);
v_toSeqRight_846_ = lean_ctor_get(v_toApplicative_839_, 4);
v_isSharedCheck_910_ = !lean_is_exclusive(v_toApplicative_839_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_toApplicative_839_, 1);
lean_dec(v_unused_911_);
v___x_848_ = v_toApplicative_839_;
v_isShared_849_ = v_isSharedCheck_910_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_toSeqRight_846_);
lean_inc(v_toSeqLeft_845_);
lean_inc(v_toSeq_844_);
lean_inc(v_toFunctor_843_);
lean_dec(v_toApplicative_839_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_910_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___x_859_; 
v___f_850_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4));
v___f_851_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5));
lean_inc_ref(v_toFunctor_843_);
v___f_852_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_852_, 0, v_toFunctor_843_);
v___f_853_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_853_, 0, v_toFunctor_843_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___f_852_);
lean_ctor_set(v___x_854_, 1, v___f_853_);
v___f_855_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_855_, 0, v_toSeqRight_846_);
v___f_856_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_856_, 0, v_toSeqLeft_845_);
v___f_857_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_857_, 0, v_toSeq_844_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 4, v___f_855_);
lean_ctor_set(v___x_848_, 3, v___f_856_);
lean_ctor_set(v___x_848_, 2, v___f_857_);
lean_ctor_set(v___x_848_, 1, v___f_850_);
lean_ctor_set(v___x_848_, 0, v___x_854_);
v___x_859_ = v___x_848_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___f_850_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v___f_857_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v___f_856_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v___f_855_);
v___x_859_ = v_reuseFailAlloc_909_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___f_851_);
lean_ctor_set(v___x_841_, 0, v___x_859_);
v___x_861_ = v___x_841_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v___f_851_);
v___x_861_ = v_reuseFailAlloc_908_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v_toApplicative_869_; lean_object* v_toFunctor_870_; lean_object* v_toSeq_871_; lean_object* v_toSeqLeft_872_; lean_object* v_toSeqRight_873_; lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v_toApplicative_900_; lean_object* v_toBind_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_862_ = l_StateRefT_x27_instMonad___redArg(v___x_861_);
v___x_863_ = l_ReaderT_instMonad___redArg(v___x_862_);
v___x_864_ = l_StateRefT_x27_instMonad___redArg(v___x_863_);
v___x_865_ = l_ReaderT_instMonad___redArg(v___x_864_);
lean_inc_ref(v___x_865_);
v___x_866_ = l_ReaderT_instMonad___redArg(v___x_865_);
v___x_867_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0);
v___x_868_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1);
v_toApplicative_869_ = lean_ctor_get(v___x_822_, 0);
v_toFunctor_870_ = lean_ctor_get(v_toApplicative_869_, 0);
v_toSeq_871_ = lean_ctor_get(v_toApplicative_869_, 2);
v_toSeqLeft_872_ = lean_ctor_get(v_toApplicative_869_, 3);
v_toSeqRight_873_ = lean_ctor_get(v_toApplicative_869_, 4);
lean_inc_ref_n(v_toFunctor_870_, 2);
v___f_874_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_874_, 0, v_toFunctor_870_);
v___f_875_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_875_, 0, v_toFunctor_870_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___f_874_);
lean_ctor_set(v___x_876_, 1, v___f_875_);
lean_inc(v_toSeqRight_873_);
v___f_877_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_877_, 0, v_toSeqRight_873_);
lean_inc(v_toSeqLeft_872_);
v___f_878_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_878_, 0, v_toSeqLeft_872_);
lean_inc(v_toSeq_871_);
v___f_879_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_879_, 0, v_toSeq_871_);
v___x_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_880_, 0, v___x_876_);
lean_ctor_set(v___x_880_, 1, v___f_828_);
lean_ctor_set(v___x_880_, 2, v___f_879_);
lean_ctor_set(v___x_880_, 3, v___f_878_);
lean_ctor_set(v___x_880_, 4, v___f_877_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v___f_829_);
v___x_882_ = l_StateRefT_x27_instMonad___redArg(v___x_881_);
v___x_883_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_883_, 0, lean_box(0));
lean_closure_set(v___x_883_, 1, lean_box(0));
lean_closure_set(v___x_883_, 2, v___x_882_);
v___x_884_ = l_instMonadControlTOfPure___redArg(v___x_883_);
lean_inc_ref(v___x_884_);
v___f_885_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_885_, 0, v___x_868_);
lean_closure_set(v___f_885_, 1, v___x_884_);
v___f_886_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_886_, 0, v___x_868_);
lean_closure_set(v___f_886_, 1, v___x_884_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___f_885_);
lean_ctor_set(v___x_887_, 1, v___f_886_);
lean_inc_ref(v___x_887_);
v___f_888_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_888_, 0, v___x_867_);
lean_closure_set(v___f_888_, 1, v___x_887_);
v___f_889_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_889_, 0, v___x_867_);
lean_closure_set(v___f_889_, 1, v___x_887_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___f_888_);
lean_ctor_set(v___x_890_, 1, v___f_889_);
lean_inc_ref(v___x_890_);
v___f_891_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_891_, 0, v___x_868_);
lean_closure_set(v___f_891_, 1, v___x_890_);
v___f_892_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_892_, 0, v___x_868_);
lean_closure_set(v___f_892_, 1, v___x_890_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___f_891_);
lean_ctor_set(v___x_893_, 1, v___f_892_);
lean_inc_ref(v___x_893_);
v___f_894_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_894_, 0, v___x_867_);
lean_closure_set(v___f_894_, 1, v___x_893_);
v___f_895_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_895_, 0, v___x_867_);
lean_closure_set(v___f_895_, 1, v___x_893_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___f_894_);
lean_ctor_set(v___x_896_, 1, v___f_895_);
lean_inc_ref(v___x_896_);
v___f_897_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_897_, 0, v___x_867_);
lean_closure_set(v___f_897_, 1, v___x_896_);
v___f_898_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_898_, 0, v___x_867_);
lean_closure_set(v___f_898_, 1, v___x_896_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v___f_897_);
lean_ctor_set(v___x_899_, 1, v___f_898_);
v_toApplicative_900_ = lean_ctor_get(v_inst_817_, 0);
lean_inc_ref(v_toApplicative_900_);
v_toBind_901_ = lean_ctor_get(v_inst_817_, 1);
lean_inc_n(v_toBind_901_, 3);
lean_dec_ref(v_inst_817_);
v___f_902_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__2));
lean_inc_n(v_inst_819_, 2);
lean_inc_n(v_a_821_, 3);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_903_, 0, v_toApplicative_900_);
lean_closure_set(v___f_903_, 1, v_a_821_);
lean_closure_set(v___f_903_, 2, v_inst_819_);
lean_closure_set(v___f_903_, 3, v_toBind_901_);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_904_, 0, v_x_820_);
lean_closure_set(v___f_904_, 1, v___x_899_);
lean_closure_set(v___f_904_, 2, v___x_866_);
lean_closure_set(v___f_904_, 3, v___x_865_);
lean_closure_set(v___f_904_, 4, v_inst_818_);
lean_closure_set(v___f_904_, 5, v_toBind_901_);
lean_closure_set(v___f_904_, 6, v___f_903_);
lean_closure_set(v___f_904_, 7, v_a_821_);
lean_closure_set(v___f_904_, 8, v___f_902_);
lean_closure_set(v___f_904_, 9, v_inst_819_);
v___x_905_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_905_, 0, lean_box(0));
lean_closure_set(v___x_905_, 1, lean_box(0));
lean_closure_set(v___x_905_, 2, v_a_821_);
v___x_906_ = lean_apply_2(v_inst_819_, lean_box(0), v___x_905_);
v___x_907_ = lean_apply_4(v_toBind_901_, lean_box(0), lean_box(0), v___x_906_, v___f_904_);
return v___x_907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___boxed(lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_x_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(v_inst_914_, v_inst_915_, v_inst_916_, v_x_917_, v_a_918_);
lean_dec(v_a_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM(lean_object* v_00_u03c3_920_, lean_object* v_m_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_00_u03b1_926_, lean_object* v_x_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(v_inst_923_, v_inst_924_, v_inst_925_, v_x_927_, v_a_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___boxed(lean_object* v_00_u03c3_930_, lean_object* v_m_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_00_u03b1_936_, lean_object* v_x_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM(v_00_u03c3_930_, v_m_931_, v_inst_932_, v_inst_933_, v_inst_934_, v_inst_935_, v_00_u03b1_936_, v_x_937_, v_a_938_);
lean_dec(v_a_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__0(lean_object* v_x_940_){
_start:
{
lean_object* v_bvExpr_941_; 
v_bvExpr_941_ = lean_ctor_get(v_x_940_, 0);
lean_inc_ref(v_bvExpr_941_);
return v_bvExpr_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__0___boxed(lean_object* v_x_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__0(v_x_942_);
lean_dec_ref(v_x_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1(lean_object* v___f_963_, lean_object* v_____x_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_979_; lean_object* v___x_980_; size_t v_sz_981_; size_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_fst_977_ = lean_ctor_get(v_____x_964_, 0);
lean_inc(v_fst_977_);
v_snd_978_ = lean_ctor_get(v_____x_964_, 1);
lean_inc(v_snd_978_);
lean_dec_ref(v_____x_964_);
v___x_979_ = l_Array_append___redArg(v_snd_978_, v_fst_977_);
lean_dec(v_fst_977_);
v___x_980_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___closed__9));
v_sz_981_ = lean_array_size(v___x_979_);
v___x_982_ = ((size_t)0ULL);
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_980_, v___f_963_, v_sz_981_, v___x_982_, v___x_979_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1___boxed(lean_object* v___f_985_, lean_object* v_____x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__1(v___f_985_, v_____x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_999_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__4(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__3));
v___x_1006_ = l_Lean_stringToMessageData(v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2(lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v_hyp_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__0));
v___x_1024_ = l_Lean_Core_checkSystem(v___x_1023_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1042_; 
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v___x_1024_, 0);
lean_dec(v_unused_1043_);
v___x_1026_ = v___x_1024_;
v_isShared_1027_ = v_isSharedCheck_1042_;
goto v_resetjp_1025_;
}
else
{
lean_dec(v___x_1024_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1042_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_type_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_type_1028_ = lean_ctor_get(v_hyp_1009_, 1);
lean_inc_ref(v_type_1028_);
v___x_1029_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__2));
v___x_1030_ = l_Lean_Expr_isConstOf(v_type_1028_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_del_object(v___x_1026_);
v___x_1031_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_hyp_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
if (lean_obj_tag(v_a_1032_) == 1)
{
lean_dec_ref(v_type_1028_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v___x_1007_);
return v___x_1031_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_3557__overap_1036_; lean_object* v___x_1037_; 
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___closed__4);
v___x_1034_ = l_Lean_MessageData_ofExpr(v_type_1028_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_3557__overap_1036_ = l_Lean_throwError___redArg(v___x_1007_, v___x_1008_, v___x_1035_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
v___x_1037_ = lean_apply_13(v___x_3557__overap_1036_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
return v___x_1037_;
}
}
else
{
lean_dec_ref(v_type_1028_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v___x_1007_);
return v___x_1031_;
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
lean_dec_ref(v_type_1028_);
lean_dec_ref(v_hyp_1009_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v___x_1007_);
v___x_1038_ = lean_box(0);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1038_);
v___x_1040_ = v___x_1026_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v_hyp_1009_);
lean_dec_ref(v___x_1008_);
lean_dec_ref(v___x_1007_);
v_a_1044_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1024_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1024_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___boxed(lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v_hyp_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2(v___x_1052_, v___x_1053_, v_hyp_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
return v_res_1068_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__2(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___f_1072_; 
v___x_1071_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1072_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1072_, 0, v___x_1071_);
return v___f_1072_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__3(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___f_1074_; 
v___x_1073_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1074_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1074_, 0, v___x_1073_);
return v___f_1074_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4(void){
_start:
{
lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; 
v___f_1075_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__3);
v___f_1076_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__2);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___f_1076_);
lean_ctor_set(v___x_1077_, 1, v___f_1075_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__5(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___f_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4);
v___f_1079_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1079_, 0, v___x_1078_);
return v___f_1079_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__6(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___f_1081_; 
v___x_1080_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__4);
v___f_1081_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1081_, 0, v___x_1080_);
return v___f_1081_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7(void){
_start:
{
lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___f_1082_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__6);
v___f_1083_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__5);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___f_1083_);
lean_ctor_set(v___x_1084_, 1, v___f_1082_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__8(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___f_1086_; 
v___x_1085_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7);
v___f_1086_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1086_, 0, v___x_1085_);
return v___f_1086_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__9(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___f_1088_; 
v___x_1087_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__7);
v___f_1088_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1088_, 0, v___x_1087_);
return v___f_1088_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10(void){
_start:
{
lean_object* v___f_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; 
v___f_1089_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__9);
v___f_1090_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__8);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___f_1090_);
lean_ctor_set(v___x_1091_, 1, v___f_1089_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__11(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___f_1093_; 
v___x_1092_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10);
v___f_1093_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1093_, 0, v___x_1092_);
return v___f_1093_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__12(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___f_1095_; 
v___x_1094_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__10);
v___f_1095_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1095_, 0, v___x_1094_);
return v___f_1095_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13(void){
_start:
{
lean_object* v___f_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; 
v___f_1096_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__12, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__12);
v___f_1097_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__11, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__11);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___f_1097_);
lean_ctor_set(v___x_1098_, 1, v___f_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__14(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___f_1100_; 
v___x_1099_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13);
v___f_1100_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1100_, 0, v___x_1099_);
return v___f_1100_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__15(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___f_1102_; 
v___x_1101_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__13);
v___f_1102_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1102_, 0, v___x_1101_);
return v___f_1102_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16(void){
_start:
{
lean_object* v___f_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; 
v___f_1103_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__15);
v___f_1104_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__14, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__14);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___f_1104_);
lean_ctor_set(v___x_1105_, 1, v___f_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__17(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___f_1107_; 
v___x_1106_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16);
v___f_1107_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1107_, 0, v___x_1106_);
return v___f_1107_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__18(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___f_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__16);
v___f_1109_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1109_, 0, v___x_1108_);
return v___f_1109_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19(void){
_start:
{
lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___f_1110_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__18, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__18);
v___f_1111_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__17, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__17);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___f_1111_);
lean_ctor_set(v___x_1112_, 1, v___f_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__20(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___f_1114_; 
v___x_1113_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19);
v___f_1114_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1114_, 0, v___x_1113_);
return v___f_1114_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__21(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___f_1116_; 
v___x_1115_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__19);
v___f_1116_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1116_, 0, v___x_1115_);
return v___f_1116_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22(void){
_start:
{
lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v___x_1119_; 
v___f_1117_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__21, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__21);
v___f_1118_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__20, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__20);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___f_1118_);
lean_ctor_set(v___x_1119_, 1, v___f_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__23(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___f_1121_; 
v___x_1120_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22);
v___f_1121_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1121_, 0, v___x_1120_);
return v___f_1121_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__24(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___f_1123_; 
v___x_1122_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__22);
v___f_1123_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1123_, 0, v___x_1122_);
return v___f_1123_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25(void){
_start:
{
lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; 
v___f_1124_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__24, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__24);
v___f_1125_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__23, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__23);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___f_1125_);
lean_ctor_set(v___x_1126_, 1, v___f_1124_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__26(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___f_1128_; 
v___x_1127_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25);
v___f_1128_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1128_, 0, v___x_1127_);
return v___f_1128_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__27(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___f_1130_; 
v___x_1129_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__25);
v___f_1130_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1130_, 0, v___x_1129_);
return v___f_1130_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28(void){
_start:
{
lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___f_1131_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__27, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__27);
v___f_1132_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__26, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__26_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__26);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___f_1132_);
lean_ctor_set(v___x_1133_, 1, v___f_1131_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__29(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___f_1135_; 
v___x_1134_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28);
v___f_1135_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1135_, 0, v___x_1134_);
return v___f_1135_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__30(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___f_1137_; 
v___x_1136_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__28);
v___f_1137_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1137_, 0, v___x_1136_);
return v___f_1137_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__31(void){
_start:
{
lean_object* v___f_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; 
v___f_1138_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__30, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__30);
v___f_1139_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__29, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__29);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___f_1139_);
lean_ctor_set(v___x_1140_, 1, v___f_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__34(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1144_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___x_1145_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__32));
v___x_1146_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1145_, v___x_1144_, v___x_1143_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__35(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___f_1149_; lean_object* v___x_1150_; 
v___x_1147_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__34, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__34);
v___f_1148_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__33));
v___x_1150_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1149_, v___f_1148_, v___x_1147_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__36(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__35, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__35);
v___x_1152_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___x_1153_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__32));
v___x_1154_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1153_, v___x_1152_, v___x_1151_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__37(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___f_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__36, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__36_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__36);
v___f_1156_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1157_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__33));
v___x_1158_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1157_, v___f_1156_, v___x_1155_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__38(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1159_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__37, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__37);
v___x_1160_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___x_1161_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__32));
v___x_1162_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1161_, v___x_1160_, v___x_1159_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__39(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
v___x_1163_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__38, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__38_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__38);
v___f_1164_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1165_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__33));
v___x_1166_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1165_, v___f_1164_, v___x_1163_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__40(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; 
v___x_1167_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__39, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__39_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__39);
v___f_1168_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1169_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__33));
v___x_1170_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1169_, v___f_1168_, v___x_1167_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__41(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__40, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__40_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__40);
v___x_1172_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___x_1173_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__32));
v___x_1174_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1173_, v___x_1172_, v___x_1171_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__42(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; 
v___x_1175_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__41, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__41_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__41);
v___f_1176_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1177_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__33));
v___x_1178_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1177_, v___f_1176_, v___x_1175_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__43(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1179_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__42, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__42_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__42);
v___x_1180_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___x_1181_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__32));
v___x_1182_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1181_, v___x_1180_, v___x_1179_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__46(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___f_1188_; 
v___x_1186_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___x_1187_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1188_, 0, v___x_1187_);
lean_closure_set(v___f_1188_, 1, v___x_1186_);
return v___f_1188_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__47(void){
_start:
{
lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; 
v___f_1189_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1190_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__46, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__46_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__46);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1191_, 0, v___f_1190_);
lean_closure_set(v___f_1191_, 1, v___f_1189_);
return v___f_1191_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__48(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___f_1193_; lean_object* v___f_1194_; 
v___x_1192_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___f_1193_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__47, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__47_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__47);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1194_, 0, v___f_1193_);
lean_closure_set(v___f_1194_, 1, v___x_1192_);
return v___f_1194_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__49(void){
_start:
{
lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___f_1197_; 
v___f_1195_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1196_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__48, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__48_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__48);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1197_, 0, v___f_1196_);
lean_closure_set(v___f_1197_, 1, v___f_1195_);
return v___f_1197_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__50(void){
_start:
{
lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; 
v___f_1198_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1199_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__49, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__49_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__49);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1200_, 0, v___f_1199_);
lean_closure_set(v___f_1200_, 1, v___f_1198_);
return v___f_1200_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__51(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; 
v___x_1201_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___f_1202_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__50, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__50_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__50);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1203_, 0, v___f_1202_);
lean_closure_set(v___f_1203_, 1, v___x_1201_);
return v___f_1203_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__52(void){
_start:
{
lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; 
v___f_1204_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__1));
v___f_1205_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__51, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__51_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__51);
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1206_, 0, v___f_1205_);
lean_closure_set(v___f_1206_, 1, v___f_1204_);
return v___f_1206_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__53(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; 
v___x_1207_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__0));
v___f_1208_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__52, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__52_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__52);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1209_, 0, v___f_1208_);
lean_closure_set(v___f_1209_, 1, v___x_1207_);
return v___f_1209_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__55(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0___closed__1);
v___x_1213_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__54));
v___x_1214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1212_);
lean_ctor_set(v___x_1214_, 2, v___x_1212_);
lean_ctor_set(v___x_1214_, 3, v___x_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg(lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_hyps_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v_toApplicative_1221_; lean_object* v_toFunctor_1222_; lean_object* v_toSeq_1223_; lean_object* v_toSeqLeft_1224_; lean_object* v_toSeqRight_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_toApplicative_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1287_; 
v___x_1220_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1);
v_toApplicative_1221_ = lean_ctor_get(v___x_1220_, 0);
v_toFunctor_1222_ = lean_ctor_get(v_toApplicative_1221_, 0);
v_toSeq_1223_ = lean_ctor_get(v_toApplicative_1221_, 2);
v_toSeqLeft_1224_ = lean_ctor_get(v_toApplicative_1221_, 3);
v_toSeqRight_1225_ = lean_ctor_get(v_toApplicative_1221_, 4);
v___f_1226_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2));
v___f_1227_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1222_, 2);
v___f_1228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1228_, 0, v_toFunctor_1222_);
v___f_1229_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1229_, 0, v_toFunctor_1222_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___f_1228_);
lean_ctor_set(v___x_1230_, 1, v___f_1229_);
lean_inc(v_toSeqRight_1225_);
v___f_1231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1231_, 0, v_toSeqRight_1225_);
lean_inc(v_toSeqLeft_1224_);
v___f_1232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1232_, 0, v_toSeqLeft_1224_);
lean_inc(v_toSeq_1223_);
v___f_1233_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1233_, 0, v_toSeq_1223_);
v___x_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1230_);
lean_ctor_set(v___x_1234_, 1, v___f_1226_);
lean_ctor_set(v___x_1234_, 2, v___f_1233_);
lean_ctor_set(v___x_1234_, 3, v___f_1232_);
lean_ctor_set(v___x_1234_, 4, v___f_1231_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v___f_1227_);
v___x_1236_ = l_StateRefT_x27_instMonad___redArg(v___x_1235_);
v_toApplicative_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v___x_1236_, 1);
lean_dec(v_unused_1288_);
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1287_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_toApplicative_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1287_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_toFunctor_1241_; lean_object* v_toSeq_1242_; lean_object* v_toSeqLeft_1243_; lean_object* v_toSeqRight_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1285_; 
v_toFunctor_1241_ = lean_ctor_get(v_toApplicative_1237_, 0);
v_toSeq_1242_ = lean_ctor_get(v_toApplicative_1237_, 2);
v_toSeqLeft_1243_ = lean_ctor_get(v_toApplicative_1237_, 3);
v_toSeqRight_1244_ = lean_ctor_get(v_toApplicative_1237_, 4);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_toApplicative_1237_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v_toApplicative_1237_, 1);
lean_dec(v_unused_1286_);
v___x_1246_ = v_toApplicative_1237_;
v_isShared_1247_ = v_isSharedCheck_1285_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_toSeqRight_1244_);
lean_inc(v_toSeqLeft_1243_);
lean_inc(v_toSeq_1242_);
lean_inc(v_toFunctor_1241_);
lean_dec(v_toApplicative_1237_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1285_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; lean_object* v___f_1253_; lean_object* v___f_1254_; lean_object* v___f_1255_; lean_object* v___x_1257_; 
v___f_1248_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4));
v___f_1249_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5));
lean_inc_ref(v_toFunctor_1241_);
v___f_1250_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1250_, 0, v_toFunctor_1241_);
v___f_1251_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1251_, 0, v_toFunctor_1241_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___f_1250_);
lean_ctor_set(v___x_1252_, 1, v___f_1251_);
v___f_1253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1253_, 0, v_toSeqRight_1244_);
v___f_1254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1254_, 0, v_toSeqLeft_1243_);
v___f_1255_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1255_, 0, v_toSeq_1242_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 4, v___f_1253_);
lean_ctor_set(v___x_1246_, 3, v___f_1254_);
lean_ctor_set(v___x_1246_, 2, v___f_1255_);
lean_ctor_set(v___x_1246_, 1, v___f_1248_);
lean_ctor_set(v___x_1246_, 0, v___x_1252_);
v___x_1257_ = v___x_1246_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___f_1248_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v___f_1255_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v___f_1254_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v___f_1253_);
v___x_1257_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___f_1249_);
lean_ctor_set(v___x_1239_, 0, v___x_1257_);
v___x_1259_ = v___x_1239_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___f_1249_);
v___x_1259_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_toMonadRef_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1260_ = l_StateRefT_x27_instMonad___redArg(v___x_1259_);
v___x_1261_ = l_ReaderT_instMonad___redArg(v___x_1260_);
v___x_1262_ = l_StateRefT_x27_instMonad___redArg(v___x_1261_);
v___x_1263_ = l_ReaderT_instMonad___redArg(v___x_1262_);
v___x_1264_ = l_ReaderT_instMonad___redArg(v___x_1263_);
v___x_1265_ = l_StateRefT_x27_instMonad___redArg(v___x_1264_);
lean_inc_ref(v___x_1265_);
v___x_1266_ = l_ReaderT_instMonad___redArg(v___x_1265_);
v___x_1267_ = l_StateRefT_x27_instMonad___redArg(v___x_1266_);
v___x_1268_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__31, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__31);
v___x_1269_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__43, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__43_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__43);
v_toMonadRef_1270_ = lean_ctor_get(v___x_1269_, 0);
v___f_1271_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__45));
v___f_1272_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__53, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__53_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__53);
lean_inc_ref_n(v___x_1267_, 2);
v___x_1273_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1272_, v___x_1267_);
lean_inc_ref(v_toMonadRef_1270_);
v___x_1274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1268_);
lean_ctor_set(v___x_1274_, 1, v_toMonadRef_1270_);
lean_ctor_set(v___x_1274_, 2, v___x_1273_);
v___f_1275_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___lam__2___boxed), 16, 2);
lean_closure_set(v___f_1275_, 0, v___x_1267_);
lean_closure_set(v___f_1275_, 1, v___x_1274_);
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = lean_array_get_size(v_hyps_1218_);
v___x_1278_ = l_Array_filterMapM___redArg(v___x_1267_, v___f_1275_, v_hyps_1218_, v___x_1276_, v___x_1277_);
v___x_1279_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__55, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__55_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___closed__55);
v___x_1280_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed), 15, 3);
lean_closure_set(v___x_1280_, 0, lean_box(0));
lean_closure_set(v___x_1280_, 1, v___x_1278_);
lean_closure_set(v___x_1280_, 2, v___x_1279_);
v___x_1281_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1281_, 0, lean_box(0));
lean_closure_set(v___x_1281_, 1, lean_box(0));
lean_closure_set(v___x_1281_, 2, v___x_1265_);
lean_closure_set(v___x_1281_, 3, lean_box(0));
lean_closure_set(v___x_1281_, 4, lean_box(0));
lean_closure_set(v___x_1281_, 5, v___x_1280_);
lean_closure_set(v___x_1281_, 6, v___f_1271_);
v___x_1282_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_1215_, v_inst_1216_, v_inst_1217_, v___x_1281_, v_a_1219_);
return v___x_1282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg___boxed(lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_hyps_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg(v_inst_1289_, v_inst_1290_, v_inst_1291_, v_hyps_1292_, v_a_1293_);
lean_dec(v_a_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized(lean_object* v_00_u03c3_1295_, lean_object* v_m_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_hyps_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg(v_inst_1298_, v_inst_1299_, v_inst_1300_, v_hyps_1301_, v_a_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___boxed(lean_object* v_00_u03c3_1304_, lean_object* v_m_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_hyps_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized(v_00_u03c3_1304_, v_m_1305_, v_inst_1306_, v_inst_1307_, v_inst_1308_, v_inst_1309_, v_hyps_1310_, v_a_1311_);
lean_dec(v_a_1311_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___redArg(lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_bvExprs_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_BvSolverM_push___boxed), 10, 1);
lean_closure_set(v___x_1318_, 0, v_bvExprs_1316_);
v___x_1319_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_1313_, v_inst_1314_, v_inst_1315_, v___x_1318_, v_a_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___redArg___boxed(lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_bvExprs_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___redArg(v_inst_1320_, v_inst_1321_, v_inst_1322_, v_bvExprs_1323_, v_a_1324_);
lean_dec(v_a_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified(lean_object* v_00_u03c3_1326_, lean_object* v_m_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_bvExprs_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___redArg(v_inst_1329_, v_inst_1330_, v_inst_1331_, v_bvExprs_1332_, v_a_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___boxed(lean_object* v_00_u03c3_1335_, lean_object* v_m_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_bvExprs_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified(v_00_u03c3_1335_, v_m_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_inst_1340_, v_bvExprs_1341_, v_a_1342_);
lean_dec(v_a_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0(lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushReified___redArg(v_inst_1344_, v_inst_1345_, v_inst_1346_, v_a_1348_, v_a_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___boxed(lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0(v_inst_1350_, v_inst_1351_, v_inst_1352_, v_a_1353_, v_a_1354_);
lean_dec(v_a_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_hyps_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_toBind_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_toBind_1362_ = lean_ctor_get(v_inst_1356_, 1);
lean_inc(v_toBind_1362_);
lean_inc(v_a_1361_);
lean_inc(v_inst_1359_);
lean_inc_ref(v_inst_1356_);
v___f_1363_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1363_, 0, v_inst_1356_);
lean_closure_set(v___f_1363_, 1, v_inst_1357_);
lean_closure_set(v___f_1363_, 2, v_inst_1359_);
lean_closure_set(v___f_1363_, 3, v_a_1361_);
v___x_1364_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_reifyNormalized___redArg(v_inst_1356_, v_inst_1358_, v_inst_1359_, v_hyps_1360_, v_a_1361_);
v___x_1365_ = lean_apply_4(v_toBind_1362_, lean_box(0), lean_box(0), v___x_1364_, v___f_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___boxed(lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_hyps_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(v_inst_1366_, v_inst_1367_, v_inst_1368_, v_inst_1369_, v_hyps_1370_, v_a_1371_);
lean_dec(v_a_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized(lean_object* v_00_u03c3_1373_, lean_object* v_m_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_hyps_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(v_inst_1376_, v_inst_1377_, v_inst_1378_, v_inst_1379_, v_hyps_1380_, v_a_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___boxed(lean_object* v_00_u03c3_1383_, lean_object* v_m_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_hyps_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized(v_00_u03c3_1383_, v_m_1384_, v_inst_1385_, v_inst_1386_, v_inst_1387_, v_inst_1388_, v_inst_1389_, v_hyps_1390_, v_a_1391_);
lean_dec(v_a_1391_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0(uint8_t v_____do__lift_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
if (v_____do__lift_1393_ == 0)
{
lean_object* v___x_1406_; lean_object* v_hypotheses_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1406_ = lean_st_ref_get(v___y_1395_);
v_hypotheses_1407_ = lean_ctor_get(v___x_1406_, 3);
lean_inc_ref(v_hypotheses_1407_);
lean_dec(v___x_1406_);
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_hypotheses_1407_);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0___boxed(lean_object* v_____do__lift_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
uint8_t v_____do__lift_1248__boxed_1425_; lean_object* v_res_1426_; 
v_____do__lift_1248__boxed_1425_ = lean_unbox(v_____do__lift_1412_);
v_res_1426_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0(v_____do__lift_1248__boxed_1425_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1426_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0(void){
_start:
{
uint8_t v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = 0;
v___x_1428_ = l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1429_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0);
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1430_);
v___x_1432_ = lean_array_push(v___x_1431_, v___x_1429_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1);
v___x_1434_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_BvSolverM_push___boxed), 10, 1);
lean_closure_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1(lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_a_1438_, lean_object* v_inst_1439_, lean_object* v_a_1440_){
_start:
{
if (lean_obj_tag(v_a_1440_) == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec(v_inst_1439_);
v___x_1441_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2);
v___x_1442_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_1435_, v_inst_1436_, v_inst_1437_, v___x_1441_, v_a_1438_);
return v___x_1442_;
}
else
{
lean_object* v_val_1443_; lean_object* v___x_1444_; 
v_val_1443_ = lean_ctor_get(v_a_1440_, 0);
lean_inc(v_val_1443_);
lean_dec_ref_known(v_a_1440_, 1);
v___x_1444_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(v_inst_1435_, v_inst_1436_, v_inst_1439_, v_inst_1437_, v_val_1443_, v_a_1438_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___boxed(lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_a_1448_, lean_object* v_inst_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1(v_inst_1445_, v_inst_1446_, v_inst_1447_, v_a_1448_, v_inst_1449_, v_a_1450_);
lean_dec(v_a_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg(lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_hyps_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1459_; lean_object* v_toApplicative_1460_; lean_object* v_toFunctor_1461_; lean_object* v_toSeq_1462_; lean_object* v_toSeqLeft_1463_; lean_object* v_toSeqRight_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; lean_object* v___f_1470_; lean_object* v___f_1471_; lean_object* v___f_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v_toApplicative_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1517_; 
v___x_1459_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1);
v_toApplicative_1460_ = lean_ctor_get(v___x_1459_, 0);
v_toFunctor_1461_ = lean_ctor_get(v_toApplicative_1460_, 0);
v_toSeq_1462_ = lean_ctor_get(v_toApplicative_1460_, 2);
v_toSeqLeft_1463_ = lean_ctor_get(v_toApplicative_1460_, 3);
v_toSeqRight_1464_ = lean_ctor_get(v_toApplicative_1460_, 4);
v___f_1465_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2));
v___f_1466_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1461_, 2);
v___f_1467_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1467_, 0, v_toFunctor_1461_);
v___f_1468_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1468_, 0, v_toFunctor_1461_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___f_1467_);
lean_ctor_set(v___x_1469_, 1, v___f_1468_);
lean_inc(v_toSeqRight_1464_);
v___f_1470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1470_, 0, v_toSeqRight_1464_);
lean_inc(v_toSeqLeft_1463_);
v___f_1471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1471_, 0, v_toSeqLeft_1463_);
lean_inc(v_toSeq_1462_);
v___f_1472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1472_, 0, v_toSeq_1462_);
v___x_1473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1469_);
lean_ctor_set(v___x_1473_, 1, v___f_1465_);
lean_ctor_set(v___x_1473_, 2, v___f_1472_);
lean_ctor_set(v___x_1473_, 3, v___f_1471_);
lean_ctor_set(v___x_1473_, 4, v___f_1470_);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v___f_1466_);
v___x_1475_ = l_StateRefT_x27_instMonad___redArg(v___x_1474_);
v_toApplicative_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v___x_1475_, 1);
lean_dec(v_unused_1518_);
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1517_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_toApplicative_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1517_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_toFunctor_1480_; lean_object* v_toSeq_1481_; lean_object* v_toSeqLeft_1482_; lean_object* v_toSeqRight_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1515_; 
v_toFunctor_1480_ = lean_ctor_get(v_toApplicative_1476_, 0);
v_toSeq_1481_ = lean_ctor_get(v_toApplicative_1476_, 2);
v_toSeqLeft_1482_ = lean_ctor_get(v_toApplicative_1476_, 3);
v_toSeqRight_1483_ = lean_ctor_get(v_toApplicative_1476_, 4);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_toApplicative_1476_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_toApplicative_1476_, 1);
lean_dec(v_unused_1516_);
v___x_1485_ = v_toApplicative_1476_;
v_isShared_1486_ = v_isSharedCheck_1515_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_toSeqRight_1483_);
lean_inc(v_toSeqLeft_1482_);
lean_inc(v_toSeq_1481_);
lean_inc(v_toFunctor_1480_);
lean_dec(v_toApplicative_1476_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1515_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___f_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___f_1493_; lean_object* v___f_1494_; lean_object* v___x_1496_; 
v___f_1487_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4));
v___f_1488_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5));
lean_inc_ref(v_toFunctor_1480_);
v___f_1489_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1489_, 0, v_toFunctor_1480_);
v___f_1490_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1490_, 0, v_toFunctor_1480_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___f_1489_);
lean_ctor_set(v___x_1491_, 1, v___f_1490_);
v___f_1492_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1492_, 0, v_toSeqRight_1483_);
v___f_1493_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1493_, 0, v_toSeqLeft_1482_);
v___f_1494_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1494_, 0, v_toSeq_1481_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 4, v___f_1492_);
lean_ctor_set(v___x_1485_, 3, v___f_1493_);
lean_ctor_set(v___x_1485_, 2, v___f_1494_);
lean_ctor_set(v___x_1485_, 1, v___f_1487_);
lean_ctor_set(v___x_1485_, 0, v___x_1491_);
v___x_1496_ = v___x_1485_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___f_1487_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v___f_1494_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v___f_1493_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v___f_1492_);
v___x_1496_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 1, v___f_1488_);
lean_ctor_set(v___x_1478_, 0, v___x_1496_);
v___x_1498_ = v___x_1478_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___f_1488_);
v___x_1498_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_toBind_1505_; lean_object* v___f_1506_; lean_object* v___f_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1499_ = l_StateRefT_x27_instMonad___redArg(v___x_1498_);
v___x_1500_ = l_ReaderT_instMonad___redArg(v___x_1499_);
v___x_1501_ = l_StateRefT_x27_instMonad___redArg(v___x_1500_);
v___x_1502_ = l_ReaderT_instMonad___redArg(v___x_1501_);
v___x_1503_ = l_ReaderT_instMonad___redArg(v___x_1502_);
v___x_1504_ = l_StateRefT_x27_instMonad___redArg(v___x_1503_);
v_toBind_1505_ = lean_ctor_get(v_inst_1453_, 1);
lean_inc(v_toBind_1505_);
v___f_1506_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___closed__0));
lean_inc(v_inst_1455_);
lean_inc(v_a_1458_);
lean_inc(v_inst_1456_);
lean_inc_ref(v_inst_1453_);
v___f_1507_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1507_, 0, v_inst_1453_);
lean_closure_set(v___f_1507_, 1, v_inst_1454_);
lean_closure_set(v___f_1507_, 2, v_inst_1456_);
lean_closure_set(v___f_1507_, 3, v_a_1458_);
lean_closure_set(v___f_1507_, 4, v_inst_1455_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_hyps_1457_);
v___x_1509_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed), 13, 1);
lean_closure_set(v___x_1509_, 0, v___x_1508_);
v___x_1510_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1510_, 0, lean_box(0));
lean_closure_set(v___x_1510_, 1, lean_box(0));
lean_closure_set(v___x_1510_, 2, v___x_1504_);
lean_closure_set(v___x_1510_, 3, lean_box(0));
lean_closure_set(v___x_1510_, 4, lean_box(0));
lean_closure_set(v___x_1510_, 5, v___x_1509_);
lean_closure_set(v___x_1510_, 6, v___f_1506_);
v___x_1511_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(v_inst_1453_, v_inst_1455_, v_inst_1456_, v___x_1510_, v_a_1458_);
v___x_1512_ = lean_apply_4(v_toBind_1505_, lean_box(0), lean_box(0), v___x_1511_, v___f_1507_);
return v___x_1512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___boxed(lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_hyps_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg(v_inst_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_hyps_1523_, v_a_1524_);
lean_dec(v_a_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push(lean_object* v_00_u03c3_1526_, lean_object* v_m_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_hyps_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg(v_inst_1529_, v_inst_1530_, v_inst_1531_, v_inst_1532_, v_hyps_1533_, v_a_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___boxed(lean_object* v_00_u03c3_1536_, lean_object* v_m_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_hyps_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push(v_00_u03c3_1536_, v_m_1537_, v_inst_1538_, v_inst_1539_, v_inst_1540_, v_inst_1541_, v_inst_1542_, v_hyps_1543_, v_a_1544_);
lean_dec(v_a_1544_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg(lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v_inst_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg___closed__0));
v___x_1552_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_1547_, v_inst_1548_, v_inst_1549_, v___x_1551_, v_a_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg___boxed(lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg(v_inst_1553_, v_inst_1554_, v_inst_1555_, v_a_1556_);
lean_dec(v_a_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop(lean_object* v_00_u03c3_1558_, lean_object* v_m_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg(v_inst_1561_, v_inst_1562_, v_inst_1563_, v_a_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___boxed(lean_object* v_00_u03c3_1566_, lean_object* v_m_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop(v_00_u03c3_1566_, v_m_1567_, v_inst_1568_, v_inst_1569_, v_inst_1570_, v_inst_1571_, v_a_1572_);
lean_dec(v_a_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__0(lean_object* v_toApplicative_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_toPure_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_toPure_1576_ = lean_ctor_get(v_toApplicative_1574_, 1);
lean_inc(v_toPure_1576_);
lean_dec_ref(v_toApplicative_1574_);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1575_);
v___x_1578_ = lean_apply_2(v_toPure_1576_, lean_box(0), v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1(lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_a_1584_, lean_object* v_toBind_1585_, lean_object* v___f_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_bvSolver_1588_; lean_object* v_bitvecState_1589_; lean_object* v_aig_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_bvSolver_1588_ = lean_ctor_get(v_a_1587_, 2);
lean_inc_ref(v_bvSolver_1588_);
lean_dec_ref(v_a_1587_);
v_bitvecState_1589_ = lean_ctor_get(v_bvSolver_1588_, 0);
lean_inc_ref(v_bitvecState_1589_);
lean_dec_ref(v_bvSolver_1588_);
v_aig_1590_ = lean_ctor_get(v_bitvecState_1589_, 0);
lean_inc_ref(v_aig_1590_);
lean_dec_ref(v_bitvecState_1589_);
v___x_1591_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_1590_, v_a_1579_, v_a_1580_);
v___x_1592_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray___boxed), 13, 1);
lean_closure_set(v___x_1592_, 0, v___x_1591_);
v___x_1593_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_1581_, v_inst_1582_, v_inst_1583_, v___x_1592_, v_a_1584_);
v___x_1594_ = lean_apply_4(v_toBind_1585_, lean_box(0), lean_box(0), v___x_1593_, v___f_1586_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1___boxed(lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_a_1600_, lean_object* v_toBind_1601_, lean_object* v___f_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1(v_a_1595_, v_a_1596_, v_inst_1597_, v_inst_1598_, v_inst_1599_, v_a_1600_, v_toBind_1601_, v___f_1602_, v_a_1603_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1596_);
lean_dec_ref(v_a_1595_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2(lean_object* v_a_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_a_1609_, lean_object* v_toBind_1610_, lean_object* v___f_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_inc(v_toBind_1610_);
lean_inc_n(v_a_1609_, 2);
lean_inc(v_inst_1608_);
v___f_1613_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_1613_, 0, v_a_1605_);
lean_closure_set(v___f_1613_, 1, v_a_1612_);
lean_closure_set(v___f_1613_, 2, v_inst_1606_);
lean_closure_set(v___f_1613_, 3, v_inst_1607_);
lean_closure_set(v___f_1613_, 4, v_inst_1608_);
lean_closure_set(v___f_1613_, 5, v_a_1609_);
lean_closure_set(v___f_1613_, 6, v_toBind_1610_);
lean_closure_set(v___f_1613_, 7, v___f_1611_);
v___x_1614_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1614_, 0, lean_box(0));
lean_closure_set(v___x_1614_, 1, lean_box(0));
lean_closure_set(v___x_1614_, 2, v_a_1609_);
v___x_1615_ = lean_apply_2(v_inst_1608_, lean_box(0), v___x_1614_);
v___x_1616_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v___x_1615_, v___f_1613_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2___boxed(lean_object* v_a_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_a_1621_, lean_object* v_toBind_1622_, lean_object* v___f_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2(v_a_1617_, v_inst_1618_, v_inst_1619_, v_inst_1620_, v_a_1621_, v_toBind_1622_, v___f_1623_, v_a_1624_);
lean_dec(v_a_1621_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3(lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_a_1632_, lean_object* v_toBind_1633_, lean_object* v___f_1634_, lean_object* v_toApplicative_1635_, lean_object* v_a_1636_){
_start:
{
if (lean_obj_tag(v_a_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___f_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v_toApplicative_1635_);
v_a_1637_ = lean_ctor_get(v_a_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v_a_1636_, 1);
lean_inc(v_toBind_1633_);
lean_inc(v_a_1632_);
lean_inc(v_inst_1631_);
lean_inc(v_inst_1630_);
lean_inc_ref(v_inst_1629_);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1638_, 0, v_a_1637_);
lean_closure_set(v___f_1638_, 1, v_inst_1629_);
lean_closure_set(v___f_1638_, 2, v_inst_1630_);
lean_closure_set(v___f_1638_, 3, v_inst_1631_);
lean_closure_set(v___f_1638_, 4, v_a_1632_);
lean_closure_set(v___f_1638_, 5, v_toBind_1633_);
lean_closure_set(v___f_1638_, 6, v___f_1634_);
v___x_1639_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__0));
v___x_1640_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_1629_, v_inst_1630_, v_inst_1631_, v___x_1639_, v_a_1632_);
v___x_1641_ = lean_apply_4(v_toBind_1633_, lean_box(0), lean_box(0), v___x_1640_, v___f_1638_);
return v___x_1641_;
}
else
{
lean_object* v_toPure_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec_ref_known(v_a_1636_, 1);
lean_dec(v___f_1634_);
lean_dec(v_toBind_1633_);
lean_dec(v_inst_1631_);
lean_dec(v_inst_1630_);
lean_dec_ref(v_inst_1629_);
v_toPure_1642_ = lean_ctor_get(v_toApplicative_1635_, 1);
lean_inc(v_toPure_1642_);
lean_dec_ref(v_toApplicative_1635_);
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__1));
v___x_1644_ = lean_apply_2(v_toPure_1642_, lean_box(0), v___x_1643_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___boxed(lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_a_1648_, lean_object* v_toBind_1649_, lean_object* v___f_1650_, lean_object* v_toApplicative_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3(v_inst_1645_, v_inst_1646_, v_inst_1647_, v_a_1648_, v_toBind_1649_, v___f_1650_, v_toApplicative_1651_, v_a_1652_);
lean_dec(v_a_1648_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg(lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_toApplicative_1660_; lean_object* v_toBind_1661_; lean_object* v___f_1662_; lean_object* v___f_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_toApplicative_1660_ = lean_ctor_get(v_inst_1655_, 0);
v_toBind_1661_ = lean_ctor_get(v_inst_1655_, 1);
lean_inc_n(v_toBind_1661_, 2);
lean_inc_ref_n(v_toApplicative_1660_, 2);
v___f_1662_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1662_, 0, v_toApplicative_1660_);
lean_inc(v_a_1659_);
lean_inc(v_inst_1658_);
lean_inc_ref(v_inst_1655_);
v___f_1663_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1663_, 0, v_inst_1655_);
lean_closure_set(v___f_1663_, 1, v_inst_1657_);
lean_closure_set(v___f_1663_, 2, v_inst_1658_);
lean_closure_set(v___f_1663_, 3, v_a_1659_);
lean_closure_set(v___f_1663_, 4, v_toBind_1661_);
lean_closure_set(v___f_1663_, 5, v___f_1662_);
lean_closure_set(v___f_1663_, 6, v_toApplicative_1660_);
v___x_1664_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___closed__0));
v___x_1665_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_1655_, v_inst_1656_, v_inst_1658_, v___x_1664_, v_a_1659_);
v___x_1666_ = lean_apply_4(v_toBind_1661_, lean_box(0), lean_box(0), v___x_1665_, v___f_1663_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___boxed(lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg(v_inst_1667_, v_inst_1668_, v_inst_1669_, v_inst_1670_, v_a_1671_);
lean_dec(v_a_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check(lean_object* v_00_u03c3_1673_, lean_object* v_m_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg(v_inst_1676_, v_inst_1677_, v_inst_1678_, v_inst_1679_, v_a_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___boxed(lean_object* v_00_u03c3_1682_, lean_object* v_m_1683_, lean_object* v_inst_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check(v_00_u03c3_1682_, v_m_1683_, v_inst_1684_, v_inst_1685_, v_inst_1686_, v_inst_1687_, v_inst_1688_, v_a_1689_);
lean_dec(v_a_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__0(lean_object* v_toPure_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_reifyState_1693_; lean_object* v___x_1694_; 
v_reifyState_1693_ = lean_ctor_get(v_a_1692_, 0);
lean_inc_ref(v_reifyState_1693_);
lean_dec_ref(v_a_1692_);
v___x_1694_ = lean_apply_2(v_toPure_1691_, lean_box(0), v_reifyState_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__1(lean_object* v_a_1695_, lean_object* v_inst_1696_, lean_object* v_toBind_1697_, lean_object* v___f_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_inc(v_a_1695_);
v___x_1700_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1700_, 0, lean_box(0));
lean_closure_set(v___x_1700_, 1, lean_box(0));
lean_closure_set(v___x_1700_, 2, v_a_1695_);
v___x_1701_ = lean_apply_2(v_inst_1696_, lean_box(0), v___x_1700_);
v___x_1702_ = lean_apply_4(v_toBind_1697_, lean_box(0), lean_box(0), v___x_1701_, v___f_1698_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__1___boxed(lean_object* v_a_1703_, lean_object* v_inst_1704_, lean_object* v_toBind_1705_, lean_object* v___f_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__1(v_a_1703_, v_inst_1704_, v_toBind_1705_, v___f_1706_, v_a_1707_);
lean_dec(v_a_1703_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg(lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_toApplicative_1713_; lean_object* v_toFunctor_1714_; lean_object* v_toBind_1715_; lean_object* v_toPure_1716_; lean_object* v_mapConst_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_toApplicative_1713_ = lean_ctor_get(v_inst_1709_, 0);
v_toFunctor_1714_ = lean_ctor_get(v_toApplicative_1713_, 0);
v_toBind_1715_ = lean_ctor_get(v_inst_1709_, 1);
lean_inc_n(v_toBind_1715_, 2);
v_toPure_1716_ = lean_ctor_get(v_toApplicative_1713_, 1);
v_mapConst_1717_ = lean_ctor_get(v_toFunctor_1714_, 1);
lean_inc(v_mapConst_1717_);
lean_inc(v_toPure_1716_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1718_, 0, v_toPure_1716_);
lean_inc(v_inst_1711_);
lean_inc(v_a_1712_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1719_, 0, v_a_1712_);
lean_closure_set(v___f_1719_, 1, v_inst_1711_);
lean_closure_set(v___f_1719_, 2, v_toBind_1715_);
lean_closure_set(v___f_1719_, 3, v___f_1718_);
v___x_1720_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__0));
v___x_1721_ = lean_box(0);
v___x_1722_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_1709_, v_inst_1710_, v_inst_1711_, v___x_1720_, v_a_1712_);
v___x_1723_ = lean_apply_4(v_mapConst_1717_, lean_box(0), lean_box(0), v___x_1721_, v___x_1722_);
v___x_1724_ = lean_apply_4(v_toBind_1715_, lean_box(0), lean_box(0), v___x_1723_, v___f_1719_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg___boxed(lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg(v_inst_1725_, v_inst_1726_, v_inst_1727_, v_a_1728_);
lean_dec(v_a_1728_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState(lean_object* v_00_u03c3_1730_, lean_object* v_m_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___redArg(v_inst_1733_, v_inst_1734_, v_inst_1735_, v_a_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState___boxed(lean_object* v_00_u03c3_1738_, lean_object* v_m_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_getReifyState(v_00_u03c3_1738_, v_m_1739_, v_inst_1740_, v_inst_1741_, v_inst_1742_, v_inst_1743_, v_a_1744_);
lean_dec(v_a_1744_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__0(lean_object* v_a_1746_, lean_object* v_toPure_1747_, lean_object* v_s_1748_){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_a_1746_);
lean_ctor_set(v___x_1749_, 1, v_s_1748_);
v___x_1750_ = lean_apply_2(v_toPure_1747_, lean_box(0), v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__1(lean_object* v_toPure_1751_, lean_object* v_ref_1752_, lean_object* v_inst_1753_, lean_object* v_toBind_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1756_, 0, v_a_1755_);
lean_closure_set(v___f_1756_, 1, v_toPure_1751_);
v___x_1757_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1757_, 0, lean_box(0));
lean_closure_set(v___x_1757_, 1, lean_box(0));
lean_closure_set(v___x_1757_, 2, v_ref_1752_);
v___x_1758_ = lean_apply_2(v_inst_1753_, lean_box(0), v___x_1757_);
v___x_1759_ = lean_apply_4(v_toBind_1754_, lean_box(0), lean_box(0), v___x_1758_, v___f_1756_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__2(lean_object* v_toPure_1760_, lean_object* v_inst_1761_, lean_object* v_toBind_1762_, lean_object* v_x_1763_, lean_object* v_ref_1764_){
_start:
{
lean_object* v___f_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_inc(v_toBind_1762_);
lean_inc(v_ref_1764_);
v___f_1765_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1765_, 0, v_toPure_1760_);
lean_closure_set(v___f_1765_, 1, v_ref_1764_);
lean_closure_set(v___f_1765_, 2, v_inst_1761_);
lean_closure_set(v___f_1765_, 3, v_toBind_1762_);
v___x_1766_ = lean_apply_1(v_x_1763_, v_ref_1764_);
v___x_1767_ = lean_apply_4(v_toBind_1762_, lean_box(0), lean_box(0), v___x_1766_, v___f_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__3(lean_object* v_toPure_1768_, lean_object* v_____x_1769_){
_start:
{
lean_object* v_fst_1770_; lean_object* v___x_1771_; 
v_fst_1770_ = lean_ctor_get(v_____x_1769_, 0);
lean_inc(v_fst_1770_);
lean_dec_ref(v_____x_1769_);
v___x_1771_ = lean_apply_2(v_toPure_1768_, lean_box(0), v_fst_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__4(lean_object* v_toApplicative_1772_, lean_object* v_inst_1773_, lean_object* v_toBind_1774_, lean_object* v_x_1775_, lean_object* v_solver_1776_){
_start:
{
lean_object* v_toPure_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___f_1780_; lean_object* v___f_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_toPure_1777_ = lean_ctor_get(v_toApplicative_1772_, 1);
lean_inc_n(v_toPure_1777_, 2);
lean_dec_ref(v_toApplicative_1772_);
v___x_1778_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1778_, 0, lean_box(0));
lean_closure_set(v___x_1778_, 1, lean_box(0));
lean_closure_set(v___x_1778_, 2, v_solver_1776_);
lean_inc(v_inst_1773_);
v___x_1779_ = lean_apply_2(v_inst_1773_, lean_box(0), v___x_1778_);
lean_inc_n(v_toBind_1774_, 2);
v___f_1780_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1780_, 0, v_toPure_1777_);
lean_closure_set(v___f_1780_, 1, v_inst_1773_);
lean_closure_set(v___f_1780_, 2, v_toBind_1774_);
lean_closure_set(v___f_1780_, 3, v_x_1775_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_1781_, 0, v_toPure_1777_);
v___x_1782_ = lean_apply_4(v_toBind_1774_, lean_box(0), lean_box(0), v___x_1779_, v___f_1780_);
v___x_1783_ = lean_apply_4(v_toBind_1774_, lean_box(0), lean_box(0), v___x_1782_, v___f_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg(lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_ctx_1787_, lean_object* v_mvar_1788_, lean_object* v_x_1789_, lean_object* v_reifyState_1790_, uint8_t v_trackFunAtoms_1791_){
_start:
{
lean_object* v_toApplicative_1792_; lean_object* v_toBind_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_toApplicative_1792_ = lean_ctor_get(v_inst_1784_, 0);
lean_inc_ref(v_toApplicative_1792_);
v_toBind_1793_ = lean_ctor_get(v_inst_1784_, 1);
lean_inc_n(v_toBind_1793_, 2);
lean_dec_ref(v_inst_1784_);
v___f_1794_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1794_, 0, v_toApplicative_1792_);
lean_closure_set(v___f_1794_, 1, v_inst_1786_);
lean_closure_set(v___f_1794_, 2, v_toBind_1793_);
lean_closure_set(v___f_1794_, 3, v_x_1789_);
v___x_1795_ = lean_box(v_trackFunAtoms_1791_);
v___x_1796_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___boxed), 11, 4);
lean_closure_set(v___x_1796_, 0, v_ctx_1787_);
lean_closure_set(v___x_1796_, 1, v_mvar_1788_);
lean_closure_set(v___x_1796_, 2, v_reifyState_1790_);
lean_closure_set(v___x_1796_, 3, v___x_1795_);
v___x_1797_ = lean_apply_2(v_inst_1785_, lean_box(0), v___x_1796_);
v___x_1798_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v___x_1797_, v___f_1794_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___boxed(lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_ctx_1802_, lean_object* v_mvar_1803_, lean_object* v_x_1804_, lean_object* v_reifyState_1805_, lean_object* v_trackFunAtoms_1806_){
_start:
{
uint8_t v_trackFunAtoms_boxed_1807_; lean_object* v_res_1808_; 
v_trackFunAtoms_boxed_1807_ = lean_unbox(v_trackFunAtoms_1806_);
v_res_1808_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg(v_inst_1799_, v_inst_1800_, v_inst_1801_, v_ctx_1802_, v_mvar_1803_, v_x_1804_, v_reifyState_1805_, v_trackFunAtoms_boxed_1807_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run(lean_object* v_00_u03c3_1809_, lean_object* v_m_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_00_u03b1_1815_, lean_object* v_ctx_1816_, lean_object* v_mvar_1817_, lean_object* v_x_1818_, lean_object* v_reifyState_1819_, uint8_t v_trackFunAtoms_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg(v_inst_1812_, v_inst_1813_, v_inst_1814_, v_ctx_1816_, v_mvar_1817_, v_x_1818_, v_reifyState_1819_, v_trackFunAtoms_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___boxed(lean_object* v_00_u03c3_1822_, lean_object* v_m_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_inst_1827_, lean_object* v_00_u03b1_1828_, lean_object* v_ctx_1829_, lean_object* v_mvar_1830_, lean_object* v_x_1831_, lean_object* v_reifyState_1832_, lean_object* v_trackFunAtoms_1833_){
_start:
{
uint8_t v_trackFunAtoms_boxed_1834_; lean_object* v_res_1835_; 
v_trackFunAtoms_boxed_1834_ = lean_unbox(v_trackFunAtoms_1833_);
v_res_1835_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run(v_00_u03c3_1822_, v_m_1823_, v_inst_1824_, v_inst_1825_, v_inst_1826_, v_inst_1827_, v_00_u03b1_1828_, v_ctx_1829_, v_mvar_1830_, v_x_1831_, v_reifyState_1832_, v_trackFunAtoms_boxed_1834_);
return v_res_1835_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0 = _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(builtin);
}
#ifdef __cplusplus
}
#endif
