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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Cadical_Solver_new();
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(uint8_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instMonadControlReaderT___redArg();
lean_object* l_instMonadControlStateRefT_x27___redArg();
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_BvSolverM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_BvSolverM_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_empty___redArg();
lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg(lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Array_filterMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_BvSolverM_pop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__5;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to reify subsolver hypothesis "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__7_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__3_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__4_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__5_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__8_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__6_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__12;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__14;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__15;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__17;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__20;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__21;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__23;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__24;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__26;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__27;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__29;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__30;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__31;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__32 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__32_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__34;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__35;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__36;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__37;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__38;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__39;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__40;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__41;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__42;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__43;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__44;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__45;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__46;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__47;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__48;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__49;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__50;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__51;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__52 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__52_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__53 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__53_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__53_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__54 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__54_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__55;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_unsigned_to_nat(16u);
v___x_33_ = lean_mk_array(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__0);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__3));
v___x_42_ = lean_box(0);
v___x_43_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1);
v___x_44_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_42_);
lean_ctor_set(v___x_44_, 3, v___x_43_);
lean_ctor_set(v___x_44_, 4, v___x_41_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__5);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__6);
v___x_49_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
lean_ctor_set(v___x_49_, 2, v___x_48_);
lean_ctor_set(v___x_49_, 3, v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__9(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0;
v___x_53_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__1(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__10(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__9);
v___x_55_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__8);
v___x_56_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new_spec__0;
v___x_57_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg(lean_object* v_ctx_58_, lean_object* v_mvar_59_){
_start:
{
lean_object* v_config_61_; lean_object* v_exprDef_62_; lean_object* v_certDef_63_; lean_object* v_reflectionDef_64_; lean_object* v_solver_65_; lean_object* v_lratPath_66_; lean_object* v_restrictedTypes_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_105_; 
v_config_61_ = lean_ctor_get(v_ctx_58_, 5);
v_exprDef_62_ = lean_ctor_get(v_ctx_58_, 0);
v_certDef_63_ = lean_ctor_get(v_ctx_58_, 1);
v_reflectionDef_64_ = lean_ctor_get(v_ctx_58_, 2);
v_solver_65_ = lean_ctor_get(v_ctx_58_, 3);
v_lratPath_66_ = lean_ctor_get(v_ctx_58_, 4);
v_restrictedTypes_67_ = lean_ctor_get(v_ctx_58_, 6);
v_isSharedCheck_105_ = !lean_is_exclusive(v_ctx_58_);
if (v_isSharedCheck_105_ == 0)
{
v___x_69_ = v_ctx_58_;
v_isShared_70_ = v_isSharedCheck_105_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_restrictedTypes_67_);
lean_inc(v_config_61_);
lean_inc(v_lratPath_66_);
lean_inc(v_solver_65_);
lean_inc(v_reflectionDef_64_);
lean_inc(v_certDef_63_);
lean_inc(v_exprDef_62_);
lean_dec(v_ctx_58_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_105_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v_timeout_71_; uint8_t v_trimProofs_72_; uint8_t v_binaryProofs_73_; uint8_t v_acNf_74_; uint8_t v_andFlattening_75_; uint8_t v_embeddedConstraintSubst_76_; uint8_t v_graphviz_77_; lean_object* v_maxSteps_78_; uint8_t v_solverMode_79_; lean_object* v_cegarRounds_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_104_; 
v_timeout_71_ = lean_ctor_get(v_config_61_, 0);
v_trimProofs_72_ = lean_ctor_get_uint8(v_config_61_, sizeof(void*)*3);
v_binaryProofs_73_ = lean_ctor_get_uint8(v_config_61_, sizeof(void*)*3 + 1);
v_acNf_74_ = lean_ctor_get_uint8(v_config_61_, sizeof(void*)*3 + 2);
v_andFlattening_75_ = lean_ctor_get_uint8(v_config_61_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_76_ = lean_ctor_get_uint8(v_config_61_, sizeof(void*)*3 + 4);
v_graphviz_77_ = lean_ctor_get_uint8(v_config_61_, sizeof(void*)*3 + 8);
v_maxSteps_78_ = lean_ctor_get(v_config_61_, 1);
v_solverMode_79_ = lean_ctor_get_uint8(v_config_61_, sizeof(void*)*3 + 10);
v_cegarRounds_80_ = lean_ctor_get(v_config_61_, 2);
v_isSharedCheck_104_ = !lean_is_exclusive(v_config_61_);
if (v_isSharedCheck_104_ == 0)
{
v___x_82_ = v_config_61_;
v_isShared_83_ = v_isSharedCheck_104_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_cegarRounds_80_);
lean_inc(v_maxSteps_78_);
lean_inc(v_timeout_71_);
lean_dec(v_config_61_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_104_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
uint8_t v___x_84_; lean_object* v___x_86_; 
v___x_84_ = 0;
lean_inc(v_timeout_71_);
if (v_isShared_83_ == 0)
{
v___x_86_ = v___x_82_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_timeout_71_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_maxSteps_78_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_cegarRounds_80_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*3, v_trimProofs_72_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*3 + 1, v_binaryProofs_73_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*3 + 2, v_acNf_74_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*3 + 3, v_andFlattening_75_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_76_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*3 + 8, v_graphviz_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*3 + 10, v_solverMode_79_);
v___x_86_ = v_reuseFailAlloc_103_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v_ctx_88_; 
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 5, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 6, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 7, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 9, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 11, v___x_84_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 5, v___x_86_);
v_ctx_88_ = v___x_69_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_exprDef_62_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_certDef_63_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_reflectionDef_64_);
lean_ctor_set(v_reuseFailAlloc_102_, 3, v_solver_65_);
lean_ctor_set(v_reuseFailAlloc_102_, 4, v_lratPath_66_);
lean_ctor_set(v_reuseFailAlloc_102_, 5, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_102_, 6, v_restrictedTypes_67_);
v_ctx_88_ = v_reuseFailAlloc_102_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_89_ = l_Lean_Cadical_Solver_new();
v___x_90_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_solverMode_79_);
v___x_91_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(v___x_90_);
v___x_92_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v___x_91_, v___x_89_);
lean_dec_ref(v___x_91_);
v___x_93_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__2));
v___x_94_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4);
v___x_95_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7);
v___x_96_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__10);
v___x_97_ = lean_unsigned_to_nat(1000u);
v___x_98_ = lean_nat_mul(v_timeout_71_, v___x_97_);
lean_dec(v_timeout_71_);
v___x_99_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_99_, 0, v___x_96_);
lean_ctor_set(v___x_99_, 1, v___x_89_);
lean_ctor_set(v___x_99_, 2, v___x_98_);
lean_ctor_set(v___x_99_, 3, v___x_93_);
v___x_100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_100_, 0, v___x_94_);
lean_ctor_set(v___x_100_, 1, v___x_95_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
lean_ctor_set(v___x_100_, 3, v_mvar_59_);
lean_ctor_set(v___x_100_, 4, v_ctx_88_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___boxed(lean_object* v_ctx_106_, lean_object* v_mvar_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg(v_ctx_106_, v_mvar_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new(lean_object* v_ctx_110_, lean_object* v_mvar_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg(v_ctx_110_, v_mvar_111_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___boxed(lean_object* v_ctx_120_, lean_object* v_mvar_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new(v_ctx_120_, v_mvar_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__0(lean_object* v_snd_130_, lean_object* v_s_131_){
_start:
{
lean_object* v_reifyState_132_; lean_object* v_preProcessState_133_; lean_object* v_mvar_134_; lean_object* v_ctx_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_144_; 
v_reifyState_132_ = lean_ctor_get(v_s_131_, 0);
v_preProcessState_133_ = lean_ctor_get(v_s_131_, 1);
v_mvar_134_ = lean_ctor_get(v_s_131_, 3);
v_ctx_135_ = lean_ctor_get(v_s_131_, 4);
v_isSharedCheck_144_ = !lean_is_exclusive(v_s_131_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v_s_131_, 2);
lean_dec(v_unused_145_);
v___x_137_ = v_s_131_;
v_isShared_138_ = v_isSharedCheck_144_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_ctx_135_);
lean_inc(v_mvar_134_);
lean_inc(v_preProcessState_133_);
lean_inc(v_reifyState_132_);
lean_dec(v_s_131_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_144_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 2, v_snd_130_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_reifyState_132_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_preProcessState_133_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_snd_130_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v_mvar_134_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_ctx_135_);
v___x_141_ = v_reuseFailAlloc_143_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_139_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1(lean_object* v_toApplicative_146_, lean_object* v_fst_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_toPure_149_; lean_object* v___x_150_; 
v_toPure_149_ = lean_ctor_get(v_toApplicative_146_, 1);
lean_inc(v_toPure_149_);
lean_dec_ref(v_toApplicative_146_);
v___x_150_ = lean_apply_2(v_toPure_149_, lean_box(0), v_fst_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2(lean_object* v_toApplicative_151_, lean_object* v_a_152_, lean_object* v_inst_153_, lean_object* v_toBind_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_fst_156_ = lean_ctor_get(v_a_155_, 0);
lean_inc(v_fst_156_);
v_snd_157_ = lean_ctor_get(v_a_155_, 1);
lean_inc(v_snd_157_);
lean_dec_ref(v_a_155_);
v___f_158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_158_, 0, v_snd_157_);
v___f_159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_159_, 0, v_toApplicative_151_);
lean_closure_set(v___f_159_, 1, v_fst_156_);
lean_inc(v_a_152_);
v___x_160_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_160_, 0, lean_box(0));
lean_closure_set(v___x_160_, 1, lean_box(0));
lean_closure_set(v___x_160_, 2, lean_box(0));
lean_closure_set(v___x_160_, 3, v_a_152_);
lean_closure_set(v___x_160_, 4, v___f_158_);
v___x_161_ = lean_apply_2(v_inst_153_, lean_box(0), v___x_160_);
v___x_162_ = lean_apply_4(v_toBind_154_, lean_box(0), lean_box(0), v___x_161_, v___f_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2___boxed(lean_object* v_toApplicative_163_, lean_object* v_a_164_, lean_object* v_inst_165_, lean_object* v_toBind_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2(v_toApplicative_163_, v_a_164_, v_inst_165_, v_toBind_166_, v_a_167_);
lean_dec(v_a_164_);
return v_res_168_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Sat_AIG_empty___redArg();
return v___x_169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_box(0);
v___x_171_ = lean_unsigned_to_nat(16u);
v___x_172_ = lean_mk_array(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__1);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0);
v___x_177_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__2);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__5(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__3);
v___x_181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__4);
v___x_182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__0);
v___x_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_180_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3(lean_object* v_s_184_){
_start:
{
lean_object* v_bvSolver_185_; lean_object* v_reifyState_186_; lean_object* v_preProcessState_187_; lean_object* v_mvar_188_; lean_object* v_ctx_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_202_; 
v_bvSolver_185_ = lean_ctor_get(v_s_184_, 2);
v_reifyState_186_ = lean_ctor_get(v_s_184_, 0);
v_preProcessState_187_ = lean_ctor_get(v_s_184_, 1);
v_mvar_188_ = lean_ctor_get(v_s_184_, 3);
v_ctx_189_ = lean_ctor_get(v_s_184_, 4);
v_isSharedCheck_202_ = !lean_is_exclusive(v_s_184_);
if (v_isSharedCheck_202_ == 0)
{
v___x_191_ = v_s_184_;
v_isShared_192_ = v_isSharedCheck_202_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_ctx_189_);
lean_inc(v_mvar_188_);
lean_inc(v_bvSolver_185_);
lean_inc(v_preProcessState_187_);
lean_inc(v_reifyState_186_);
lean_dec(v_s_184_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_202_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_satSolver_193_; lean_object* v_solverTimeBudgetMs_194_; lean_object* v_assumptions_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v_satSolver_193_ = lean_ctor_get(v_bvSolver_185_, 1);
v_solverTimeBudgetMs_194_ = lean_ctor_get(v_bvSolver_185_, 2);
v_assumptions_195_ = lean_ctor_get(v_bvSolver_185_, 3);
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__3___closed__5);
lean_inc_ref(v_assumptions_195_);
lean_inc(v_solverTimeBudgetMs_194_);
lean_inc_ref(v_satSolver_193_);
v___x_197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v_satSolver_193_);
lean_ctor_set(v___x_197_, 2, v_solverTimeBudgetMs_194_);
lean_ctor_set(v___x_197_, 3, v_assumptions_195_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 2, v___x_197_);
v___x_199_ = v___x_191_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_reifyState_186_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_preProcessState_187_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_mvar_188_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_ctx_189_);
v___x_199_ = v_reuseFailAlloc_201_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_bvSolver_185_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__4(lean_object* v_ctx_203_, lean_object* v_x_204_, lean_object* v_inst_205_, lean_object* v_toBind_206_, lean_object* v___f_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_BvSolverM_run___boxed), 11, 4);
lean_closure_set(v___x_209_, 0, lean_box(0));
lean_closure_set(v___x_209_, 1, v_ctx_203_);
lean_closure_set(v___x_209_, 2, v_a_208_);
lean_closure_set(v___x_209_, 3, v_x_204_);
v___x_210_ = lean_apply_2(v_inst_205_, lean_box(0), v___x_209_);
v___x_211_ = lean_apply_4(v_toBind_206_, lean_box(0), lean_box(0), v___x_210_, v___f_207_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5(lean_object* v_x_212_, lean_object* v_inst_213_, lean_object* v_toBind_214_, lean_object* v___f_215_, lean_object* v_a_216_, lean_object* v___f_217_, lean_object* v_inst_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_ctx_220_; lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_ctx_220_ = lean_ctor_get(v_a_219_, 4);
lean_inc_ref(v_ctx_220_);
lean_dec_ref(v_a_219_);
lean_inc(v_toBind_214_);
v___f_221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__4), 6, 5);
lean_closure_set(v___f_221_, 0, v_ctx_220_);
lean_closure_set(v___f_221_, 1, v_x_212_);
lean_closure_set(v___f_221_, 2, v_inst_213_);
lean_closure_set(v___f_221_, 3, v_toBind_214_);
lean_closure_set(v___f_221_, 4, v___f_215_);
lean_inc(v_a_216_);
v___x_222_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_222_, 0, lean_box(0));
lean_closure_set(v___x_222_, 1, lean_box(0));
lean_closure_set(v___x_222_, 2, lean_box(0));
lean_closure_set(v___x_222_, 3, v_a_216_);
lean_closure_set(v___x_222_, 4, v___f_217_);
v___x_223_ = lean_apply_2(v_inst_218_, lean_box(0), v___x_222_);
v___x_224_ = lean_apply_4(v_toBind_214_, lean_box(0), lean_box(0), v___x_223_, v___f_221_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5___boxed(lean_object* v_x_225_, lean_object* v_inst_226_, lean_object* v_toBind_227_, lean_object* v___f_228_, lean_object* v_a_229_, lean_object* v___f_230_, lean_object* v_inst_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5(v_x_225_, v_inst_226_, v_toBind_227_, v___f_228_, v_a_229_, v___f_230_, v_inst_231_, v_a_232_);
lean_dec(v_a_229_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_x_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_toApplicative_240_; lean_object* v_toBind_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_toApplicative_240_ = lean_ctor_get(v_inst_235_, 0);
lean_inc_ref(v_toApplicative_240_);
v_toBind_241_ = lean_ctor_get(v_inst_235_, 1);
lean_inc_n(v_toBind_241_, 3);
lean_dec_ref(v_inst_235_);
lean_inc_n(v_inst_237_, 2);
lean_inc_n(v_a_239_, 3);
v___f_242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_242_, 0, v_toApplicative_240_);
lean_closure_set(v___f_242_, 1, v_a_239_);
lean_closure_set(v___f_242_, 2, v_inst_237_);
lean_closure_set(v___f_242_, 3, v_toBind_241_);
v___f_243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___closed__0));
v___f_244_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_244_, 0, v_x_238_);
lean_closure_set(v___f_244_, 1, v_inst_236_);
lean_closure_set(v___f_244_, 2, v_toBind_241_);
lean_closure_set(v___f_244_, 3, v___f_242_);
lean_closure_set(v___f_244_, 4, v_a_239_);
lean_closure_set(v___f_244_, 5, v___f_243_);
lean_closure_set(v___f_244_, 6, v_inst_237_);
v___x_245_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_245_, 0, lean_box(0));
lean_closure_set(v___x_245_, 1, lean_box(0));
lean_closure_set(v___x_245_, 2, v_a_239_);
v___x_246_ = lean_apply_2(v_inst_237_, lean_box(0), v___x_245_);
v___x_247_ = lean_apply_4(v_toBind_241_, lean_box(0), lean_box(0), v___x_246_, v___f_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___boxed(lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_x_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_248_, v_inst_249_, v_inst_250_, v_x_251_, v_a_252_);
lean_dec(v_a_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM(lean_object* v_00_u03c3_254_, lean_object* v_m_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_00_u03b1_260_, lean_object* v_x_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_257_, v_inst_258_, v_inst_259_, v_x_261_, v_a_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___boxed(lean_object* v_00_u03c3_264_, lean_object* v_m_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_00_u03b1_270_, lean_object* v_x_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM(v_00_u03c3_264_, v_m_265_, v_inst_266_, v_inst_267_, v_inst_268_, v_inst_269_, v_00_u03b1_270_, v_x_271_, v_a_272_);
lean_dec(v_a_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__0(lean_object* v_s_274_){
_start:
{
lean_object* v_reifyState_275_; lean_object* v_preProcessState_276_; lean_object* v_bvSolver_277_; lean_object* v_mvar_278_; lean_object* v_ctx_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_288_; 
v_reifyState_275_ = lean_ctor_get(v_s_274_, 0);
v_preProcessState_276_ = lean_ctor_get(v_s_274_, 1);
v_bvSolver_277_ = lean_ctor_get(v_s_274_, 2);
v_mvar_278_ = lean_ctor_get(v_s_274_, 3);
v_ctx_279_ = lean_ctor_get(v_s_274_, 4);
v_isSharedCheck_288_ = !lean_is_exclusive(v_s_274_);
if (v_isSharedCheck_288_ == 0)
{
v___x_281_ = v_s_274_;
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_ctx_279_);
lean_inc(v_mvar_278_);
lean_inc(v_bvSolver_277_);
lean_inc(v_preProcessState_276_);
lean_inc(v_reifyState_275_);
lean_dec(v_s_274_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__4);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_preProcessState_276_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_bvSolver_277_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_mvar_278_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_ctx_279_);
v___x_285_ = v_reuseFailAlloc_287_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v_reifyState_275_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__1(lean_object* v_snd_289_, lean_object* v_s_290_){
_start:
{
lean_object* v_preProcessState_291_; lean_object* v_bvSolver_292_; lean_object* v_mvar_293_; lean_object* v_ctx_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_303_; 
v_preProcessState_291_ = lean_ctor_get(v_s_290_, 1);
v_bvSolver_292_ = lean_ctor_get(v_s_290_, 2);
v_mvar_293_ = lean_ctor_get(v_s_290_, 3);
v_ctx_294_ = lean_ctor_get(v_s_290_, 4);
v_isSharedCheck_303_ = !lean_is_exclusive(v_s_290_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v_s_290_, 0);
lean_dec(v_unused_304_);
v___x_296_ = v_s_290_;
v_isShared_297_ = v_isSharedCheck_303_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_ctx_294_);
lean_inc(v_mvar_293_);
lean_inc(v_bvSolver_292_);
lean_inc(v_preProcessState_291_);
lean_dec(v_s_290_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_303_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_box(0);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v_snd_289_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_snd_289_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_preProcessState_291_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_bvSolver_292_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_mvar_293_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v_ctx_294_);
v___x_300_ = v_reuseFailAlloc_302_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_298_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3(lean_object* v_toApplicative_305_, lean_object* v_a_306_, lean_object* v_inst_307_, lean_object* v_toBind_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_fst_310_; lean_object* v_snd_311_; lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_fst_310_ = lean_ctor_get(v_a_309_, 0);
lean_inc(v_fst_310_);
v_snd_311_ = lean_ctor_get(v_a_309_, 1);
lean_inc(v_snd_311_);
lean_dec_ref(v_a_309_);
v___f_312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_312_, 0, v_snd_311_);
v___f_313_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_313_, 0, v_toApplicative_305_);
lean_closure_set(v___f_313_, 1, v_fst_310_);
lean_inc(v_a_306_);
v___x_314_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_314_, 0, lean_box(0));
lean_closure_set(v___x_314_, 1, lean_box(0));
lean_closure_set(v___x_314_, 2, lean_box(0));
lean_closure_set(v___x_314_, 3, v_a_306_);
lean_closure_set(v___x_314_, 4, v___f_312_);
v___x_315_ = lean_apply_2(v_inst_307_, lean_box(0), v___x_314_);
v___x_316_ = lean_apply_4(v_toBind_308_, lean_box(0), lean_box(0), v___x_315_, v___f_313_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3___boxed(lean_object* v_toApplicative_317_, lean_object* v_a_318_, lean_object* v_inst_319_, lean_object* v_toBind_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3(v_toApplicative_317_, v_a_318_, v_inst_319_, v_toBind_320_, v_a_321_);
lean_dec(v_a_318_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2(lean_object* v_a_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_st_mk_ref(v_a_323_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2___boxed(lean_object* v_a_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2(v_a_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4(lean_object* v_x_348_, lean_object* v___x_349_, lean_object* v_ref_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
lean_inc(v___y_359_);
lean_inc_ref(v___y_358_);
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
lean_inc(v___y_351_);
lean_inc(v_ref_350_);
v___x_361_ = lean_apply_12(v_x_348_, v___x_349_, v_ref_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, lean_box(0));
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_371_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_371_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = lean_st_ref_get(v_ref_350_);
lean_dec(v_ref_350_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_a_362_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_ref_350_);
v_a_372_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_361_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_361_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4___boxed(lean_object* v_x_380_, lean_object* v___x_381_, lean_object* v_ref_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4(v_x_380_, v___x_381_, v_ref_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5(lean_object* v_config_396_, lean_object* v_x_397_, lean_object* v___x_398_, lean_object* v_inst_399_, lean_object* v_toBind_400_, lean_object* v___f_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___f_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___f_403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__2___boxed), 11, 1);
lean_closure_set(v___f_403_, 0, v_a_402_);
v___x_404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0));
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_config_396_);
v___f_406_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__4___boxed), 13, 2);
lean_closure_set(v___f_406_, 0, v_x_397_);
lean_closure_set(v___f_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_407_, 0, lean_box(0));
lean_closure_set(v___x_407_, 1, lean_box(0));
lean_closure_set(v___x_407_, 2, v___x_398_);
lean_closure_set(v___x_407_, 3, lean_box(0));
lean_closure_set(v___x_407_, 4, lean_box(0));
lean_closure_set(v___x_407_, 5, v___f_403_);
lean_closure_set(v___x_407_, 6, v___f_406_);
v___x_408_ = lean_apply_2(v_inst_399_, lean_box(0), v___x_407_);
v___x_409_ = lean_apply_4(v_toBind_400_, lean_box(0), lean_box(0), v___x_408_, v___f_401_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6(lean_object* v_x_410_, lean_object* v___x_411_, lean_object* v_inst_412_, lean_object* v_toBind_413_, lean_object* v___f_414_, lean_object* v_a_415_, lean_object* v___f_416_, lean_object* v_inst_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_ctx_419_; lean_object* v_config_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_ctx_419_ = lean_ctor_get(v_a_418_, 4);
lean_inc_ref(v_ctx_419_);
lean_dec_ref(v_a_418_);
v_config_420_ = lean_ctor_get(v_ctx_419_, 5);
lean_inc_ref(v_config_420_);
lean_dec_ref(v_ctx_419_);
lean_inc(v_toBind_413_);
v___f_421_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5), 7, 6);
lean_closure_set(v___f_421_, 0, v_config_420_);
lean_closure_set(v___f_421_, 1, v_x_410_);
lean_closure_set(v___f_421_, 2, v___x_411_);
lean_closure_set(v___f_421_, 3, v_inst_412_);
lean_closure_set(v___f_421_, 4, v_toBind_413_);
lean_closure_set(v___f_421_, 5, v___f_414_);
lean_inc(v_a_415_);
v___x_422_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_422_, 0, lean_box(0));
lean_closure_set(v___x_422_, 1, lean_box(0));
lean_closure_set(v___x_422_, 2, lean_box(0));
lean_closure_set(v___x_422_, 3, v_a_415_);
lean_closure_set(v___x_422_, 4, v___f_416_);
v___x_423_ = lean_apply_2(v_inst_417_, lean_box(0), v___x_422_);
v___x_424_ = lean_apply_4(v_toBind_413_, lean_box(0), lean_box(0), v___x_423_, v___f_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6___boxed(lean_object* v_x_425_, lean_object* v___x_426_, lean_object* v_inst_427_, lean_object* v_toBind_428_, lean_object* v___f_429_, lean_object* v_a_430_, lean_object* v___f_431_, lean_object* v_inst_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6(v_x_425_, v___x_426_, v_inst_427_, v_toBind_428_, v___f_429_, v_a_430_, v___f_431_, v_inst_432_, v_a_433_);
lean_dec(v_a_430_);
return v_res_434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0(void){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_instMonadEIO___redArg();
return v___x_435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__0);
v___x_437_ = l_StateRefT_x27_instMonad___redArg(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_x_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_448_; lean_object* v_toApplicative_449_; lean_object* v_toFunctor_450_; lean_object* v_toSeq_451_; lean_object* v_toSeqLeft_452_; lean_object* v_toSeqRight_453_; lean_object* v___f_454_; lean_object* v___f_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___f_459_; lean_object* v___f_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_toApplicative_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_504_; 
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1);
v_toApplicative_449_ = lean_ctor_get(v___x_448_, 0);
v_toFunctor_450_ = lean_ctor_get(v_toApplicative_449_, 0);
v_toSeq_451_ = lean_ctor_get(v_toApplicative_449_, 2);
v_toSeqLeft_452_ = lean_ctor_get(v_toApplicative_449_, 3);
v_toSeqRight_453_ = lean_ctor_get(v_toApplicative_449_, 4);
v___f_454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2));
v___f_455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_450_, 2);
v___f_456_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_456_, 0, v_toFunctor_450_);
v___f_457_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_457_, 0, v_toFunctor_450_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___f_456_);
lean_ctor_set(v___x_458_, 1, v___f_457_);
lean_inc(v_toSeqRight_453_);
v___f_459_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_459_, 0, v_toSeqRight_453_);
lean_inc(v_toSeqLeft_452_);
v___f_460_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_460_, 0, v_toSeqLeft_452_);
lean_inc(v_toSeq_451_);
v___f_461_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_461_, 0, v_toSeq_451_);
v___x_462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_462_, 0, v___x_458_);
lean_ctor_set(v___x_462_, 1, v___f_454_);
lean_ctor_set(v___x_462_, 2, v___f_461_);
lean_ctor_set(v___x_462_, 3, v___f_460_);
lean_ctor_set(v___x_462_, 4, v___f_459_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___f_455_);
v___x_464_ = l_StateRefT_x27_instMonad___redArg(v___x_463_);
v_toApplicative_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v___x_464_, 1);
lean_dec(v_unused_505_);
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_504_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_toApplicative_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_504_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_toFunctor_469_; lean_object* v_toSeq_470_; lean_object* v_toSeqLeft_471_; lean_object* v_toSeqRight_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_502_; 
v_toFunctor_469_ = lean_ctor_get(v_toApplicative_465_, 0);
v_toSeq_470_ = lean_ctor_get(v_toApplicative_465_, 2);
v_toSeqLeft_471_ = lean_ctor_get(v_toApplicative_465_, 3);
v_toSeqRight_472_ = lean_ctor_get(v_toApplicative_465_, 4);
v_isSharedCheck_502_ = !lean_is_exclusive(v_toApplicative_465_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_toApplicative_465_, 1);
lean_dec(v_unused_503_);
v___x_474_ = v_toApplicative_465_;
v_isShared_475_ = v_isSharedCheck_502_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_toSeqRight_472_);
lean_inc(v_toSeqLeft_471_);
lean_inc(v_toSeq_470_);
lean_inc(v_toFunctor_469_);
lean_dec(v_toApplicative_465_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_502_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___f_476_; lean_object* v___f_477_; lean_object* v___f_478_; lean_object* v___f_479_; lean_object* v___x_480_; lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___x_485_; 
v___f_476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4));
v___f_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5));
lean_inc_ref(v_toFunctor_469_);
v___f_478_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_478_, 0, v_toFunctor_469_);
v___f_479_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_479_, 0, v_toFunctor_469_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___f_478_);
lean_ctor_set(v___x_480_, 1, v___f_479_);
v___f_481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_481_, 0, v_toSeqRight_472_);
v___f_482_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_482_, 0, v_toSeqLeft_471_);
v___f_483_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_483_, 0, v_toSeq_470_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 4, v___f_481_);
lean_ctor_set(v___x_474_, 3, v___f_482_);
lean_ctor_set(v___x_474_, 2, v___f_483_);
lean_ctor_set(v___x_474_, 1, v___f_476_);
lean_ctor_set(v___x_474_, 0, v___x_480_);
v___x_485_ = v___x_474_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___f_476_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v___f_483_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v___f_482_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v___f_481_);
v___x_485_ = v_reuseFailAlloc_501_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v___f_477_);
lean_ctor_set(v___x_467_, 0, v___x_485_);
v___x_487_ = v___x_467_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___f_477_);
v___x_487_ = v_reuseFailAlloc_500_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_toApplicative_492_; lean_object* v_toBind_493_; lean_object* v___f_494_; lean_object* v___f_495_; lean_object* v___f_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_488_ = l_StateRefT_x27_instMonad___redArg(v___x_487_);
v___x_489_ = l_ReaderT_instMonad___redArg(v___x_488_);
v___x_490_ = l_StateRefT_x27_instMonad___redArg(v___x_489_);
v___x_491_ = l_ReaderT_instMonad___redArg(v___x_490_);
v_toApplicative_492_ = lean_ctor_get(v_inst_443_, 0);
lean_inc_ref(v_toApplicative_492_);
v_toBind_493_ = lean_ctor_get(v_inst_443_, 1);
lean_inc_n(v_toBind_493_, 3);
lean_dec_ref(v_inst_443_);
v___f_494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__6));
lean_inc_n(v_inst_445_, 2);
lean_inc_n(v_a_447_, 3);
v___f_495_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_495_, 0, v_toApplicative_492_);
lean_closure_set(v___f_495_, 1, v_a_447_);
lean_closure_set(v___f_495_, 2, v_inst_445_);
lean_closure_set(v___f_495_, 3, v_toBind_493_);
v___f_496_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_496_, 0, v_x_446_);
lean_closure_set(v___f_496_, 1, v___x_491_);
lean_closure_set(v___f_496_, 2, v_inst_444_);
lean_closure_set(v___f_496_, 3, v_toBind_493_);
lean_closure_set(v___f_496_, 4, v___f_495_);
lean_closure_set(v___f_496_, 5, v_a_447_);
lean_closure_set(v___f_496_, 6, v___f_494_);
lean_closure_set(v___f_496_, 7, v_inst_445_);
v___x_497_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_497_, 0, lean_box(0));
lean_closure_set(v___x_497_, 1, lean_box(0));
lean_closure_set(v___x_497_, 2, v_a_447_);
v___x_498_ = lean_apply_2(v_inst_445_, lean_box(0), v___x_497_);
v___x_499_ = lean_apply_4(v_toBind_493_, lean_box(0), lean_box(0), v___x_498_, v___f_496_);
return v___x_499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___boxed(lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_x_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_506_, v_inst_507_, v_inst_508_, v_x_509_, v_a_510_);
lean_dec(v_a_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM(lean_object* v_00_u03c3_512_, lean_object* v_m_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_00_u03b1_518_, lean_object* v_x_519_, lean_object* v_a_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_515_, v_inst_516_, v_inst_517_, v_x_519_, v_a_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___boxed(lean_object* v_00_u03c3_522_, lean_object* v_m_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_00_u03b1_528_, lean_object* v_x_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM(v_00_u03c3_522_, v_m_523_, v_inst_524_, v_inst_525_, v_inst_526_, v_inst_527_, v_00_u03b1_528_, v_x_529_, v_a_530_);
lean_dec(v_a_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__0(lean_object* v_s_532_){
_start:
{
lean_object* v_reifyState_533_; lean_object* v_preProcessState_534_; lean_object* v_bvSolver_535_; lean_object* v_mvar_536_; lean_object* v_ctx_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_546_; 
v_reifyState_533_ = lean_ctor_get(v_s_532_, 0);
v_preProcessState_534_ = lean_ctor_get(v_s_532_, 1);
v_bvSolver_535_ = lean_ctor_get(v_s_532_, 2);
v_mvar_536_ = lean_ctor_get(v_s_532_, 3);
v_ctx_537_ = lean_ctor_get(v_s_532_, 4);
v_isSharedCheck_546_ = !lean_is_exclusive(v_s_532_);
if (v_isSharedCheck_546_ == 0)
{
v___x_539_ = v_s_532_;
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_ctx_537_);
lean_inc(v_mvar_536_);
lean_inc(v_bvSolver_535_);
lean_inc(v_preProcessState_534_);
lean_inc(v_reifyState_533_);
lean_dec(v_s_532_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_reifyState_533_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_bvSolver_535_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_mvar_536_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_ctx_537_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_preProcessState_534_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1(lean_object* v_snd_547_, lean_object* v_s_548_){
_start:
{
lean_object* v_reifyState_549_; lean_object* v_bvSolver_550_; lean_object* v_mvar_551_; lean_object* v_ctx_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_562_; 
v_reifyState_549_ = lean_ctor_get(v_s_548_, 0);
v_bvSolver_550_ = lean_ctor_get(v_s_548_, 2);
v_mvar_551_ = lean_ctor_get(v_s_548_, 3);
v_ctx_552_ = lean_ctor_get(v_s_548_, 4);
v_isSharedCheck_562_ = !lean_is_exclusive(v_s_548_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v_s_548_, 1);
lean_dec(v_unused_563_);
v___x_554_ = v_s_548_;
v_isShared_555_ = v_isSharedCheck_562_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_ctx_552_);
lean_inc(v_mvar_551_);
lean_inc(v_bvSolver_550_);
lean_inc(v_reifyState_549_);
lean_dec(v_s_548_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_562_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_caches_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v_caches_556_ = lean_ctor_get(v_snd_547_, 0);
v___x_557_ = lean_box(0);
lean_inc_ref(v_caches_556_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v_caches_556_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_reifyState_549_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_caches_556_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_bvSolver_550_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_mvar_551_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_ctx_552_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_557_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1___boxed(lean_object* v_snd_564_, lean_object* v_s_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1(v_snd_564_, v_s_565_);
lean_dec_ref(v_snd_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3(lean_object* v_toApplicative_567_, lean_object* v_a_568_, lean_object* v_inst_569_, lean_object* v_toBind_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_fst_572_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v_a_571_, 1);
lean_inc(v_snd_573_);
lean_dec_ref(v_a_571_);
v___f_574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_574_, 0, v_snd_573_);
v___f_575_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg___lam__1), 3, 2);
lean_closure_set(v___f_575_, 0, v_toApplicative_567_);
lean_closure_set(v___f_575_, 1, v_fst_572_);
lean_inc(v_a_568_);
v___x_576_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_576_, 0, lean_box(0));
lean_closure_set(v___x_576_, 1, lean_box(0));
lean_closure_set(v___x_576_, 2, lean_box(0));
lean_closure_set(v___x_576_, 3, v_a_568_);
lean_closure_set(v___x_576_, 4, v___f_574_);
v___x_577_ = lean_apply_2(v_inst_569_, lean_box(0), v___x_576_);
v___x_578_ = lean_apply_4(v_toBind_570_, lean_box(0), lean_box(0), v___x_577_, v___f_575_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3___boxed(lean_object* v_toApplicative_579_, lean_object* v_a_580_, lean_object* v_inst_581_, lean_object* v_toBind_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3(v_toApplicative_579_, v_a_580_, v_inst_581_, v_toBind_582_, v_a_583_);
lean_dec(v_a_580_);
return v_res_584_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_box(0);
v___x_586_ = lean_unsigned_to_nat(16u);
v___x_587_ = lean_mk_array(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__0);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__1);
v___x_592_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
lean_ctor_set(v___x_592_, 2, v___x_591_);
lean_ctor_set(v___x_592_, 3, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2(lean_object* v_a_593_, lean_object* v_x_594_, lean_object* v___x_595_, lean_object* v_target_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_typeAnalysis_616_; lean_object* v_target_617_; lean_object* v_hypotheses_618_; uint8_t v_didChange_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_646_; 
v___x_607_ = l_Lean_Expr_mvarId_x21(v_target_596_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__7);
v___x_610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___closed__2);
v___x_611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___lam__5___closed__0));
v___x_612_ = 0;
v___x_613_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_613_, 0, v___x_609_);
lean_ctor_set(v___x_613_, 1, v___x_610_);
lean_ctor_set(v___x_613_, 2, v___x_608_);
lean_ctor_set(v___x_613_, 3, v___x_611_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*4, v___x_612_);
v___x_614_ = lean_st_mk_ref(v___x_613_);
v___x_615_ = lean_st_ref_take(v___x_614_);
v_typeAnalysis_616_ = lean_ctor_get(v___x_615_, 1);
v_target_617_ = lean_ctor_get(v___x_615_, 2);
v_hypotheses_618_ = lean_ctor_get(v___x_615_, 3);
v_didChange_619_ = lean_ctor_get_uint8(v___x_615_, sizeof(void*)*4);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v___x_615_, 0);
lean_dec(v_unused_647_);
v___x_621_ = v___x_615_;
v_isShared_622_ = v_isSharedCheck_646_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_hypotheses_618_);
lean_inc(v_target_617_);
lean_inc(v_typeAnalysis_616_);
lean_dec(v___x_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_646_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_a_593_);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_593_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_typeAnalysis_616_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_target_617_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_hypotheses_618_);
lean_ctor_set_uint8(v_reuseFailAlloc_645_, sizeof(void*)*4, v_didChange_619_);
v___x_624_ = v_reuseFailAlloc_645_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_st_ref_put(v___x_614_, v___x_624_);
lean_inc(v___y_605_);
lean_inc_ref(v___y_604_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_597_);
lean_inc(v___x_614_);
v___x_626_ = lean_apply_12(v_x_594_, v___x_595_, v___x_614_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, lean_box(0));
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_636_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_636_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_636_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_636_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_631_ = lean_st_ref_get(v___x_614_);
lean_dec(v___x_614_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_a_627_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_632_);
v___x_634_ = v___x_629_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v___x_614_);
v_a_637_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_626_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_626_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___boxed(lean_object* v_a_648_, lean_object* v_x_649_, lean_object* v___x_650_, lean_object* v_target_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2(v_a_648_, v_x_649_, v___x_650_, v_target_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v_target_651_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4(lean_object* v___x_663_, uint8_t v___x_664_, lean_object* v___x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_mkFreshExprMVar(v___x_663_, v___x_664_, v___x_665_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4___boxed(lean_object* v___x_677_, lean_object* v___x_678_, lean_object* v___x_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
uint8_t v___x_1833__boxed_690_; lean_object* v_res_691_; 
v___x_1833__boxed_690_ = lean_unbox(v___x_678_);
v_res_691_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4(v___x_677_, v___x_1833__boxed_690_, v___x_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
return v_res_691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_box(0);
v___x_696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__1));
v___x_697_ = l_Lean_mkConst(v___x_696_, v___x_695_);
return v___x_697_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__2);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___f_704_; 
v___x_700_ = lean_box(0);
v___x_701_ = 0;
v___x_702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__3);
v___x_703_ = lean_box(v___x_701_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__4___boxed), 13, 3);
lean_closure_set(v___f_704_, 0, v___x_702_);
lean_closure_set(v___f_704_, 1, v___x_703_);
lean_closure_set(v___f_704_, 2, v___x_700_);
return v___f_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5(lean_object* v_x_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v_mvar_709_, lean_object* v___x_710_, lean_object* v_inst_711_, lean_object* v_toBind_712_, lean_object* v___f_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___f_715_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__2___boxed), 14, 3);
lean_closure_set(v___f_715_, 0, v_a_714_);
lean_closure_set(v___f_715_, 1, v_x_705_);
lean_closure_set(v___f_715_, 2, v___x_706_);
v___f_716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5___closed__4);
v___x_717_ = l_Lean_MVarId_withContext___redArg(v___x_707_, v___x_708_, v_mvar_709_, v___f_716_);
v___x_718_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_718_, 0, lean_box(0));
lean_closure_set(v___x_718_, 1, lean_box(0));
lean_closure_set(v___x_718_, 2, v___x_710_);
lean_closure_set(v___x_718_, 3, lean_box(0));
lean_closure_set(v___x_718_, 4, lean_box(0));
lean_closure_set(v___x_718_, 5, v___x_717_);
lean_closure_set(v___x_718_, 6, v___f_715_);
v___x_719_ = lean_apply_2(v_inst_711_, lean_box(0), v___x_718_);
v___x_720_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_719_, v___f_713_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6(lean_object* v_x_721_, lean_object* v___x_722_, lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v___x_725_, lean_object* v_inst_726_, lean_object* v_toBind_727_, lean_object* v___f_728_, lean_object* v_a_729_, lean_object* v___f_730_, lean_object* v_inst_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_mvar_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_mvar_733_ = lean_ctor_get(v_a_732_, 3);
lean_inc(v_mvar_733_);
lean_dec_ref(v_a_732_);
lean_inc(v_toBind_727_);
v___f_734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__5), 10, 9);
lean_closure_set(v___f_734_, 0, v_x_721_);
lean_closure_set(v___f_734_, 1, v___x_722_);
lean_closure_set(v___f_734_, 2, v___x_723_);
lean_closure_set(v___f_734_, 3, v___x_724_);
lean_closure_set(v___f_734_, 4, v_mvar_733_);
lean_closure_set(v___f_734_, 5, v___x_725_);
lean_closure_set(v___f_734_, 6, v_inst_726_);
lean_closure_set(v___f_734_, 7, v_toBind_727_);
lean_closure_set(v___f_734_, 8, v___f_728_);
lean_inc(v_a_729_);
v___x_735_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_735_, 0, lean_box(0));
lean_closure_set(v___x_735_, 1, lean_box(0));
lean_closure_set(v___x_735_, 2, lean_box(0));
lean_closure_set(v___x_735_, 3, v_a_729_);
lean_closure_set(v___x_735_, 4, v___f_730_);
v___x_736_ = lean_apply_2(v_inst_731_, lean_box(0), v___x_735_);
v___x_737_ = lean_apply_4(v_toBind_727_, lean_box(0), lean_box(0), v___x_736_, v___f_734_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6___boxed(lean_object* v_x_738_, lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v_inst_743_, lean_object* v_toBind_744_, lean_object* v___f_745_, lean_object* v_a_746_, lean_object* v___f_747_, lean_object* v_inst_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6(v_x_738_, v___x_739_, v___x_740_, v___x_741_, v___x_742_, v_inst_743_, v_toBind_744_, v___f_745_, v_a_746_, v___f_747_, v_inst_748_, v_a_749_);
lean_dec(v_a_746_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7(lean_object* v_x_754_, lean_object* v___x_755_, lean_object* v___x_756_, lean_object* v___x_757_, lean_object* v_inst_758_, lean_object* v_toBind_759_, lean_object* v___f_760_, lean_object* v_a_761_, lean_object* v___f_762_, lean_object* v_inst_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_ctx_765_; lean_object* v___x_766_; lean_object* v_config_767_; lean_object* v_mode_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_ctx_765_ = lean_ctor_get(v_a_764_, 4);
lean_inc_ref(v_ctx_765_);
lean_dec_ref(v_a_764_);
v___x_766_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_ctx_765_);
v_config_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc_ref(v_config_767_);
v_mode_768_ = lean_ctor_get(v___x_766_, 1);
lean_inc(v_mode_768_);
lean_dec_ref(v___x_766_);
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___closed__0));
v___x_770_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_768_, v_config_767_, v___x_769_);
lean_inc(v_inst_763_);
lean_inc_n(v_a_761_, 2);
lean_inc(v_toBind_759_);
v___f_771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__6___boxed), 12, 11);
lean_closure_set(v___f_771_, 0, v_x_754_);
lean_closure_set(v___f_771_, 1, v___x_770_);
lean_closure_set(v___f_771_, 2, v___x_755_);
lean_closure_set(v___f_771_, 3, v___x_756_);
lean_closure_set(v___f_771_, 4, v___x_757_);
lean_closure_set(v___f_771_, 5, v_inst_758_);
lean_closure_set(v___f_771_, 6, v_toBind_759_);
lean_closure_set(v___f_771_, 7, v___f_760_);
lean_closure_set(v___f_771_, 8, v_a_761_);
lean_closure_set(v___f_771_, 9, v___f_762_);
lean_closure_set(v___f_771_, 10, v_inst_763_);
v___x_772_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_772_, 0, lean_box(0));
lean_closure_set(v___x_772_, 1, lean_box(0));
lean_closure_set(v___x_772_, 2, v_a_761_);
v___x_773_ = lean_apply_2(v_inst_763_, lean_box(0), v___x_772_);
v___x_774_ = lean_apply_4(v_toBind_759_, lean_box(0), lean_box(0), v___x_773_, v___f_771_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___boxed(lean_object* v_x_775_, lean_object* v___x_776_, lean_object* v___x_777_, lean_object* v___x_778_, lean_object* v_inst_779_, lean_object* v_toBind_780_, lean_object* v___f_781_, lean_object* v_a_782_, lean_object* v___f_783_, lean_object* v_inst_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7(v_x_775_, v___x_776_, v___x_777_, v___x_778_, v_inst_779_, v_toBind_780_, v___f_781_, v_a_782_, v___f_783_, v_inst_784_, v_a_785_);
lean_dec(v_a_782_);
return v_res_786_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0(void){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_instMonadControlReaderT___redArg();
return v___x_787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1(void){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_x_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_795_; lean_object* v_toApplicative_796_; lean_object* v_toFunctor_797_; lean_object* v_toSeq_798_; lean_object* v_toSeqLeft_799_; lean_object* v_toSeqRight_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_toApplicative_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_885_; 
v___x_795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1);
v_toApplicative_796_ = lean_ctor_get(v___x_795_, 0);
v_toFunctor_797_ = lean_ctor_get(v_toApplicative_796_, 0);
v_toSeq_798_ = lean_ctor_get(v_toApplicative_796_, 2);
v_toSeqLeft_799_ = lean_ctor_get(v_toApplicative_796_, 3);
v_toSeqRight_800_ = lean_ctor_get(v_toApplicative_796_, 4);
v___f_801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2));
v___f_802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_797_, 2);
v___f_803_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_803_, 0, v_toFunctor_797_);
v___f_804_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_804_, 0, v_toFunctor_797_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___f_803_);
lean_ctor_set(v___x_805_, 1, v___f_804_);
lean_inc(v_toSeqRight_800_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_806_, 0, v_toSeqRight_800_);
lean_inc(v_toSeqLeft_799_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_807_, 0, v_toSeqLeft_799_);
lean_inc(v_toSeq_798_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_808_, 0, v_toSeq_798_);
v___x_809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_809_, 0, v___x_805_);
lean_ctor_set(v___x_809_, 1, v___f_801_);
lean_ctor_set(v___x_809_, 2, v___f_808_);
lean_ctor_set(v___x_809_, 3, v___f_807_);
lean_ctor_set(v___x_809_, 4, v___f_806_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___f_802_);
v___x_811_ = l_StateRefT_x27_instMonad___redArg(v___x_810_);
v_toApplicative_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_811_, 1);
lean_dec(v_unused_886_);
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_885_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_toApplicative_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_885_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_toFunctor_816_; lean_object* v_toSeq_817_; lean_object* v_toSeqLeft_818_; lean_object* v_toSeqRight_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_883_; 
v_toFunctor_816_ = lean_ctor_get(v_toApplicative_812_, 0);
v_toSeq_817_ = lean_ctor_get(v_toApplicative_812_, 2);
v_toSeqLeft_818_ = lean_ctor_get(v_toApplicative_812_, 3);
v_toSeqRight_819_ = lean_ctor_get(v_toApplicative_812_, 4);
v_isSharedCheck_883_ = !lean_is_exclusive(v_toApplicative_812_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v_toApplicative_812_, 1);
lean_dec(v_unused_884_);
v___x_821_ = v_toApplicative_812_;
v_isShared_822_ = v_isSharedCheck_883_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_toSeqRight_819_);
lean_inc(v_toSeqLeft_818_);
lean_inc(v_toSeq_817_);
lean_inc(v_toFunctor_816_);
lean_dec(v_toApplicative_812_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_883_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___f_823_; lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___x_832_; 
v___f_823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4));
v___f_824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5));
lean_inc_ref(v_toFunctor_816_);
v___f_825_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_825_, 0, v_toFunctor_816_);
v___f_826_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_826_, 0, v_toFunctor_816_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___f_825_);
lean_ctor_set(v___x_827_, 1, v___f_826_);
v___f_828_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_828_, 0, v_toSeqRight_819_);
v___f_829_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_829_, 0, v_toSeqLeft_818_);
v___f_830_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_830_, 0, v_toSeq_817_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 4, v___f_828_);
lean_ctor_set(v___x_821_, 3, v___f_829_);
lean_ctor_set(v___x_821_, 2, v___f_830_);
lean_ctor_set(v___x_821_, 1, v___f_823_);
lean_ctor_set(v___x_821_, 0, v___x_827_);
v___x_832_ = v___x_821_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___f_823_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v___f_830_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v___f_829_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v___f_828_);
v___x_832_ = v_reuseFailAlloc_882_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_834_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___f_824_);
lean_ctor_set(v___x_814_, 0, v___x_832_);
v___x_834_ = v___x_814_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___f_824_);
v___x_834_ = v_reuseFailAlloc_881_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_toApplicative_842_; lean_object* v_toFunctor_843_; lean_object* v_toSeq_844_; lean_object* v_toSeqLeft_845_; lean_object* v_toSeqRight_846_; lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___x_849_; lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___x_863_; lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___x_869_; lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v_toApplicative_873_; lean_object* v_toBind_874_; lean_object* v___f_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_835_ = l_StateRefT_x27_instMonad___redArg(v___x_834_);
v___x_836_ = l_ReaderT_instMonad___redArg(v___x_835_);
v___x_837_ = l_StateRefT_x27_instMonad___redArg(v___x_836_);
v___x_838_ = l_ReaderT_instMonad___redArg(v___x_837_);
lean_inc_ref(v___x_838_);
v___x_839_ = l_ReaderT_instMonad___redArg(v___x_838_);
v___x_840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__0);
v___x_841_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__1);
v_toApplicative_842_ = lean_ctor_get(v___x_795_, 0);
v_toFunctor_843_ = lean_ctor_get(v_toApplicative_842_, 0);
v_toSeq_844_ = lean_ctor_get(v_toApplicative_842_, 2);
v_toSeqLeft_845_ = lean_ctor_get(v_toApplicative_842_, 3);
v_toSeqRight_846_ = lean_ctor_get(v_toApplicative_842_, 4);
lean_inc_ref_n(v_toFunctor_843_, 2);
v___f_847_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_847_, 0, v_toFunctor_843_);
v___f_848_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_848_, 0, v_toFunctor_843_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___f_847_);
lean_ctor_set(v___x_849_, 1, v___f_848_);
lean_inc(v_toSeqRight_846_);
v___f_850_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_850_, 0, v_toSeqRight_846_);
lean_inc(v_toSeqLeft_845_);
v___f_851_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_851_, 0, v_toSeqLeft_845_);
lean_inc(v_toSeq_844_);
v___f_852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_852_, 0, v_toSeq_844_);
v___x_853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_853_, 0, v___x_849_);
lean_ctor_set(v___x_853_, 1, v___f_801_);
lean_ctor_set(v___x_853_, 2, v___f_852_);
lean_ctor_set(v___x_853_, 3, v___f_851_);
lean_ctor_set(v___x_853_, 4, v___f_850_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___f_802_);
v___x_855_ = l_StateRefT_x27_instMonad___redArg(v___x_854_);
v___x_856_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_856_, 0, lean_box(0));
lean_closure_set(v___x_856_, 1, lean_box(0));
lean_closure_set(v___x_856_, 2, v___x_855_);
v___x_857_ = l_instMonadControlTOfPure___redArg(v___x_856_);
lean_inc_ref(v___x_857_);
v___f_858_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_858_, 0, v___x_841_);
lean_closure_set(v___f_858_, 1, v___x_857_);
v___f_859_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_859_, 0, v___x_841_);
lean_closure_set(v___f_859_, 1, v___x_857_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___f_858_);
lean_ctor_set(v___x_860_, 1, v___f_859_);
lean_inc_ref(v___x_860_);
v___f_861_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_861_, 0, v___x_840_);
lean_closure_set(v___f_861_, 1, v___x_860_);
v___f_862_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_862_, 0, v___x_840_);
lean_closure_set(v___f_862_, 1, v___x_860_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___f_861_);
lean_ctor_set(v___x_863_, 1, v___f_862_);
lean_inc_ref(v___x_863_);
v___f_864_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_864_, 0, v___x_841_);
lean_closure_set(v___f_864_, 1, v___x_863_);
v___f_865_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_865_, 0, v___x_841_);
lean_closure_set(v___f_865_, 1, v___x_863_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___f_864_);
lean_ctor_set(v___x_866_, 1, v___f_865_);
lean_inc_ref(v___x_866_);
v___f_867_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_867_, 0, v___x_840_);
lean_closure_set(v___f_867_, 1, v___x_866_);
v___f_868_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_868_, 0, v___x_840_);
lean_closure_set(v___f_868_, 1, v___x_866_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___f_867_);
lean_ctor_set(v___x_869_, 1, v___f_868_);
lean_inc_ref(v___x_869_);
v___f_870_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_870_, 0, v___x_840_);
lean_closure_set(v___f_870_, 1, v___x_869_);
v___f_871_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_871_, 0, v___x_840_);
lean_closure_set(v___f_871_, 1, v___x_869_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___f_870_);
lean_ctor_set(v___x_872_, 1, v___f_871_);
v_toApplicative_873_ = lean_ctor_get(v_inst_790_, 0);
lean_inc_ref(v_toApplicative_873_);
v_toBind_874_ = lean_ctor_get(v_inst_790_, 1);
lean_inc_n(v_toBind_874_, 3);
lean_dec_ref(v_inst_790_);
v___f_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___closed__2));
lean_inc_n(v_inst_792_, 2);
lean_inc_n(v_a_794_, 3);
v___f_876_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_876_, 0, v_toApplicative_873_);
lean_closure_set(v___f_876_, 1, v_a_794_);
lean_closure_set(v___f_876_, 2, v_inst_792_);
lean_closure_set(v___f_876_, 3, v_toBind_874_);
v___f_877_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_877_, 0, v_x_793_);
lean_closure_set(v___f_877_, 1, v___x_872_);
lean_closure_set(v___f_877_, 2, v___x_839_);
lean_closure_set(v___f_877_, 3, v___x_838_);
lean_closure_set(v___f_877_, 4, v_inst_791_);
lean_closure_set(v___f_877_, 5, v_toBind_874_);
lean_closure_set(v___f_877_, 6, v___f_876_);
lean_closure_set(v___f_877_, 7, v_a_794_);
lean_closure_set(v___f_877_, 8, v___f_875_);
lean_closure_set(v___f_877_, 9, v_inst_792_);
v___x_878_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_878_, 0, lean_box(0));
lean_closure_set(v___x_878_, 1, lean_box(0));
lean_closure_set(v___x_878_, 2, v_a_794_);
v___x_879_ = lean_apply_2(v_inst_792_, lean_box(0), v___x_878_);
v___x_880_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_879_, v___f_877_);
return v___x_880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg___boxed(lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_x_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(v_inst_887_, v_inst_888_, v_inst_889_, v_x_890_, v_a_891_);
lean_dec(v_a_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM(lean_object* v_00_u03c3_893_, lean_object* v_m_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_00_u03b1_899_, lean_object* v_x_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(v_inst_896_, v_inst_897_, v_inst_898_, v_x_900_, v_a_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___boxed(lean_object* v_00_u03c3_903_, lean_object* v_m_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_00_u03b1_909_, lean_object* v_x_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM(v_00_u03c3_903_, v_m_904_, v_inst_905_, v_inst_906_, v_inst_907_, v_inst_908_, v_00_u03b1_909_, v_x_910_, v_a_911_);
lean_dec(v_a_911_);
return v_res_912_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__3));
v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0(lean_object* v___x_920_, lean_object* v___x_921_, lean_object* v_hyp_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__0));
v___x_937_ = l_Lean_Core_checkSystem(v___x_936_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_955_; 
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v___x_937_, 0);
lean_dec(v_unused_956_);
v___x_939_ = v___x_937_;
v_isShared_940_ = v_isSharedCheck_955_;
goto v_resetjp_938_;
}
else
{
lean_dec(v___x_937_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_955_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_type_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_type_941_ = lean_ctor_get(v_hyp_922_, 1);
lean_inc_ref(v_type_941_);
v___x_942_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__2));
v___x_943_ = l_Lean_Expr_isConstOf(v_type_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
lean_del_object(v___x_939_);
v___x_944_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_hyp_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
if (lean_obj_tag(v_a_945_) == 1)
{
lean_dec_ref(v_type_941_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
return v___x_944_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_3561__overap_949_; lean_object* v___x_950_; 
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___closed__4);
v___x_947_ = l_Lean_MessageData_ofExpr(v_type_941_);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_3561__overap_949_ = l_Lean_throwError___redArg(v___x_920_, v___x_921_, v___x_948_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
v___x_950_ = lean_apply_13(v___x_3561__overap_949_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, lean_box(0));
return v___x_950_;
}
}
else
{
lean_dec_ref(v_type_941_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
return v___x_944_;
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec_ref(v_type_941_);
lean_dec_ref(v_hyp_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v___x_951_ = lean_box(0);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_951_);
v___x_953_ = v___x_939_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v_hyp_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v_a_957_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_937_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_937_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___boxed(lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v_hyp_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0(v___x_965_, v___x_966_, v_hyp_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__1(lean_object* v_x_982_){
_start:
{
lean_object* v_bvExpr_983_; 
v_bvExpr_983_ = lean_ctor_get(v_x_982_, 0);
lean_inc_ref(v_bvExpr_983_);
return v_bvExpr_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__1___boxed(lean_object* v_x_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__1(v_x_984_);
lean_dec_ref(v_x_984_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2(lean_object* v___f_1005_, lean_object* v_____x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_fst_1019_; lean_object* v_snd_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; size_t v_sz_1023_; size_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_fst_1019_ = lean_ctor_get(v_____x_1006_, 0);
lean_inc(v_fst_1019_);
v_snd_1020_ = lean_ctor_get(v_____x_1006_, 1);
lean_inc(v_snd_1020_);
lean_dec_ref(v_____x_1006_);
v___x_1021_ = l_Array_append___redArg(v_snd_1020_, v_fst_1019_);
lean_dec(v_fst_1019_);
v___x_1022_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___closed__9));
v_sz_1023_ = lean_array_size(v___x_1021_);
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1022_, v___f_1005_, v_sz_1023_, v___x_1024_, v___x_1021_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2___boxed(lean_object* v___f_1027_, lean_object* v_____x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__2(v___f_1027_, v_____x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__3(lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_BvSolverM_push___boxed), 10, 1);
lean_closure_set(v___x_1047_, 0, v_a_1046_);
v___x_1048_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_1042_, v_inst_1043_, v_inst_1044_, v___x_1047_, v_a_1045_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__3___boxed(lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__3(v_inst_1049_, v_inst_1050_, v_inst_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1052_);
return v_res_1054_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__2(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___f_1058_; 
v___x_1057_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1058_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1058_, 0, v___x_1057_);
return v___f_1058_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__3(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___f_1060_; 
v___x_1059_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1060_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1060_, 0, v___x_1059_);
return v___f_1060_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4(void){
_start:
{
lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; 
v___f_1061_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__3);
v___f_1062_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__2);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___f_1062_);
lean_ctor_set(v___x_1063_, 1, v___f_1061_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__5(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___f_1065_; 
v___x_1064_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4);
v___f_1065_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1065_, 0, v___x_1064_);
return v___f_1065_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__6(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___f_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__4);
v___f_1067_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1067_, 0, v___x_1066_);
return v___f_1067_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7(void){
_start:
{
lean_object* v___f_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; 
v___f_1068_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__6);
v___f_1069_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__5);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___f_1069_);
lean_ctor_set(v___x_1070_, 1, v___f_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__8(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___f_1072_; 
v___x_1071_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7);
v___f_1072_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1072_, 0, v___x_1071_);
return v___f_1072_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__9(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___f_1074_; 
v___x_1073_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__7);
v___f_1074_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1074_, 0, v___x_1073_);
return v___f_1074_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10(void){
_start:
{
lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; 
v___f_1075_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__9);
v___f_1076_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__8);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___f_1076_);
lean_ctor_set(v___x_1077_, 1, v___f_1075_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__11(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___f_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10);
v___f_1079_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1079_, 0, v___x_1078_);
return v___f_1079_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__12(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___f_1081_; 
v___x_1080_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__10);
v___f_1081_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1081_, 0, v___x_1080_);
return v___f_1081_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13(void){
_start:
{
lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___f_1082_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__12, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__12);
v___f_1083_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__11, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__11);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___f_1083_);
lean_ctor_set(v___x_1084_, 1, v___f_1082_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__14(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___f_1086_; 
v___x_1085_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13);
v___f_1086_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1086_, 0, v___x_1085_);
return v___f_1086_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__15(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___f_1088_; 
v___x_1087_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__13);
v___f_1088_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1088_, 0, v___x_1087_);
return v___f_1088_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16(void){
_start:
{
lean_object* v___f_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; 
v___f_1089_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__15);
v___f_1090_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__14, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__14);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___f_1090_);
lean_ctor_set(v___x_1091_, 1, v___f_1089_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__17(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___f_1093_; 
v___x_1092_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16);
v___f_1093_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1093_, 0, v___x_1092_);
return v___f_1093_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__18(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___f_1095_; 
v___x_1094_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__16);
v___f_1095_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1095_, 0, v___x_1094_);
return v___f_1095_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19(void){
_start:
{
lean_object* v___f_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; 
v___f_1096_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__18, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__18);
v___f_1097_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__17, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__17);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___f_1097_);
lean_ctor_set(v___x_1098_, 1, v___f_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__20(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___f_1100_; 
v___x_1099_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19);
v___f_1100_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1100_, 0, v___x_1099_);
return v___f_1100_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__21(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___f_1102_; 
v___x_1101_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__19);
v___f_1102_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1102_, 0, v___x_1101_);
return v___f_1102_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22(void){
_start:
{
lean_object* v___f_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; 
v___f_1103_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__21, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__21);
v___f_1104_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__20, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__20);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___f_1104_);
lean_ctor_set(v___x_1105_, 1, v___f_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__23(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___f_1107_; 
v___x_1106_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22);
v___f_1107_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1107_, 0, v___x_1106_);
return v___f_1107_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__24(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___f_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__22);
v___f_1109_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1109_, 0, v___x_1108_);
return v___f_1109_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25(void){
_start:
{
lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___f_1110_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__24, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__24);
v___f_1111_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__23, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__23);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___f_1111_);
lean_ctor_set(v___x_1112_, 1, v___f_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__26(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___f_1114_; 
v___x_1113_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25);
v___f_1114_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1114_, 0, v___x_1113_);
return v___f_1114_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__27(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___f_1116_; 
v___x_1115_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__25);
v___f_1116_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1116_, 0, v___x_1115_);
return v___f_1116_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28(void){
_start:
{
lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v___x_1119_; 
v___f_1117_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__27, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__27);
v___f_1118_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__26, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__26_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__26);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___f_1118_);
lean_ctor_set(v___x_1119_, 1, v___f_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__29(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___f_1121_; 
v___x_1120_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28);
v___f_1121_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1121_, 0, v___x_1120_);
return v___f_1121_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__30(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___f_1123_; 
v___x_1122_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__28);
v___f_1123_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1123_, 0, v___x_1122_);
return v___f_1123_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__31(void){
_start:
{
lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; 
v___f_1124_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__30, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__30);
v___f_1125_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__29, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__29);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___f_1125_);
lean_ctor_set(v___x_1126_, 1, v___f_1124_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__34(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1130_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___x_1131_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__32));
v___x_1132_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1131_, v___x_1130_, v___x_1129_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__35(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; 
v___x_1133_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__34, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__34);
v___f_1134_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1135_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__33));
v___x_1136_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1135_, v___f_1134_, v___x_1133_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__36(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1137_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__35, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__35);
v___x_1138_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___x_1139_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__32));
v___x_1140_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1139_, v___x_1138_, v___x_1137_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__37(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___f_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; 
v___x_1141_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__36, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__36_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__36);
v___f_1142_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1143_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__33));
v___x_1144_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1143_, v___f_1142_, v___x_1141_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__38(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__37, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__37);
v___x_1146_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___x_1147_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__32));
v___x_1148_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1147_, v___x_1146_, v___x_1145_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__39(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; 
v___x_1149_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__38, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__38_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__38);
v___f_1150_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1151_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__33));
v___x_1152_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1151_, v___f_1150_, v___x_1149_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__40(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___f_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; 
v___x_1153_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__39, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__39_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__39);
v___f_1154_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1155_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__33));
v___x_1156_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1155_, v___f_1154_, v___x_1153_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__41(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1157_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__40, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__40_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__40);
v___x_1158_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___x_1159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__32));
v___x_1160_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1159_, v___x_1158_, v___x_1157_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__42(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___x_1161_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__41, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__41_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__41);
v___f_1162_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1163_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__33));
v___x_1164_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1163_, v___f_1162_, v___x_1161_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__43(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1165_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__42, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__42_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__42);
v___x_1166_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___x_1167_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__32));
v___x_1168_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1167_, v___x_1166_, v___x_1165_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__44(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___f_1171_; 
v___x_1169_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___x_1170_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1171_, 0, v___x_1170_);
lean_closure_set(v___f_1171_, 1, v___x_1169_);
return v___f_1171_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__45(void){
_start:
{
lean_object* v___f_1172_; lean_object* v___f_1173_; lean_object* v___f_1174_; 
v___f_1172_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1173_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__44, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__44_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__44);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1174_, 0, v___f_1173_);
lean_closure_set(v___f_1174_, 1, v___f_1172_);
return v___f_1174_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__46(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___f_1177_; 
v___x_1175_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___f_1176_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__45, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__45_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__45);
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1177_, 0, v___f_1176_);
lean_closure_set(v___f_1177_, 1, v___x_1175_);
return v___f_1177_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__47(void){
_start:
{
lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; 
v___f_1178_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1179_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__46, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__46_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__46);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1180_, 0, v___f_1179_);
lean_closure_set(v___f_1180_, 1, v___f_1178_);
return v___f_1180_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__48(void){
_start:
{
lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; 
v___f_1181_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1182_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__47, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__47_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__47);
v___f_1183_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1183_, 0, v___f_1182_);
lean_closure_set(v___f_1183_, 1, v___f_1181_);
return v___f_1183_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__49(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___f_1185_; lean_object* v___f_1186_; 
v___x_1184_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___f_1185_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__48, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__48_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__48);
v___f_1186_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1186_, 0, v___f_1185_);
lean_closure_set(v___f_1186_, 1, v___x_1184_);
return v___f_1186_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__50(void){
_start:
{
lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___f_1189_; 
v___f_1187_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__1));
v___f_1188_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__49, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__49_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__49);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1189_, 0, v___f_1188_);
lean_closure_set(v___f_1189_, 1, v___f_1187_);
return v___f_1189_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__51(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___f_1191_; lean_object* v___f_1192_; 
v___x_1190_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__0));
v___f_1191_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__50, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__50_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__50);
v___f_1192_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1192_, 0, v___f_1191_);
lean_closure_set(v___f_1192_, 1, v___x_1190_);
return v___f_1192_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__55(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___redArg___closed__1);
v___x_1199_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__52));
v___x_1200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1198_);
lean_ctor_set(v___x_1200_, 2, v___x_1198_);
lean_ctor_set(v___x_1200_, 3, v___x_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_hyps_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1207_; lean_object* v_toApplicative_1208_; lean_object* v_toFunctor_1209_; lean_object* v_toSeq_1210_; lean_object* v_toSeqLeft_1211_; lean_object* v_toSeqRight_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_toApplicative_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1277_; 
v___x_1207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1);
v_toApplicative_1208_ = lean_ctor_get(v___x_1207_, 0);
v_toFunctor_1209_ = lean_ctor_get(v_toApplicative_1208_, 0);
v_toSeq_1210_ = lean_ctor_get(v_toApplicative_1208_, 2);
v_toSeqLeft_1211_ = lean_ctor_get(v_toApplicative_1208_, 3);
v_toSeqRight_1212_ = lean_ctor_get(v_toApplicative_1208_, 4);
v___f_1213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2));
v___f_1214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1209_, 2);
v___f_1215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1215_, 0, v_toFunctor_1209_);
v___f_1216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1216_, 0, v_toFunctor_1209_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___f_1215_);
lean_ctor_set(v___x_1217_, 1, v___f_1216_);
lean_inc(v_toSeqRight_1212_);
v___f_1218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1218_, 0, v_toSeqRight_1212_);
lean_inc(v_toSeqLeft_1211_);
v___f_1219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1219_, 0, v_toSeqLeft_1211_);
lean_inc(v_toSeq_1210_);
v___f_1220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1220_, 0, v_toSeq_1210_);
v___x_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1217_);
lean_ctor_set(v___x_1221_, 1, v___f_1213_);
lean_ctor_set(v___x_1221_, 2, v___f_1220_);
lean_ctor_set(v___x_1221_, 3, v___f_1219_);
lean_ctor_set(v___x_1221_, 4, v___f_1218_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___f_1214_);
v___x_1223_ = l_StateRefT_x27_instMonad___redArg(v___x_1222_);
v_toApplicative_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1223_, 1);
lean_dec(v_unused_1278_);
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1277_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_toApplicative_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1277_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_toFunctor_1228_; lean_object* v_toSeq_1229_; lean_object* v_toSeqLeft_1230_; lean_object* v_toSeqRight_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1275_; 
v_toFunctor_1228_ = lean_ctor_get(v_toApplicative_1224_, 0);
v_toSeq_1229_ = lean_ctor_get(v_toApplicative_1224_, 2);
v_toSeqLeft_1230_ = lean_ctor_get(v_toApplicative_1224_, 3);
v_toSeqRight_1231_ = lean_ctor_get(v_toApplicative_1224_, 4);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_toApplicative_1224_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v_toApplicative_1224_, 1);
lean_dec(v_unused_1276_);
v___x_1233_ = v_toApplicative_1224_;
v_isShared_1234_ = v_isSharedCheck_1275_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_toSeqRight_1231_);
lean_inc(v_toSeqLeft_1230_);
lean_inc(v_toSeq_1229_);
lean_inc(v_toFunctor_1228_);
lean_dec(v_toApplicative_1224_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1275_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___x_1244_; 
v___f_1235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4));
v___f_1236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5));
lean_inc_ref(v_toFunctor_1228_);
v___f_1237_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1237_, 0, v_toFunctor_1228_);
v___f_1238_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1238_, 0, v_toFunctor_1228_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___f_1237_);
lean_ctor_set(v___x_1239_, 1, v___f_1238_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toSeqRight_1231_);
v___f_1241_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1241_, 0, v_toSeqLeft_1230_);
v___f_1242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1242_, 0, v_toSeq_1229_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 4, v___f_1240_);
lean_ctor_set(v___x_1233_, 3, v___f_1241_);
lean_ctor_set(v___x_1233_, 2, v___f_1242_);
lean_ctor_set(v___x_1233_, 1, v___f_1235_);
lean_ctor_set(v___x_1233_, 0, v___x_1239_);
v___x_1244_ = v___x_1233_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___f_1235_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___f_1242_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___f_1241_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v___f_1240_);
v___x_1244_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___f_1236_);
lean_ctor_set(v___x_1226_, 0, v___x_1244_);
v___x_1246_ = v___x_1226_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___f_1236_);
v___x_1246_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_toMonadRef_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_toBind_1265_; lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1247_ = l_StateRefT_x27_instMonad___redArg(v___x_1246_);
v___x_1248_ = l_ReaderT_instMonad___redArg(v___x_1247_);
v___x_1249_ = l_StateRefT_x27_instMonad___redArg(v___x_1248_);
v___x_1250_ = l_ReaderT_instMonad___redArg(v___x_1249_);
v___x_1251_ = l_ReaderT_instMonad___redArg(v___x_1250_);
v___x_1252_ = l_StateRefT_x27_instMonad___redArg(v___x_1251_);
lean_inc_ref(v___x_1252_);
v___x_1253_ = l_ReaderT_instMonad___redArg(v___x_1252_);
v___x_1254_ = l_StateRefT_x27_instMonad___redArg(v___x_1253_);
v___x_1255_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__31, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__31);
v___x_1256_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__43, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__43_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__43);
v_toMonadRef_1257_ = lean_ctor_get(v___x_1256_, 0);
v___f_1258_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__51, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__51_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__51);
lean_inc_ref_n(v___x_1254_, 2);
v___x_1259_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1258_, v___x_1254_);
lean_inc_ref(v_toMonadRef_1257_);
v___x_1260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1255_);
lean_ctor_set(v___x_1260_, 1, v_toMonadRef_1257_);
lean_ctor_set(v___x_1260_, 2, v___x_1259_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__0___boxed), 16, 2);
lean_closure_set(v___f_1261_, 0, v___x_1254_);
lean_closure_set(v___f_1261_, 1, v___x_1260_);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = lean_array_get_size(v_hyps_1205_);
v___x_1264_ = l_Array_filterMapM___redArg(v___x_1254_, v___f_1261_, v_hyps_1205_, v___x_1262_, v___x_1263_);
v_toBind_1265_ = lean_ctor_get(v_inst_1201_, 1);
lean_inc(v_toBind_1265_);
v___f_1266_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__54));
lean_inc(v_a_1206_);
lean_inc(v_inst_1204_);
lean_inc_ref(v_inst_1201_);
v___f_1267_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_1267_, 0, v_inst_1201_);
lean_closure_set(v___f_1267_, 1, v_inst_1202_);
lean_closure_set(v___f_1267_, 2, v_inst_1204_);
lean_closure_set(v___f_1267_, 3, v_a_1206_);
v___x_1268_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__55, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__55_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___closed__55);
v___x_1269_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed), 15, 3);
lean_closure_set(v___x_1269_, 0, lean_box(0));
lean_closure_set(v___x_1269_, 1, v___x_1264_);
lean_closure_set(v___x_1269_, 2, v___x_1268_);
v___x_1270_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1270_, 0, lean_box(0));
lean_closure_set(v___x_1270_, 1, lean_box(0));
lean_closure_set(v___x_1270_, 2, v___x_1252_);
lean_closure_set(v___x_1270_, 3, lean_box(0));
lean_closure_set(v___x_1270_, 4, lean_box(0));
lean_closure_set(v___x_1270_, 5, v___x_1269_);
lean_closure_set(v___x_1270_, 6, v___f_1266_);
v___x_1271_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_1201_, v_inst_1203_, v_inst_1204_, v___x_1270_, v_a_1206_);
v___x_1272_ = lean_apply_4(v_toBind_1265_, lean_box(0), lean_box(0), v___x_1271_, v___f_1267_);
return v___x_1272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg___boxed(lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_hyps_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(v_inst_1279_, v_inst_1280_, v_inst_1281_, v_inst_1282_, v_hyps_1283_, v_a_1284_);
lean_dec(v_a_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized(lean_object* v_00_u03c3_1286_, lean_object* v_m_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_hyps_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(v_inst_1289_, v_inst_1290_, v_inst_1291_, v_inst_1292_, v_hyps_1293_, v_a_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___boxed(lean_object* v_00_u03c3_1296_, lean_object* v_m_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_hyps_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized(v_00_u03c3_1296_, v_m_1297_, v_inst_1298_, v_inst_1299_, v_inst_1300_, v_inst_1301_, v_inst_1302_, v_hyps_1303_, v_a_1304_);
lean_dec(v_a_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0(uint8_t v_____do__lift_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
if (v_____do__lift_1306_ == 0)
{
lean_object* v___x_1319_; lean_object* v_hypotheses_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = lean_st_ref_get(v___y_1308_);
v_hypotheses_1320_ = lean_ctor_get(v___x_1319_, 3);
lean_inc_ref(v_hypotheses_1320_);
lean_dec(v___x_1319_);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_hypotheses_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0___boxed(lean_object* v_____do__lift_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v_____do__lift_1248__boxed_1338_; lean_object* v_res_1339_; 
v_____do__lift_1248__boxed_1338_ = lean_unbox(v_____do__lift_1325_);
v_res_1339_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__0(v_____do__lift_1248__boxed_1338_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1339_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0(void){
_start:
{
uint8_t v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = 0;
v___x_1341_ = l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(v___x_1340_);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__0);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_mk_empty_array_with_capacity(v___x_1343_);
v___x_1345_ = lean_array_push(v___x_1344_, v___x_1342_);
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__1);
v___x_1347_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_BvSolverM_push___boxed), 10, 1);
lean_closure_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1(lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_a_1351_, lean_object* v_inst_1352_, lean_object* v_a_1353_){
_start:
{
if (lean_obj_tag(v_a_1353_) == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_inst_1352_);
v___x_1354_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___closed__2);
v___x_1355_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_1348_, v_inst_1349_, v_inst_1350_, v___x_1354_, v_a_1351_);
return v___x_1355_;
}
else
{
lean_object* v_val_1356_; lean_object* v___x_1357_; 
v_val_1356_ = lean_ctor_get(v_a_1353_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v_a_1353_, 1);
v___x_1357_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pushNormalized___redArg(v_inst_1348_, v_inst_1349_, v_inst_1352_, v_inst_1350_, v_val_1356_, v_a_1351_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___boxed(lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_a_1361_, lean_object* v_inst_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1(v_inst_1358_, v_inst_1359_, v_inst_1360_, v_a_1361_, v_inst_1362_, v_a_1363_);
lean_dec(v_a_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg(lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_hyps_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v_toApplicative_1373_; lean_object* v_toFunctor_1374_; lean_object* v_toSeq_1375_; lean_object* v_toSeqLeft_1376_; lean_object* v_toSeqRight_1377_; lean_object* v___f_1378_; lean_object* v___f_1379_; lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___f_1384_; lean_object* v___f_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_toApplicative_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1430_; 
v___x_1372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__1);
v_toApplicative_1373_ = lean_ctor_get(v___x_1372_, 0);
v_toFunctor_1374_ = lean_ctor_get(v_toApplicative_1373_, 0);
v_toSeq_1375_ = lean_ctor_get(v_toApplicative_1373_, 2);
v_toSeqLeft_1376_ = lean_ctor_get(v_toApplicative_1373_, 3);
v_toSeqRight_1377_ = lean_ctor_get(v_toApplicative_1373_, 4);
v___f_1378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__2));
v___f_1379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1374_, 2);
v___f_1380_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1380_, 0, v_toFunctor_1374_);
v___f_1381_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1381_, 0, v_toFunctor_1374_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___f_1380_);
lean_ctor_set(v___x_1382_, 1, v___f_1381_);
lean_inc(v_toSeqRight_1377_);
v___f_1383_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1383_, 0, v_toSeqRight_1377_);
lean_inc(v_toSeqLeft_1376_);
v___f_1384_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1384_, 0, v_toSeqLeft_1376_);
lean_inc(v_toSeq_1375_);
v___f_1385_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1385_, 0, v_toSeq_1375_);
v___x_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1382_);
lean_ctor_set(v___x_1386_, 1, v___f_1378_);
lean_ctor_set(v___x_1386_, 2, v___f_1385_);
lean_ctor_set(v___x_1386_, 3, v___f_1384_);
lean_ctor_set(v___x_1386_, 4, v___f_1383_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v___f_1379_);
v___x_1388_ = l_StateRefT_x27_instMonad___redArg(v___x_1387_);
v_toApplicative_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v___x_1388_, 1);
lean_dec(v_unused_1431_);
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1430_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_toApplicative_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1430_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_toFunctor_1393_; lean_object* v_toSeq_1394_; lean_object* v_toSeqLeft_1395_; lean_object* v_toSeqRight_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1428_; 
v_toFunctor_1393_ = lean_ctor_get(v_toApplicative_1389_, 0);
v_toSeq_1394_ = lean_ctor_get(v_toApplicative_1389_, 2);
v_toSeqLeft_1395_ = lean_ctor_get(v_toApplicative_1389_, 3);
v_toSeqRight_1396_ = lean_ctor_get(v_toApplicative_1389_, 4);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_toApplicative_1389_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_toApplicative_1389_, 1);
lean_dec(v_unused_1429_);
v___x_1398_ = v_toApplicative_1389_;
v_isShared_1399_ = v_isSharedCheck_1428_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_toSeqRight_1396_);
lean_inc(v_toSeqLeft_1395_);
lean_inc(v_toSeq_1394_);
lean_inc(v_toFunctor_1393_);
lean_dec(v_toApplicative_1389_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1428_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___f_1400_; lean_object* v___f_1401_; lean_object* v___f_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v___f_1406_; lean_object* v___f_1407_; lean_object* v___x_1409_; 
v___f_1400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__4));
v___f_1401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg___closed__5));
lean_inc_ref(v_toFunctor_1393_);
v___f_1402_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1402_, 0, v_toFunctor_1393_);
v___f_1403_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1403_, 0, v_toFunctor_1393_);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___f_1402_);
lean_ctor_set(v___x_1404_, 1, v___f_1403_);
v___f_1405_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1405_, 0, v_toSeqRight_1396_);
v___f_1406_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1406_, 0, v_toSeqLeft_1395_);
v___f_1407_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1407_, 0, v_toSeq_1394_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 4, v___f_1405_);
lean_ctor_set(v___x_1398_, 3, v___f_1406_);
lean_ctor_set(v___x_1398_, 2, v___f_1407_);
lean_ctor_set(v___x_1398_, 1, v___f_1400_);
lean_ctor_set(v___x_1398_, 0, v___x_1404_);
v___x_1409_ = v___x_1398_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___f_1400_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v___f_1407_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v___f_1406_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v___f_1405_);
v___x_1409_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v___f_1401_);
lean_ctor_set(v___x_1391_, 0, v___x_1409_);
v___x_1411_ = v___x_1391_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___f_1401_);
v___x_1411_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_toBind_1418_; lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1412_ = l_StateRefT_x27_instMonad___redArg(v___x_1411_);
v___x_1413_ = l_ReaderT_instMonad___redArg(v___x_1412_);
v___x_1414_ = l_StateRefT_x27_instMonad___redArg(v___x_1413_);
v___x_1415_ = l_ReaderT_instMonad___redArg(v___x_1414_);
v___x_1416_ = l_ReaderT_instMonad___redArg(v___x_1415_);
v___x_1417_ = l_StateRefT_x27_instMonad___redArg(v___x_1416_);
v_toBind_1418_ = lean_ctor_get(v_inst_1366_, 1);
lean_inc(v_toBind_1418_);
v___f_1419_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___closed__0));
lean_inc(v_inst_1368_);
lean_inc(v_a_1371_);
lean_inc(v_inst_1369_);
lean_inc_ref(v_inst_1366_);
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1420_, 0, v_inst_1366_);
lean_closure_set(v___f_1420_, 1, v_inst_1367_);
lean_closure_set(v___f_1420_, 2, v_inst_1369_);
lean_closure_set(v___f_1420_, 3, v_a_1371_);
lean_closure_set(v___f_1420_, 4, v_inst_1368_);
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_hyps_1370_);
v___x_1422_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed), 13, 1);
lean_closure_set(v___x_1422_, 0, v___x_1421_);
v___x_1423_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1423_, 0, lean_box(0));
lean_closure_set(v___x_1423_, 1, lean_box(0));
lean_closure_set(v___x_1423_, 2, v___x_1417_);
lean_closure_set(v___x_1423_, 3, lean_box(0));
lean_closure_set(v___x_1423_, 4, lean_box(0));
lean_closure_set(v___x_1423_, 5, v___x_1422_);
lean_closure_set(v___x_1423_, 6, v___f_1419_);
v___x_1424_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftPreProcessM___redArg(v_inst_1366_, v_inst_1368_, v_inst_1369_, v___x_1423_, v_a_1371_);
v___x_1425_ = lean_apply_4(v_toBind_1418_, lean_box(0), lean_box(0), v___x_1424_, v___f_1420_);
return v___x_1425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg___boxed(lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_hyps_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg(v_inst_1432_, v_inst_1433_, v_inst_1434_, v_inst_1435_, v_hyps_1436_, v_a_1437_);
lean_dec(v_a_1437_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push(lean_object* v_00_u03c3_1439_, lean_object* v_m_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_hyps_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___redArg(v_inst_1442_, v_inst_1443_, v_inst_1444_, v_inst_1445_, v_hyps_1446_, v_a_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push___boxed(lean_object* v_00_u03c3_1449_, lean_object* v_m_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_hyps_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_push(v_00_u03c3_1449_, v_m_1450_, v_inst_1451_, v_inst_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_hyps_1456_, v_a_1457_);
lean_dec(v_a_1457_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg(lean_object* v_inst_1460_, lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg___closed__0));
v___x_1465_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_1460_, v_inst_1461_, v_inst_1462_, v___x_1464_, v_a_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg___boxed(lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg(v_inst_1466_, v_inst_1467_, v_inst_1468_, v_a_1469_);
lean_dec(v_a_1469_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop(lean_object* v_00_u03c3_1471_, lean_object* v_m_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_inst_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___redArg(v_inst_1474_, v_inst_1475_, v_inst_1476_, v_a_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop___boxed(lean_object* v_00_u03c3_1479_, lean_object* v_m_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_pop(v_00_u03c3_1479_, v_m_1480_, v_inst_1481_, v_inst_1482_, v_inst_1483_, v_inst_1484_, v_a_1485_);
lean_dec(v_a_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__0(lean_object* v_toApplicative_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_toPure_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_toPure_1489_ = lean_ctor_get(v_toApplicative_1487_, 1);
lean_inc(v_toPure_1489_);
lean_dec_ref(v_toApplicative_1487_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1488_);
v___x_1491_ = lean_apply_2(v_toPure_1489_, lean_box(0), v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1(lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_inst_1496_, lean_object* v_a_1497_, lean_object* v_toBind_1498_, lean_object* v___f_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_bvSolver_1501_; lean_object* v_bitvecState_1502_; lean_object* v_aig_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_bvSolver_1501_ = lean_ctor_get(v_a_1500_, 2);
lean_inc_ref(v_bvSolver_1501_);
lean_dec_ref(v_a_1500_);
v_bitvecState_1502_ = lean_ctor_get(v_bvSolver_1501_, 0);
lean_inc_ref(v_bitvecState_1502_);
lean_dec_ref(v_bvSolver_1501_);
v_aig_1503_ = lean_ctor_get(v_bitvecState_1502_, 0);
lean_inc_ref(v_aig_1503_);
lean_dec_ref(v_bitvecState_1502_);
v___x_1504_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_1503_, v_a_1492_, v_a_1493_);
v___x_1505_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray___boxed), 13, 1);
lean_closure_set(v___x_1505_, 0, v___x_1504_);
v___x_1506_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_1494_, v_inst_1495_, v_inst_1496_, v___x_1505_, v_a_1497_);
v___x_1507_ = lean_apply_4(v_toBind_1498_, lean_box(0), lean_box(0), v___x_1506_, v___f_1499_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1___boxed(lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_a_1513_, lean_object* v_toBind_1514_, lean_object* v___f_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1(v_a_1508_, v_a_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_a_1513_, v_toBind_1514_, v___f_1515_, v_a_1516_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2(lean_object* v_a_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_a_1522_, lean_object* v_toBind_1523_, lean_object* v___f_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___f_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_inc(v_toBind_1523_);
lean_inc_n(v_a_1522_, 2);
lean_inc(v_inst_1521_);
v___f_1526_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_1526_, 0, v_a_1518_);
lean_closure_set(v___f_1526_, 1, v_a_1525_);
lean_closure_set(v___f_1526_, 2, v_inst_1519_);
lean_closure_set(v___f_1526_, 3, v_inst_1520_);
lean_closure_set(v___f_1526_, 4, v_inst_1521_);
lean_closure_set(v___f_1526_, 5, v_a_1522_);
lean_closure_set(v___f_1526_, 6, v_toBind_1523_);
lean_closure_set(v___f_1526_, 7, v___f_1524_);
v___x_1527_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1527_, 0, lean_box(0));
lean_closure_set(v___x_1527_, 1, lean_box(0));
lean_closure_set(v___x_1527_, 2, v_a_1522_);
v___x_1528_ = lean_apply_2(v_inst_1521_, lean_box(0), v___x_1527_);
v___x_1529_ = lean_apply_4(v_toBind_1523_, lean_box(0), lean_box(0), v___x_1528_, v___f_1526_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2___boxed(lean_object* v_a_1530_, lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_inst_1533_, lean_object* v_a_1534_, lean_object* v_toBind_1535_, lean_object* v___f_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2(v_a_1530_, v_inst_1531_, v_inst_1532_, v_inst_1533_, v_a_1534_, v_toBind_1535_, v___f_1536_, v_a_1537_);
lean_dec(v_a_1534_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3(lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_a_1545_, lean_object* v_toBind_1546_, lean_object* v___f_1547_, lean_object* v_toApplicative_1548_, lean_object* v_a_1549_){
_start:
{
if (lean_obj_tag(v_a_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec_ref(v_toApplicative_1548_);
v_a_1550_ = lean_ctor_get(v_a_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v_a_1549_, 1);
lean_inc(v_toBind_1546_);
lean_inc(v_a_1545_);
lean_inc(v_inst_1544_);
lean_inc(v_inst_1543_);
lean_inc_ref(v_inst_1542_);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1551_, 0, v_a_1550_);
lean_closure_set(v___f_1551_, 1, v_inst_1542_);
lean_closure_set(v___f_1551_, 2, v_inst_1543_);
lean_closure_set(v___f_1551_, 3, v_inst_1544_);
lean_closure_set(v___f_1551_, 4, v_a_1545_);
lean_closure_set(v___f_1551_, 5, v_toBind_1546_);
lean_closure_set(v___f_1551_, 6, v___f_1547_);
v___x_1552_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__0));
v___x_1553_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftReifyM___redArg(v_inst_1542_, v_inst_1543_, v_inst_1544_, v___x_1552_, v_a_1545_);
v___x_1554_ = lean_apply_4(v_toBind_1546_, lean_box(0), lean_box(0), v___x_1553_, v___f_1551_);
return v___x_1554_;
}
else
{
lean_object* v_toPure_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref_known(v_a_1549_, 1);
lean_dec(v___f_1547_);
lean_dec(v_toBind_1546_);
lean_dec(v_inst_1544_);
lean_dec(v_inst_1543_);
lean_dec_ref(v_inst_1542_);
v_toPure_1555_ = lean_ctor_get(v_toApplicative_1548_, 1);
lean_inc(v_toPure_1555_);
lean_dec_ref(v_toApplicative_1548_);
v___x_1556_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___closed__1));
v___x_1557_ = lean_apply_2(v_toPure_1555_, lean_box(0), v___x_1556_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___boxed(lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_a_1561_, lean_object* v_toBind_1562_, lean_object* v___f_1563_, lean_object* v_toApplicative_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3(v_inst_1558_, v_inst_1559_, v_inst_1560_, v_a_1561_, v_toBind_1562_, v___f_1563_, v_toApplicative_1564_, v_a_1565_);
lean_dec(v_a_1561_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg(lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_toApplicative_1573_; lean_object* v_toBind_1574_; lean_object* v___f_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_toApplicative_1573_ = lean_ctor_get(v_inst_1568_, 0);
v_toBind_1574_ = lean_ctor_get(v_inst_1568_, 1);
lean_inc_n(v_toBind_1574_, 2);
lean_inc_ref_n(v_toApplicative_1573_, 2);
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1575_, 0, v_toApplicative_1573_);
lean_inc(v_a_1572_);
lean_inc(v_inst_1571_);
lean_inc_ref(v_inst_1568_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1576_, 0, v_inst_1568_);
lean_closure_set(v___f_1576_, 1, v_inst_1570_);
lean_closure_set(v___f_1576_, 2, v_inst_1571_);
lean_closure_set(v___f_1576_, 3, v_a_1572_);
lean_closure_set(v___f_1576_, 4, v_toBind_1574_);
lean_closure_set(v___f_1576_, 5, v___f_1575_);
lean_closure_set(v___f_1576_, 6, v_toApplicative_1573_);
v___x_1577_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___closed__0));
v___x_1578_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver_0__Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_liftBvSolverM___redArg(v_inst_1568_, v_inst_1569_, v_inst_1571_, v___x_1577_, v_a_1572_);
v___x_1579_ = lean_apply_4(v_toBind_1574_, lean_box(0), lean_box(0), v___x_1578_, v___f_1576_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg___boxed(lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg(v_inst_1580_, v_inst_1581_, v_inst_1582_, v_inst_1583_, v_a_1584_);
lean_dec(v_a_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check(lean_object* v_00_u03c3_1586_, lean_object* v_m_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___redArg(v_inst_1589_, v_inst_1590_, v_inst_1591_, v_inst_1592_, v_a_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check___boxed(lean_object* v_00_u03c3_1595_, lean_object* v_m_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_check(v_00_u03c3_1595_, v_m_1596_, v_inst_1597_, v_inst_1598_, v_inst_1599_, v_inst_1600_, v_inst_1601_, v_a_1602_);
lean_dec(v_a_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__0(lean_object* v_a_1604_, lean_object* v_toPure_1605_, lean_object* v_s_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_a_1604_);
lean_ctor_set(v___x_1607_, 1, v_s_1606_);
v___x_1608_ = lean_apply_2(v_toPure_1605_, lean_box(0), v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__1(lean_object* v_toPure_1609_, lean_object* v_ref_1610_, lean_object* v_inst_1611_, lean_object* v_toBind_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1614_, 0, v_a_1613_);
lean_closure_set(v___f_1614_, 1, v_toPure_1609_);
v___x_1615_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1615_, 0, lean_box(0));
lean_closure_set(v___x_1615_, 1, lean_box(0));
lean_closure_set(v___x_1615_, 2, v_ref_1610_);
v___x_1616_ = lean_apply_2(v_inst_1611_, lean_box(0), v___x_1615_);
v___x_1617_ = lean_apply_4(v_toBind_1612_, lean_box(0), lean_box(0), v___x_1616_, v___f_1614_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__2(lean_object* v_toPure_1618_, lean_object* v_inst_1619_, lean_object* v_toBind_1620_, lean_object* v_x_1621_, lean_object* v_ref_1622_){
_start:
{
lean_object* v___f_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_inc(v_toBind_1620_);
lean_inc(v_ref_1622_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1623_, 0, v_toPure_1618_);
lean_closure_set(v___f_1623_, 1, v_ref_1622_);
lean_closure_set(v___f_1623_, 2, v_inst_1619_);
lean_closure_set(v___f_1623_, 3, v_toBind_1620_);
v___x_1624_ = lean_apply_1(v_x_1621_, v_ref_1622_);
v___x_1625_ = lean_apply_4(v_toBind_1620_, lean_box(0), lean_box(0), v___x_1624_, v___f_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__3(lean_object* v_toPure_1626_, lean_object* v_____x_1627_){
_start:
{
lean_object* v_fst_1628_; lean_object* v___x_1629_; 
v_fst_1628_ = lean_ctor_get(v_____x_1627_, 0);
lean_inc(v_fst_1628_);
lean_dec_ref(v_____x_1627_);
v___x_1629_ = lean_apply_2(v_toPure_1626_, lean_box(0), v_fst_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__4(lean_object* v_toApplicative_1630_, lean_object* v_inst_1631_, lean_object* v_toBind_1632_, lean_object* v_x_1633_, lean_object* v_solver_1634_){
_start:
{
lean_object* v_toPure_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_toPure_1635_ = lean_ctor_get(v_toApplicative_1630_, 1);
lean_inc_n(v_toPure_1635_, 2);
lean_dec_ref(v_toApplicative_1630_);
v___x_1636_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1636_, 0, lean_box(0));
lean_closure_set(v___x_1636_, 1, lean_box(0));
lean_closure_set(v___x_1636_, 2, v_solver_1634_);
lean_inc(v_inst_1631_);
v___x_1637_ = lean_apply_2(v_inst_1631_, lean_box(0), v___x_1636_);
lean_inc_n(v_toBind_1632_, 2);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1638_, 0, v_toPure_1635_);
lean_closure_set(v___f_1638_, 1, v_inst_1631_);
lean_closure_set(v___f_1638_, 2, v_toBind_1632_);
lean_closure_set(v___f_1638_, 3, v_x_1633_);
v___f_1639_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_1639_, 0, v_toPure_1635_);
v___x_1640_ = lean_apply_4(v_toBind_1632_, lean_box(0), lean_box(0), v___x_1637_, v___f_1638_);
v___x_1641_ = lean_apply_4(v_toBind_1632_, lean_box(0), lean_box(0), v___x_1640_, v___f_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg(lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_ctx_1645_, lean_object* v_mvar_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v_toApplicative_1648_; lean_object* v_toBind_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_toApplicative_1648_ = lean_ctor_get(v_inst_1642_, 0);
lean_inc_ref(v_toApplicative_1648_);
v_toBind_1649_ = lean_ctor_get(v_inst_1642_, 1);
lean_inc_n(v_toBind_1649_, 2);
lean_dec_ref(v_inst_1642_);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1650_, 0, v_toApplicative_1648_);
lean_closure_set(v___f_1650_, 1, v_inst_1644_);
lean_closure_set(v___f_1650_, 2, v_toBind_1649_);
lean_closure_set(v___f_1650_, 3, v_x_1647_);
v___x_1651_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_Subsolver_new___boxed), 9, 2);
lean_closure_set(v___x_1651_, 0, v_ctx_1645_);
lean_closure_set(v___x_1651_, 1, v_mvar_1646_);
v___x_1652_ = lean_apply_2(v_inst_1643_, lean_box(0), v___x_1651_);
v___x_1653_ = lean_apply_4(v_toBind_1649_, lean_box(0), lean_box(0), v___x_1652_, v___f_1650_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run(lean_object* v_00_u03c3_1654_, lean_object* v_m_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_00_u03b1_1660_, lean_object* v_ctx_1661_, lean_object* v_mvar_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Meta_Tactic_BVDecide_Cegar_SubsolverT_run___redArg(v_inst_1657_, v_inst_1658_, v_inst_1659_, v_ctx_1661_, v_mvar_1662_, v_x_1663_);
return v___x_1664_;
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
